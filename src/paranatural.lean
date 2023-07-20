import difunctor category_theory.types

open category_theory
open difunctor


universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

@[ext]
structure diagonal_fam (Δ Γ : C ±⥤ D) : Type (max u₁ v₂) :=
(app : Π I : C, Δ.obj I I ⟶ Γ.obj I I)

def is_paranatural {Δ Γ : C ±⥤ D} (α : diagonal_fam Δ Γ) : Prop := ∀ {I₀ I₁ : C} {W : D} (w₀ : W ⟶ Δ.obj I₀ I₀) (w₁ : W ⟶ Δ.obj I₁ I₁) (i₂ : I₀ ⟶ I₁), 
w₀ ≫ Δ.map_pos _ i₂ = w₁ ≫ Δ.map_neg _ i₂   → 
w₀ ≫ α.app I₀ ≫ Γ.map_pos _ i₂ = w₁ ≫ α.app I₁ ≫ Γ.map_neg _ i₂

structure paranat (Δ Γ : C ±⥤ D) extends diagonal_fam Δ Γ : Type (max u₁ v₂) :=
(paranaturality : is_paranatural to_diagonal_fam)

-- attribute [simp, reassoc] paranat.paranaturality

namespace paranat

protected def id (Γ : C ±⥤ D) : paranat Γ Γ :=
{ app := λ I, 𝟙 (Γ.obj I I),
  paranaturality :=
    begin
      assume I₀ I₁ W w₀ w₁ i₂ h,
      simp,
      exact h,
    end
}

section
variables {Δ Γ Ω : C ±⥤ D}

def comp (γ : paranat Δ Γ) (ω : paranat Γ Ω) : paranat Δ Ω :=
{ app := λ I, (γ.app I) ≫ (ω.app I),
  paranaturality := 
    begin
      assume I₀ I₁ W w₀ w₁ i₂ h,
      have firstChev : (w₀ ≫ γ.app I₀) ≫ Γ.map_pos I₀ i₂ = (w₁ ≫ γ.app I₁) ≫ Γ.map_neg _ i₂,
        rw category.assoc,
        rw category.assoc,
        apply γ.paranaturality,
        exact h,
      calc
      w₀ ≫ (γ.app I₀ ≫ ω.app I₀) ≫ Ω.map_pos I₀ i₂ 
          = (w₀ ≫ γ.app I₀) ≫ ω.app I₀ ≫ Ω.map_pos I₀ i₂ : by simp
      ... = (w₁ ≫ γ.app I₁) ≫ ω.app I₁ ≫ Ω.map_neg I₁ i₂ : by apply ω.paranaturality;exact firstChev
      ... = w₁ ≫ (γ.app I₁ ≫ ω.app I₁) ≫ Ω.map_neg I₁ i₂ : by simp,
    end
}

end

namespace setvalued

variables {Δ Γ : C ±⥤ Type v₃}

def is_paranatural' (α : diagonal_fam Δ Γ) : Prop :=
∀ {I₀ I₁ : C} (d₀ : Δ.obj I₀ I₀) (d₁ : Δ.obj I₁ I₁) (i₂ : I₀ ⟶ I₁), Δ.map_pos _ i₂ d₀ = Δ.map_neg _ i₂ d₁ → Γ.map_pos _ i₂ (α.app _ d₀) = Γ.map_neg _ i₂ (α.app _ d₁)

lemma structwise_paranat : ∀ α : diagonal_fam Δ Γ, is_paranatural α ↔ is_paranatural' α :=
begin
  assume α,
  split,
  assume paranaturality I₀ I₁ d₀ d₁ i₂ h,
  have lem: Γ.map_pos I₀ i₂ ∘ α.app I₀ ∘ (λ _, d₀) = Γ.map_neg I₁ i₂ ∘ α.app I₁ ∘ (λ _, d₁),
    apply paranaturality,
    funext,
    exact h,

  calc
  Γ.map_pos I₀ i₂ (α.app I₀ d₀) 
      = (Γ.map_pos I₀ i₂ ∘ α.app I₀ ∘ λ _, d₀) punit.star : by refl
  ... = (Γ.map_neg I₁ i₂ ∘ α.app I₁ ∘ λ _, d₁) () : by rw lem
  ... = Γ.map_neg I₁ i₂ (α.app I₁ d₁) : by refl,

  assume paranaturality' I₀ I₁ W w₀ w₁ i₂ h,
  funext w, dsimp[(≫)],
  let d₀ : Δ.obj I₀ I₀ := w₀ w,
  let d₁ : Δ.obj I₁ I₁ := w₁ w,
  apply paranaturality',
  change (Δ.map_pos I₀ i₂ ∘ w₀) w = (Δ.map_neg I₁ i₂ ∘ w₁) w,
  exact congr_fun h w,


end

/-
# TODO: Pullback defn
-/


namespace structures


def difunctor.diag_elements (Γ : C ±⥤ Type v₃) := (Σ I : C, Γ.obj I I)

def is_hom {I₀ I₁ : C} (g₀ : Γ.obj I₀ I₀) (g₁ : Γ.obj I₁ I₁) (i₂ : I₀ ⟶ I₁) : Prop := Γ.map_pos _ i₂ g₀ = Γ.map_neg _ i₂ g₁

def is_hom_id {I : C} {g : Γ.obj I I} : is_hom g g (𝟙 I) := 
  by dsimp[is_hom]; rw Γ.map_pos_id; rw Γ.map_neg_id

lemma is_hom_comp {I I' I'' : C} {g: Γ.obj I I} {g': Γ.obj I' I'} {g'': Γ.obj I'' I''} {i : I ⟶ I'} {i' : I' ⟶ I''} (h : is_hom g g' i) (h' : is_hom g' g'' i') : is_hom g g'' (i ≫ i') :=
begin
  dsimp[is_hom] at h, dsimp[is_hom] at h',
  calc
  Γ.map_pos _ (i ≫ i') g
      = (Γ.map_pos _ i ≫ Γ.map_pos _ i') g : by rw map_pos_comp
  ... = Γ.map_pos _ i' (Γ.map_pos _ i g) : by refl
  ... = Γ.map_pos _ i' (Γ.map_neg _ i g') : by rw h
  ... = Γ.map_neg _ i (Γ.map_pos _ i' g') : congr_fun (Γ.map_both i i') g' 
  ... = Γ.map_neg _ i (Γ.map_neg _ i' g'') : by rw h'
  ... = (Γ.map_neg _ i' ≫ Γ.map_neg _ i) g'' : by refl
  ... = Γ.map_neg _ (i ≫ i') g'' : by rw map_neg_comp,
end

instance Struct (Γ : C ±⥤ Type v₃) : category Γ.diag_elements :=
{
  hom := λ G₀ G₁, { i₂ : G₀.1 ⟶ G₁.1 // is_hom G₀.2 G₁.2 i₂ },
  id := λ G, ⟨ 𝟙 G.1, is_hom_id ⟩ ,
  comp := λ G G' G'' h h', ⟨ h.val ≫ h'.val, is_hom_comp h.property h'.property ⟩ 
}

/-
# TODO: Functor corresponding to a paranatural transform
-/

end structures
 

end setvalued

end paranat