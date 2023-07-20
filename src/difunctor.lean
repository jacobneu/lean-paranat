import combinatorics.quiver.basic 
import category_theory.category.basic category_theory.functor.basic
-- import category_theory.products.basic
import category_theory.opposites
-- import category_theory.functor.fully_faithful
-- import category_theory.functor.currying
-- import category_theory.products.basic

open category_theory
open opposite


universes v v₁ v₂ u u₁ u₂

structure predifunctor (V : Type u₁) [quiver.{v₁} V] (W : Type u₂) [quiver.{v₂} W] :=
(obj [] : V → V → W)
(map_neg : Π {I₀ I₁ : V} (J : V), (I₀ ⟶ I₁) → (obj I₁ J ⟶ obj I₀ J))
(map_pos : Π (I : V) {J₀ J₁ : V}, (J₀ ⟶ J₁) → (obj I J₀ ⟶ obj I J₁))


namespace predifunctor

@[ext]
lemma ext {V : Type u} [quiver.{v₁} V] {W : Type u₂} [quiver.{v₂} W]
  {F G : predifunctor V W}
  (h_obj : ∀ I J, F.obj I J = G.obj I J)
  (h_map_neg : ∀ (I₀ I₁ J : V) (i₂ : I₀ ⟶ I₁),
           F.map_neg J i₂ = eq.rec_on (h_obj I₀ J).symm (eq.rec_on (h_obj I₁ J).symm (G.map_neg J i₂)))
  (h_map_pos : ∀ (I J₀ J₁ : V) (j₂ : J₀ ⟶ J₁),
           F.map_pos I j₂ = eq.rec_on (h_obj I J₁).symm (eq.rec_on (h_obj I J₀).symm (G.map_pos I j₂))) : F = G :=
begin
  cases F with F_obj _, cases G with G_obj _,
  obtain rfl : F_obj = G_obj, by { ext X, apply h_obj },
  congr,
  funext I₀ I₁ J i₂,
  simpa using h_map_neg I₀ I₁ J i₂,
  funext I J₀ J₁ j₂,
  simpa using h_map_pos I J₀ J₁ j₂,
end


-- @[simps]
-- def id (V : Type*) [quiver V] : prefunctor V V :=
-- { obj := id,
--   map := λ X Y f, f, }

-- instance (V : Type*) [quiver V] : inhabited (prefunctor V V) := ⟨id V⟩

-- def from_prefunctor_pos {V : Type u₁} [quiver.{v₁} V] {W : Type u₂} [quiver.{v₂} W] (F : prefunctor V W) : predifunctor V W :=
-- { 
--   obj := λ I J, F.obj J, 
--   map_pos := λ I J₀ J₁ j₂, F.map j₂,
--   map_neg := λ I₀ I₁ J i₂, id
-- }

end predifunctor



structure difunctor (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D]
  extends predifunctor C D : Type (max v₁ v₂ u₁ u₂) :=
(map_pos_id'   : ∀ (I J : C), map_pos I (𝟙 J) = 𝟙 (obj I J) . obviously)
(map_pos_comp' : ∀ {I J K L : C} (k : J ⟶ K) (l : K ⟶ L), map_pos I (k ≫ l) = (map_pos I k) ≫ (map_pos I l) . obviously)
(map_neg_id'   : ∀ (I J : C), map_neg J (𝟙 I) = 𝟙 (obj I J) . obviously)
(map_neg_comp' : ∀ {G H I J : C} (h : G ⟶ H) (i : H ⟶ I), map_neg J (h ≫ i) = (map_neg J i) ≫ (map_neg J h) . obviously)
(map_both : ∀ {I₀ I₁ J₀ J₁ : C} (i₂ : I₀ ⟶ I₁) (j₂ : J₀ ⟶ J₁),  (map_neg _ i₂) ≫ (map_pos _ j₂) =  (map_pos _ j₂) ≫ (map_neg _ i₂) . obviously)

/-- The prefunctor between the underlying quivers. -/
add_decl_doc difunctor.to_predifunctor


infixr ` ±⥤ `:26 := difunctor 

restate_axiom difunctor.map_pos_id'
attribute [simp] difunctor.map_pos_id
restate_axiom difunctor.map_neg_id'
attribute [simp] difunctor.map_neg_id
restate_axiom difunctor.map_pos_comp'
attribute [simp] difunctor.map_pos_comp
restate_axiom difunctor.map_neg_comp'
attribute [simp] difunctor.map_neg_comp

namespace difunctor

section 
variables {C : Type u₁} [category.{v₁} C] (D : Type u₂) [category.{v₂} D]


def dummy_neg (Γ : C ⥤ D) : C ±⥤ D :=
{
  obj := λ _, Γ.obj,
  map_pos := λ _ J₀ J₁ j₂, Γ.map j₂,
  map_neg := λ _ _ J _, 𝟙 (Γ.obj J) 
}
def dummy_pos (Γ : Cᵒᵖ ⥤ D) : C ±⥤ D :=
{
  obj := λ I _, Γ.obj (op I),
  map_pos := λ I _ _ _, 𝟙 (Γ.obj (op I)),
  map_neg := λ I₀ I₁ _ i₂, Γ.map i₂.op 
}

end
end difunctor

