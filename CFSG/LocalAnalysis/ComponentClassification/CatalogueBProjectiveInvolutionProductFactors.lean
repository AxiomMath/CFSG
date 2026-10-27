module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionProduct
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolutionProduct

variable {X Y : Type*} [Group X] [Group Y]

theorem product_eq_sup_factors (U : Subgroup X) (V : Subgroup Y) :
    U.prod V = U.prod (⊥ : Subgroup Y) ⊔ (⊥ : Subgroup X).prod V := by
  apply le_antisymm
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx' : (x, (1 : Y)) ∈ U.prod (⊥ : Subgroup Y) := ⟨hx, by simp⟩
    have hy' : ((1 : X), y) ∈ (⊥ : Subgroup X).prod V := ⟨by simp, hy⟩
    have h := (U.prod (⊥ : Subgroup Y) ⊔ (⊥ : Subgroup X).prod V).mul_mem
      ((show U.prod (⊥ : Subgroup Y) ≤
        U.prod (⊥ : Subgroup Y) ⊔ (⊥ : Subgroup X).prod V from le_sup_left) hx')
      ((show (⊥ : Subgroup X).prod V ≤
        U.prod (⊥ : Subgroup Y) ⊔ (⊥ : Subgroup X).prod V from le_sup_right) hy')
    simpa using h
  · exact sup_le (Subgroup.prod_mono le_rfl bot_le)
      (Subgroup.prod_mono bot_le le_rfl)

@[expose] def leftFactorEquiv (U : Subgroup X) :
    U.prod (⊥ : Subgroup Y) ≃* U where
  toFun z := ⟨z.val.1, z.property.1⟩
  invFun x := ⟨(x.val, 1), x.property, by simp⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (Subgroup.mem_bot.mp z.property.2).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def rightFactorEquiv (V : Subgroup Y) :
    (⊥ : Subgroup X).prod V ≃* V where
  toFun z := ⟨z.val.2, z.property.2⟩
  invFun y := ⟨(1, y.val), by simp, y.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (Subgroup.mem_bot.mp z.property.1).symm
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem leftFactor_eq_inf_kernel (L : Subgroup (X × Y)) [Group.IsPerfect L]
    (hL : L.IsSubnormal) :
    (L.map (MonoidHom.fst X Y)).prod (⊥ : Subgroup Y) =
      L ⊓ (MonoidHom.snd X Y).ker := by
  have heq := perfect_subnormal_eq_product L hL
  ext z
  change (z.1 ∈ L.map (MonoidHom.fst X Y) ∧ z.2 = 1) ↔
    z ∈ L ∧ z.2 = 1
  conv_rhs => rw [heq]
  change (_ ∧ z.2 = 1) ↔ (_ ∧ z.2 ∈ L.map (MonoidHom.snd X Y)) ∧ z.2 = 1
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨⟨hx, hy.symm ▸ Subgroup.one_mem _⟩, hy⟩
  · exact fun h => ⟨h.1.1, h.2⟩

theorem rightFactor_eq_inf_kernel (L : Subgroup (X × Y)) [Group.IsPerfect L]
    (hL : L.IsSubnormal) :
    (⊥ : Subgroup X).prod (L.map (MonoidHom.snd X Y)) =
      L ⊓ (MonoidHom.fst X Y).ker := by
  have heq := perfect_subnormal_eq_product L hL
  ext z
  change (z.1 = 1 ∧ z.2 ∈ L.map (MonoidHom.snd X Y)) ↔ z ∈ L ∧ z.1 = 1
  conv_rhs => rw [heq]
  change (z.1 = 1 ∧ _) ↔ (z.1 ∈ L.map (MonoidHom.fst X Y) ∧ _) ∧ z.1 = 1
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨⟨hx.symm ▸ Subgroup.one_mem _, hy⟩, hx⟩
  · exact fun h => ⟨h.2, h.1.2⟩

theorem map_subgroupOf_image {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A B : Subgroup G) (hAB : A ≤ B) :
    (A.subgroupOf B).map (f.subgroupMap B) = (A.map f).subgroupOf (B.map f) := by
  apply Subgroup.map_injective (f := (B.map f).subtype) (B.map f).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hAB), Subgroup.map_map]
  have hcomp : (B.map f).subtype.comp (f.subgroupMap B) = f.comp B.subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAB]

theorem normal_subgroupOf_image {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A B : Subgroup G) (hAB : A ≤ B)
    (hA : (A.subgroupOf B).Normal) :
    ((A.map f).subgroupOf (B.map f)).Normal := by
  rw [← map_subgroupOf_image f A B hAB]
  exact Subgroup.Normal.map hA (f.subgroupMap B) (f.subgroupMap_surjective B)

end CFSG.ComponentClassification.CatalogueBProjectiveInvolutionProduct
