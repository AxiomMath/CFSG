module

public import CFSG.GroupTheory.SteinbergBSInvolutoryInvertedCount
public import CFSG.GroupTheory.SmallFixedTwoGroup.InvertedBasic

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

theorem card_inverted_mul_card_fixed_of_odd {θ : MulAut G} (hθ : θ * θ = 1) {R : Subgroup G}
    (hR : ∀ r ∈ R, θ r ∈ R) (hodd : Odd (Nat.card R)) :
    Nat.card {r : R // θ r = (r : G)⁻¹} * Nat.card {r : R // θ r = (r : G)} =
      Nat.card R := by
  let θR : MulAut R :=
    { toFun := fun r => ⟨θ r, hR r r.2⟩
      invFun := fun r => ⟨θ r, hR r r.2⟩
      left_inv := fun r => Subtype.ext (apply_apply_of_mul_self_eq_one hθ (r : G))
      right_inv := fun r => Subtype.ext (apply_apply_of_mul_self_eq_one hθ (r : G))
      map_mul' := fun a b => Subtype.ext (map_mul θ (a : G) (b : G)) }
  have hcoe : ∀ r : R, (θR r : G) = θ (r : G) := fun r => rfl
  have hθR : θR ^ 2 = 1 := by
    ext r
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hcoe, hcoe]
    exact apply_apply_of_mul_self_eq_one hθ (r : G)
  have hiff_inv : ∀ x : R, (θR x = x⁻¹) ↔ (θ (x : G) = (x : G)⁻¹) := by
    intro x
    simp only [Subtype.ext_iff, hcoe, Subgroup.coe_inv]
  have hiff_fix : ∀ x : R, (θR x = x) ↔ (θ (x : G) = (x : G)) := by
    intro x
    simp only [Subtype.ext_iff, hcoe]
  have hiff_mem : ∀ x : R, (θR x = x) ↔ x ∈ θR.toMonoidHom.eqLocus (MonoidHom.id R) := by
    intro x
    simpa using (MonoidHom.mem_eqLocusM (f := θR.toMonoidHom) (g := MonoidHom.id R)
      (x := x)).symm
  have hcard_inv :
      Nat.card {r : R // θ (r : G) = (r : G)⁻¹} = Nat.card {x : R // θR x = x⁻¹} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff_inv).symm
  have hcard_fix : Nat.card {r : R // θ (r : G) = (r : G)} =
      Nat.card (θR.toMonoidHom.eqLocus (MonoidHom.id R)) :=
    Nat.card_congr ((Equiv.subtypeEquivRight hiff_fix).symm.trans
      (Equiv.subtypeEquivRight hiff_mem))
  rw [hcard_inv, hcard_fix]
  exact CFSG.GroupTheory.SteinbergBS.card_inverted_mul_card_fixed (X := R) hodd hθR

end CFSG.GroupTheory.SmallFixedTwoGroup
