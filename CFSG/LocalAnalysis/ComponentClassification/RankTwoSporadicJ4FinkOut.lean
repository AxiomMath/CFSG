module

public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTOutAuto
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMovedPerfect

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J4Fink

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open scoped Pointwise

theorem exists_eq_conj_J
    (α : MulAut J) : ∃ k : J, α = MulAut.conj k := by
  have hF := j4Facts
  have hM := hF.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J S (α • S)
  have hgS : ((α • S : Sylow 2 J) : Subgroup J) = MulAut.conj g • P0 := by
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  have hβ : ∀ x ∈ P0, ((MulAut.conj g)⁻¹ * α) x ∈ P0 := by
    intro x hx
    have h1 : α x ∈ ((α • S : Sylow 2 J) : Subgroup J) := by
      rw [Sylow.pointwise_smul_def, Sylow.coe_ofCard]
      exact Subgroup.smul_mem_pointwise_smul x α P0 hx
    rw [hgS, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rw [MulAut.mul_apply, ← hyx, MulAut.smul_def, MulAut.inv_apply_self]
    exact hy
  obtain ⟨k, hk⟩ := aut_of_maps_P0 hF ((MulAut.conj g)⁻¹ * α) hβ
  refine ⟨g * k, MulEquiv.ext fun x => ?_⟩
  have h := hk x
  rw [MulAut.mul_apply] at h
  have h' : α x = g * (k * x * k⁻¹) * g⁻¹ := by
    rw [← h, MulAut.conj_inv_apply]
    group
  rw [h', MulAut.conj_apply]
  group

theorem center_J :
    center J = ⊥ := by
  have hF := j4Facts
  have : IsSimpleGroup J := isSimpleGroup_J hF
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center J) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : J, x * y = y * x := by
      intro x y
      have hx : x ∈ center J := by
        rw [h]
        exact mem_top x
      exact (mem_center_iff.mp hx y).symm
    have hN : normalizer (Eg uJ 11 : Set J) = ⊤ := by
      refine eq_top_iff.mpr fun g _ => mem_normalizer_iff.mpr fun x => ?_
      rw [hcomm g x, mul_assoc, mul_inv_cancel, mul_one]
    rw [normalizer_Eg_eq_Hj hF] at hN
    exact (isCoatom_Hj hF).1 hN

theorem autModel_J :
    AutModel J J ⊤ :=
  autModel_top center_J exists_eq_conj_J

end CFSG.ComponentClassification.RankTwoSporadic.J4Fink
