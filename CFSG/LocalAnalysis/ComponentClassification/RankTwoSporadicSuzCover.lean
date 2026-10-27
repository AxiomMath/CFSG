module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEnd175
public import CFSG.Sporadic.Recognition.SuzMultiplier
public import CFSG.Sporadic.Recognition.HeMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndModel

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open Subgroup CFSG.Open CFSG.CosetTable CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.Recognition.SuzMultiplier

theorem suzCentralTwoGroupOrderBound_of_checks
    (hTab : suzTabCheck = true)
    (hRho0 : suzRho0Check = true)
    (hL0 : SuzIndexP1) (hL1 : SuzIndexP2) (hL2 : SuzCardP2) :
    SuzCentralTwoGroupOrderBound := by
  intro L _ _ hLq hL2' ⟨e⟩
  have hperf : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
  have f := suzEquivM
  have e' : L ⧸ center L ≃* suzM := e.trans f
  have h := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess (S := suzM) hperf e'
  have h6 : Nat.card (center L) ∣ 6 := by
    rcases card_griessHopfMultiplier_M hTab hRho0 hL0 hL1 hL2 with h36 | h36 <;> rw [h36] at h
    · exact h.trans (by norm_num)
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hL2'.exists_card_eq
  rw [hk] at h6 ⊢
  rcases k with _ | _ | k
  · norm_num
  · norm_num
  · exfalso
    have h4 : 4 ∣ 6 := (pow_dvd_pow 2 (show 2 ≤ k + 2 by omega)).trans h6
    omega

theorem fix1782_suzInv_one :
    fix1782 (suzInv 1) = 54 :=
  suzInv_fixed (i := 1) (by norm_num)

theorem exists_conj_suzInv_zero
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzM) (h2 : orderOf g = 2) (h42 : fix1782 g = 42) :
    ∃ c ∈ suzM, c * suzInv 0 * c⁻¹ = g := by
  obtain ⟨c, hcT, h0 | h1⟩ := suzM_involution_class hg h2
  · by_cases hcM : c ∈ suzM
    · exact ⟨c, hcM, h0⟩
    · obtain ⟨x, hxD, hxM⟩ :=
        IsConcreteLE.not_le_iff_exists.1 (invD_not_le_M (i := 0) (by norm_num))
      obtain ⟨hxC, hxT⟩ := invD_le_centT (i := 0) (by norm_num) hxD
      have hcomm : x * suzInv 0 = suzInv 0 * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
      have hab : (⟨c, hcT⟩ * ⟨x, hxT⟩ : suzT) ∈ suzM.subgroupOf suzT :=
        (Subgroup.mul_mem_iff_of_index_two suzM_index_T).2 (by
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          exact iff_of_false hcM hxM)
      refine ⟨c * x, Subgroup.mem_subgroupOf.1 hab, ?_⟩
      rw [← h0, mul_inv_rev, show c * x * suzInv 0 * (x⁻¹ * c⁻¹) =
        c * (x * suzInv 0) * x⁻¹ * c⁻¹ by group, hcomm]
      group
  · exfalso
    have h54 := fix1782_conj c (suzInv 1)
    rw [h1, h42, fix1782_suzInv_one] at h54
    exact absurd h54 (by decide)

theorem exists_conj_suzGenP_d
    (hTab : suzTabCheck = true) {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzM)
    (h2 : orderOf g = 2) (h42 : fix1782 g = 42) : ∃ c ∈ suzM, c * suzGenP 3 * c⁻¹ = g := by
  obtain ⟨c, hc, rfl⟩ := exists_conj_suzInv_zero hg h2 h42
  obtain ⟨c₀, hc₀, hd⟩ := exists_conj_suzInv_zero (suzGenP_mem 3) (orderOf_suzGenP_d hTab)
    (fix1782_suzGenP_d hTab)
  refine ⟨c * c₀⁻¹, suzM.mul_mem hc (suzM.inv_mem hc₀), ?_⟩
  rw [← hd]
  group

theorem suzDoubleCoverTwoBLift_of_checks
    (hTab : suzTabCheck = true)
    (hRho0 : suzRho0Check = true) (hRhoJ2 : suzRhoJ2Check = true)
    (hL0 : SuzIndexP1) (hL1 : SuzIndexP2) (hL2 : SuzCardP2) :
    SuzDoubleCoverTwoBLift := by
  intro L _ _ hLq t ht hZ π hπ hker v hv2 h42
  have : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
  obtain ⟨c, hc, hcv⟩ := exists_conj_suzGenP_d hTab (π v).2
    (by rw [Subgroup.orderOf_coe]; exact hv2) h42
  have hcen : zpowers t ≤ center L := hZ ▸ le_rfl
  have hv : π v = ⟨c, hc⟩ * suzGen suzD * (⟨c, hc⟩ : suzM)⁻¹ := Subtype.ext hcv.symm
  exact sq_eq_of_lift_conj_d hTab hRho0 hRhoJ2 hL0 hL1 hL2 π hπ ht hker hcen hv

end CFSG.ComponentClassification.RankTwoSporadic.Suz
