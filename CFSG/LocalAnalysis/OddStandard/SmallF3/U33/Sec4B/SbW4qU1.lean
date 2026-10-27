module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4qU0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Syl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_card_S (hc : Ctx4C t L S x₁ x₂ lam rho tau) : Nat.card ↥S = 2 ^ 7 := by
  have h43 : twoCore t = zpowers t := hc.l43
  rw [hc.card_S, h43, Nat.card_zpowers, hc.hyp.ord_t]
  norm_num

theorem w4q_S_eq (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    ctxU t tau x₁ x₂ lam ⊓ invCent t = S := by
  have hSyl : IsSylowIn 2 S (invCent t) := ⟨hc.le_invCent, hc.isPGroup, hc.relIndex_odd⟩
  have hle : S ≤ ctxU t tau x₁ x₂ lam ⊓ invCent t := le_inf hc.S_le_U hc.le_invCent
  have hD2 : IsPGroup 2 ↥(ctxU t tau x₁ x₂ lam ⊓ invCent t) :=
    IsPGroup.to_inf_left (p := 2) (K := invCent t) hc.U_sylow.2.1
  obtain ⟨c, _hcH, hcj⟩ :=
    exists_cj_of_card_le hSyl inf_le_right hD2 (Subgroup.card_le_of_le hle)
  have hcard : Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ invCent t) = Nat.card ↥S := by
    rw [← hcj, card_cj]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

theorem w4q_idx_U
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) (hG : Sec4Glob G) :
    2 ∣ (ctxU t tau x₁ x₂ lam).index := by
  have hdvd : 2 ^ 11 ∣
      Nat.card ↥(ctxU t tau x₁ x₂ lam) * (ctxU t tau x₁ x₂ lam).index := by
    rw [Subgroup.card_mul_index (ctxU t tau x₁ x₂ lam)]
    exact hG.dvd
  rw [w4q_card_U hc] at hdvd
  have hpow : (2 : ℕ) ^ 11 = 2 ^ 9 * 2 ^ 2 := by norm_num
  rw [hpow] at hdvd
  have h22 : 2 ^ 2 ∣ (ctxU t tau x₁ x₂ lam).index :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2 ^ 9) hdvd
  exact dvd_trans (by norm_num : 2 ∣ 2 ^ 2) h22

theorem w4q_tU
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {w : G}
    (hw : w ∈ fourGrp x₁ x₂) : ∃ u ∈ ctxU t tau x₁ x₂ lam, u * t * u⁻¹ = t * w := by
  have hS : ctxU t tau x₁ x₂ lam ⊓ centralizer ({t} : Set G) = S := by
    simpa only [invCent] using w4q_S_eq hc
  have hcard : (conjIn (ctxU t tau x₁ x₂ lam) t).ncard = 4 := by
    have h := card_eq_ncard_conjIn_mul (ctxU t tau x₁ x₂ lam) t
    rw [w4q_card_U hc, hS, w4q_card_S hc] at h
    norm_num at h
    omega
  have hVn : (t • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
    rw [Set.ncard_smul_set]
    exact (hc.wreath.fourGrp_eq_omega).2.2
  have hsub : conjIn (ctxU t tau x₁ x₂ lam) t ⊆ t • (fourGrp x₁ x₂ : Set G) := by
    rintro u ⟨k, hk, hku⟩
    have hkM : k ∈ ctxM t tau x₁ x₂ := w4q_U_le_M hc hk
    have hmem : u ∈ conjIn (ctxM t tau x₁ x₂) t := ⟨k, hkM, hku⟩
    rwa [hc.tM] at hmem
  have hset : conjIn (ctxU t tau x₁ x₂ lam) t = t • (fourGrp x₁ x₂ : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq (hVn.trans hcard.symm))
  have hmem : t * w ∈ conjIn (ctxU t tau x₁ x₂ lam) t := by
    rw [hset]
    exact Set.mem_smul_set.mpr ⟨w, hw, by rw [smul_eq_mul]⟩
  obtain ⟨u, hu, hue⟩ := hmem
  exact ⟨u, hu, hue⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
