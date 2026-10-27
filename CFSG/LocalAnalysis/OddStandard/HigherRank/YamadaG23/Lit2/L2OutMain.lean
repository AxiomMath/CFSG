module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OutT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OutPsl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OutPsu
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OutSuA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OutSuB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three

open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient)
open CFSG.ComponentClassification.HarrisLit.T1.P54 (GriessNativeTable)

theorem l2out_su43 (hG : GriessNativeTable) {H : Type} [Group H] [Finite H] (τ : H ≃* H)
    (hq : CFSG.IsQuasisimple H) (hL : CFSG.Blueprint.LieModel (H ⧸ center H) .PSU 4 3 1)
    {z : H} (hz : z ∈ center H) {k : ℕ} (hk : z ^ 2 ^ k = 1) (hτ : τ z ≠ z) :
    IsSU43 (H ⧸ CFSG.oddCore H) := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hτ (map_one τ)
  obtain ⟨hBq, ⟨e⟩⟩ := l2out_quot_data hq (l2out_oddCore_le_center hq hz1 hk)
  have hBL : CFSG.Blueprint.LieModel
      ((H ⧸ CFSG.oddCore H) ⧸ center (H ⧸ CFSG.oddCore H)) .PSU 4 3 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL
  obtain ⟨hdvd, hcyc⟩ := l2out_center_dvd_four_cyclic hG hBq hBL
    (CFSG.ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot H)
  have h3 := l2out_three_central τ hz hk hτ
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have h4 : Nat.card ↥(center (H ⧸ CFSG.oddCore H)) = 4 := by
    generalize Nat.card ↥(center (H ⧸ CFSG.oddCore H)) = c at hdvd h3 hle ⊢
    interval_cases c <;> omega
  exact ⟨hBq, h4, hcyc, hBL⟩

theorem gomiOuterPSLU4_of_table (hG : GriessNativeTable) : GomiOuterPSLU4 := by
  intro H _ _ τ hq hS hτ2 hz hT
  obtain ⟨z, hzc, ⟨k, hk⟩, hτz⟩ := hz
  have hsq : onCenterQuotient τ ^ 2 = 1 := l2out_onCenterQuotient_sq τ hτ2
  rcases hS with ⟨p, f, hp, hf, hmod, hL⟩ | ⟨p, f, hp, hf, hmod, hL⟩
  ·
    exfalso
    have hqodd : Odd (p ^ f) := by rw [Nat.odd_iff]; omega
    have hodd : Odd p := (Nat.odd_pow_iff hf.ne').1 hqodd
    have h2 : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.one_lt
    obtain ⟨Q, hQ, hev, hfix⟩ :=
      l2out_psl_fixed hp hodd hf (by omega) hL (onCenterQuotient τ) hsq
    exact l2out_not_solvable_T τ Q hQ hev hfix hT
  · by_cases h3 : p ^ f = 3
    ·
      obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 h3
      exact l2out_su43 hG τ hq hL hzc hk hτz
    ·
      exfalso
      have hqodd : Odd (p ^ f) := by rw [Nat.odd_iff]; omega
      have hodd : Odd p := (Nat.odd_pow_iff hf.ne').1 hqodd
      obtain ⟨Q, hQ, hev, hfix⟩ :=
        l2out_psu_fixed hp hodd hf (by omega) hL (onCenterQuotient τ) hsq
      exact l2out_not_solvable_T τ Q hQ hev hfix hT

end CFSG.OddStandard.HigherRank.YamadaG23
