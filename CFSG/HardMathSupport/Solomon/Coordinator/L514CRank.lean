module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KThirty2A
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremB

theorem l514c_simple_or_card {r : ℕ} {Y : Type} [Group Y] (h : IsL3Eps r Y) :
    (IsSimpleGroup Y ∧ 3 ∣ Nat.card Y) ∨ Nat.card Y = 72 := by
  rcases h with ⟨hr, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨hr, F, hF, hFin, hcard, ⟨e⟩⟩
  · obtain ⟨p, f, hK, hmod, h2⟩ := exists_true_data F (by rw [hcard]; exact hr)
    left
    let e' := e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm
    have hq := (isQuasisimple_slPi hK (fun h => by omega)).2
    exact ⟨e'.isSimpleGroup, by rw [Nat.card_congr e'.toEquiv]; exact three_dvd_card_slPi_quot hK hmod⟩
  · obtain ⟨p, f, rfl, ⟨hFd⟩⟩ := exists_unitaryFieldData hcard
    have hK : PiField false p f F := ⟨hFd.prime, hFd.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩
    have hmod : ModThree false (p ^ f) := hr
    by_cases h2 : 2 < p ^ f
    · left
      let e' := e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm
      have hq := (isQuasisimple_slPi hK (fun h => by omega)).2
      exact ⟨e'.isSimpleGroup,
        by rw [Nat.card_congr e'.toEquiv]; exact three_dvd_card_slPi_quot hK hmod⟩
    · right
      have h2' : p ^ f = 2 := pow_eq_two_of_not_two_lt hFd h2
      have hc : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) *
          Nat.gcd 3 (p ^ f + 1) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) :=
        CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hFd
      rw [Nat.card_congr e.toEquiv]
      generalize Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) = N at hc ⊢
      rw [h2'] at hc
      norm_num at hc
      omega

theorem l514c_isLThreeEps_of_isL3Eps {r : ℕ} {Y : Type} [Group Y] (h : IsL3Eps r Y)
    {Y' : Type} [Group Y'] (e : Y' ≃* Y) : UniquenessMaximal.IsLThreeEps Y' := by
  rcases h with ⟨hr, F, hF, hFin, hcard, ⟨e'⟩⟩ | ⟨hr, F, hF, hFin, hcard, ⟨e'⟩⟩
  · exact Or.inl ⟨F, hF, hFin, by rw [hcard]; exact hr, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨F, hF, hFin, r, hcard, hr, ⟨e.trans e'⟩⟩

theorem lemma514Cover_inputL3rk_holds : LocalBalance.Lemma514CoverNs.InputL3rk := by
  intro Y _ _ r h E hE
  rcases l514c_simple_or_card h with ⟨hs, h3⟩ | hc
  · have hO : GLAPPrimeCore 3 Y = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 Y) with h1 | h1
      · exact h1
      · exfalso
        have hcop := coprime_card_gLAPPrimeCore_aux 3 Y
        rw [h1, Subgroup.card_top] at hcop
        exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) h3) (by norm_num)
    let e0 : (Y ⧸ GLAPPrimeCore 3 Y) ≃* Y :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    exact UniquenessMaximal.rank_le_nine_of_isLThreeEps Y
      (l514c_isLThreeEps_of_isL3Eps h e0) E hE
  · have hEp : IsPGroup 3 ↥E := isPGroup_of_isElemAbelian' hE
    obtain ⟨n, hn⟩ := hEp.exists_card_eq
    have hd : Nat.card E ∣ 72 := hc ▸ Subgroup.card_subgroup_dvd_card E
    rw [hn] at hd ⊢
    have : n ≤ 2 := by
      by_contra hn3
      have : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
      have := this.trans hd
      omega
    calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      _ = 9 := by norm_num

end CFSG.HardMathSupport.Solomon.Coordinator
