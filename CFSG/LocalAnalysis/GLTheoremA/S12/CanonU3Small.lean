module
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Order

import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
import CFSG.Quasithin.EmptyFaithful.S146zYFacts
import CFSG.Quasithin.EmptyFaithful.S146zYRes
import CFSG.Quasithin.H13.NQCoreP134Main
import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp (lambda2_of_hasLabel)


section Certs


theorem false_of_A {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {n : ℕ}
    {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hA : labL.tag = .A) : False := by
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  have hm1 := h.labL_n_eq_one_of_untwisted (by rw [hA]; exact trivial)
  have hc : CFSG.StandardType.markChar labL = 2 := by simp [CFSG.StandardType.markChar, hA]
  have hcard : Nat.card S = ordA labL.rank 2 := by
    rw [h.card_eq hc]
    simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, hA, hm1, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have hrank2 : 2 ≤ labL.rank := by
    have h2 := hlam.2
    rw [hA] at h2
    by_contra hlt
    have h1 : labL.rank = 1 := by omega
    have hn2 := h2.2 h1
    rw [hm1] at hn2
    omega
  have hrank6 : labL.rank ≤ 6 := by
    by_cases h5 : 5 ≤ labL.rank
    · have hl := largeEvenLabelAll_typeA_two hA hm1 h5
      have hT := ggTorusLift_of_labelAll h.center_eq_bot h.innDiagKind hl
      have := h.rank_le _ hT
      omega
    · omega
  have hdvd := h.card_dvd
  rw [hcard] at hdvd
  have hcases : labL.rank = 2 ∨ labL.rank = 3 ∨ labL.rank = 4 ∨ labL.rank = 5 ∨
      labL.rank = 6 := by omega
  rcases hcases with hr | hr | hr | hr | hr
  · rw [hr] at hdvd
    exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hdvd
  · rw [hr] at hdvd
    exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hdvd
  · rw [hr] at hdvd
    exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hdvd
  · rw [hr] at hdvd
    exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hdvd
  · rw [hr] at hdvd
    exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hdvd

theorem false_of_D3 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {n : ℕ}
    {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hD : labL.tag = .D)
    (h3 : labL.rank = 3) : False := by
  have hm1 := h.labL_n_eq_one_of_untwisted (by rw [hD]; exact trivial)
  have hc : CFSG.StandardType.markChar labL = 2 := by simp [CFSG.StandardType.markChar, hD]
  have hcard : Nat.card S = ordA 3 2 := by
    rw [h.card_eq hc]
    simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, hD, h3, hm1, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have hdvd := h.card_dvd
  rw [hcard] at hdvd
  exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hdvd

theorem false_of_twD2 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hD : labL.tag = .twD)
    (h2 : labL.rank = 2) : False := by
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  have hc : CFSG.StandardType.markChar labL = 2 := by simp [CFSG.StandardType.markChar, hD]
  have hpow : (2 ^ (2 * labL.n)) ^ 2 = 2 ^ (4 * labL.n) := by
    rw [← pow_mul]
    ring_nf
  have hmpos : 0 < labL.n := by have := hlam.1; omega
  have hord : ordA 1 (2 ^ (2 * labL.n)) = 2 ^ (2 * labL.n) * (2 ^ (4 * labL.n) - 1) := by
    rw [CFSG.RankThree.PartOne.S12K.ordA_one_eq (g := 2 * labL.n) (by omega), hpow]
  have hcard : Nat.card S = 2 ^ (2 * labL.n) * (2 ^ (4 * labL.n) - 1) := by
    rw [h.card_eq hc]
    simpa [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, hD, h2, CFSG.SeitzReduction.F4Pilot.evenLieOrder] using hord
  have hmle : labL.n ≤ n := Nat.le_of_dvd h.odd.pos h.dvd
  have hpowdvd : 2 ^ (3 * n) ∣ Nat.card S :=
    (two_pow_dvd_ordTwistedA n).trans h.card_dvd
  rw [hcard] at hpowdvd
  have hFodd : Odd (2 ^ (4 * labL.n) - 1) := by
    have h := CFSG.Timmesfeld.Orders.odd_pow_sub_one (f := 2 * labL.n) (a := 2)
      (by omega) (by norm_num)
    simpa [hpow] using h
  have hcop : Nat.Coprime (2 ^ (3 * n)) (2 ^ (4 * labL.n) - 1) :=
    (hFodd.coprime_two_left).pow_left (3 * n)
  have hdvd2 : 2 ^ (3 * n) ∣ 2 ^ (2 * labL.n) := hcop.dvd_of_dvd_mul_right hpowdvd
  have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd2
  have hn3 := h.three_le
  omega

theorem false_of_B_or_C {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J)
    (hB : labL.tag = .B ∨ labL.tag = .C) : False := by
  have hB' := hB
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  rcases hB with hB | hB
  all_goals
    have hm1 := h.labL_n_eq_one_of_untwisted (by rw [hB]; exact trivial)
    have hm1' : labL.n = 1 := hm1
    simp only [LargeEvenInLambda2, hB] at hlam
    have hrank3 : 3 ≤ labL.rank := by
      have h2 := hlam.2
      by_contra hlt
      have h1 : labL.rank = 2 := by omega
      have hn2 := h2.2 h1
      omega
    have hc : CFSG.StandardType.markChar labL = 2 := by
      simp [CFSG.StandardType.markChar, hB]
    have hcard : Nat.card S = ordBC labL.rank 2 := by
      rw [h.card_eq hc]
      simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
        CFSG.StandardType.markDeg, hB, hm1', CFSG.SeitzReduction.F4Pilot.evenLieOrder]
    have hl := largeEvenLabelAll_sp_two hB' hm1 hrank3
    have hT := ggTorusLift_of_labelAll h.center_eq_bot h.innDiagKind hl
    have hrankle := h.rank_le _ hT
    have hrank4 : labL.rank ≤ 4 := by omega
    have hdvd := h.card_dvd
    rw [hcard] at hdvd
    have hcases : labL.rank = 3 ∨ labL.rank = 4 := by omega
    rcases hcases with h3 | h4
    · rw [h3] at hdvd
      exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hdvd
    · rw [h4] at hdvd
      exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hdvd

theorem false_of_B2der {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hB : labL.tag = .B2der) :
    False := by
  obtain ⟨t, r, m⟩ := labL
  dsimp only at hB
  subst hB
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  simp only [LargeEvenInLambda2] at hlam
  obtain ⟨-, rfl, rfl⟩ := hlam
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel
    h.hasLabel_of_innDiag
  have h360 : Nat.card S = 360 := by
    have hc := CFSG.LocalAnalysis.GLTheoremA.card_of_B2der hM
    rwa [Nat.card_congr
      (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot h.center_eq_bot).toEquiv] at hc
  have hdvd := h.card_dvd
  rw [h360] at hdvd
  exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hdvd

theorem u3CoreOn_lin : U3CoreOn FamLin := by
  intro S _ _ labL β n J hF h
  rcases hF with hA | ⟨hD, h3⟩ | ⟨hD, h2⟩
  · exact (false_of_A h hA).elim
  · exact (false_of_D3 h hD h3).elim
  · exact (false_of_twD2 h hD h2).elim

theorem u3CoreOn_symp : U3CoreOn FamSymp := by
  intro S _ _ labL β n J hF h
  rcases hF with hB | hC | hB2
  · exact (false_of_B_or_C h (Or.inl hB)).elim
  · exact (false_of_B_or_C h (Or.inr hC)).elim
  · exact (false_of_B2der h hB2).elim

theorem false_of_D_of_rank_ne_three {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J)
    (hD : labL.tag = .D) (h3 : labL.rank ≠ 3) : False := by
  obtain ⟨t, l, m⟩ := labL
  dsimp only at hD h3 ⊢
  subst hD
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  have hrank4 : 4 ≤ l := by
    have h3' := hlam.2
    dsimp only [LargeEvenInLambda2] at h3'
    omega
  have hm1 := h.labL_n_eq_one_of_untwisted (by simp [LargeEvenUntwisted])
  have hm1' : m = 1 := hm1
  have hc : CFSG.StandardType.markChar ⟨.D, l, m⟩ = 2 := by simp [CFSG.StandardType.markChar]
  have hlab : GGOrthRestLabel 3 ⟨.D, l, m⟩ := ⟨hrank4, Or.inr ⟨rfl, hm1, rfl⟩⟩
  have hl : LargeEvenLabelAll ⟨.D, l, m⟩ fun R _ _ _ => GGTorusLift 3 (l - 1) R :=
    LargeEvenLabelAll.mono (fun _ _ I _ hP => hP.2)
      (OrthRest.labelAll CFSG.StandardType.ggOrthRestTorusLiftInput_holds (by norm_num) hlab)
  have hT := ggTorusLift_of_labelAll h.center_eq_bot h.innDiagKind hl
  have hrankle := h.rank_le _ hT
  have hrank_eq : l = 4 := by omega
  have hcard : Nat.card S = ordD 4 2 := by
    rw [h.card_eq hc, hrank_eq]
    simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, hm1', CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have hdvd := h.card_dvd
  rw [hcard] at hdvd
  exact (not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hdvd).elim

theorem u3CoreOn_orthPlus : U3CoreOn fun lab => lab.tag = .D ∧ lab.rank ≠ 3 := by
  intro S _ _ labL β n J hF h
  exact (false_of_D_of_rank_ne_three h hF.1 hF.2).elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
