module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHubs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTwoFam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeG2
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.ParabAutIrr CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem perfectJoinHub_of_twoHub {X : Type} [Group X] (h : TwoHub X) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) : PerfectJoinHub p X := by
  intro S₀ J hNJ A hAJ hA a ha
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  exact h S₀ J hNJ p hp hp5 a (hAJ ha) ⟨k, congrArg Subtype.val hk⟩

section Models

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem perfectJoinHub_of_model_psl {n f : ℕ} (h : StatedClassicalModel Y .PSL n 2 f)
    (hf : 2 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpM : ¬ p ∣ 2 ^ f - 1) :
    PerfectJoinHub p Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact perfectJoinHub_of_borelQuotient (borelQuotient_sl
    ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm))
    (four_le_card_of_two_le hcard hf) rankOneNode_sl hp hp2 (by rw [hcard]; exact hpM)

theorem perfectJoinHub_of_model_psp {n f : ℕ} (h : StatedClassicalModel Y .PSp n 2 f)
    (hf : 2 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpM : ¬ p ∣ 2 ^ f - 1) :
    PerfectJoinHub p Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact perfectJoinHub_of_borelQuotient (borelQuotient_sp e) (four_le_card_of_two_le hcard hf)
    rankOneNode_sp hp hp2 (by rw [hcard]; exact hpM)

theorem perfectJoinHub_of_model_pomegaPlus {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) (hf : 2 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : ¬ p ∣ 2 ^ f - 1) : PerfectJoinHub p Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact perfectJoinHub_of_borelQuotient (borelQuotient_spinPlus hn3 e)
    (four_le_card_of_two_le hcard hf) (rankOneNode_spinPlus hn3) hp hp2
    (by rw [hcard]; exact hpM)

theorem perfectJoinHub_of_model_pomegaMinus {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) (hf : 2 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : ¬ p ∣ (2 ^ f) ^ 2 - 1) : PerfectJoinHub p Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hn4 : 4 ≤ n := by omega
  refine perfectJoinHub_of_borelQuotient (borelQuotient_spinMinus hirr hn4 e)
    (four_le_card_of_two_le hcard hf) (fun i => ?_) hp hp2 (by rw [hcard]; exact hpM)
  by_cases hk : i.val + 1 < n - 1
  · exact rankOneNode_spinMinus_long hirr hk
  · exact rankOneNode_spinMinus_short hirr hk

theorem perfectJoinHub_of_model_psu {n f : ℕ} (h : StatedClassicalModel Y .PSU n 2 f)
    (hf : 2 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpM : ¬ p ∣ (2 ^ f) ^ 2 - 1) :
    PerfectJoinHub p Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  exact perfectJoinHub_of_borelQuotient (borelQuotient_su hcard (by omega) ζ hζ e) hq4
    (rankOneNode_su hcard) hp hp2 (by rw [hcard]; exact hpM)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem perfectJoinHub_of_g2 {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : Y ≃* AdjointQuotient .G2 K) (hq4 : 4 ≤ Nat.card K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : ¬ p ∣ Nat.card K - 1) : PerfectJoinHub p Y := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  exact perfectJoinHub_of_borelQuotient (borelQuotient_g2 e) hq4 rankOneNode_g2 hp hp2 hpM

end Models

open ToralCensus in
theorem perfectJoinHub_of_classicalIndex {X : Type} [Group X] [Finite X]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (hG2 : ∀ q, d.1 ≠ .G2 q) (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ht : IndexTorusFree p d.1) : PerfectJoinHub p X := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hd] at h
    rcases exponent_eq_one_or_two_le (P := fun c => ¬ p ∣ c - 1) hd ht with hf | ⟨hf, hpM⟩
    · rw [hf] at h
      exact perfectJoinHub_of_twoHub (twoHub_of_model_psl h) hp hp5
    · exact perfectJoinHub_of_model_psl h hf hp hp2 hpM
  | twistedA r q =>
    change q.p = 2 at hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hd] at h
    rcases exponent_eq_one_or_two_le (P := fun c => ¬ p ∣ c ^ 2 - 1) hd ht with hf | ⟨hf, hpM⟩
    · rw [hf] at h
      exact perfectJoinHub_of_twoHub (twoHub_of_model_psu h) hp hp5
    · exact perfectJoinHub_of_model_psu h hf hp hp2 hpM
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have h : StatedClassicalModel X .PSp r 2 q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rwa [hd] at h
      · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
          (by omega) e
        rwa [hd] at h
    rcases exponent_eq_one_or_two_le (P := fun c => ¬ p ∣ c - 1) hd ht with hf | ⟨hf, hpM⟩
    · rw [hf] at h
      exact perfectJoinHub_of_twoHub (twoHub_of_model_psp h) hp hp5
    · exact perfectJoinHub_of_model_psp h hf hp hp2 hpM
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    rcases exponent_eq_one_or_two_le (P := fun c => ¬ p ∣ c - 1) hd ht with hf | ⟨hf, hpM⟩
    · rw [hf] at h
      exact perfectJoinHub_of_twoHub (twoHub_of_model_pomegaPlus h) hp hp5
    · exact perfectJoinHub_of_model_pomegaPlus h hf hp hp2 hpM
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    rcases exponent_eq_one_or_two_le (P := fun c => ¬ p ∣ c ^ 2 - 1) hd ht with hf | ⟨hf, hpM⟩
    · rw [hf] at h
      exact perfectJoinHub_of_twoHub (twoHub_of_model_pomegaMinus h) hp hp5
    · exact perfectJoinHub_of_model_pomegaMinus h hf hp hp2 hpM
  | G2 q => exact absurd rfl (hG2 q)
  | _ => exact hd.elim

section Catalog


open ToralCensus in
theorem perfectJoinHub_of_index {X : Type} [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1) (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ht : IndexTorusFree p d.1) : PerfectJoinHub p X := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, hv⟩ := d
  cases d with
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rcases exponent_eq_one_or_two_le (P := fun c => ¬ p ∣ c - 1) hd ht with hf | ⟨hf, hpM⟩
    · have hc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hd, hf, pow_one]
      omega
    · have hc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
      have h4 : 4 ≤ 2 ^ q.exponent :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
      exact perfectJoinHub_of_g2 (e.trans b.symm) (by rw [hK, hc]; exact h4) hp hp2
        (by rw [hK, hc]; exact hpM)
  | _ => exact perfectJoinHub_of_classicalIndex _ hd (fun q h => by cases h) e hp hp5 ht

end Catalog

end CFSG.AGLEmbedding
