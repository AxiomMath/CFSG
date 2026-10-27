module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerLinearDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerUnitaryDiag
public import CFSG.LieType.SeitzGeneration.RankVacuity

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.SeitzGeneration (RankLE2 not_rankLE2_linear not_rankLE2_unitary)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

section Rank

theorem rankLE2_of_pRank_eq_two {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (h : CFSG.Open.pRank p (⊤ : Subgroup P) = 2) : RankLE2 p P := by
  intro F hF
  haveI : Fact p.Prime := ⟨hp⟩
  have hFp : IsPGroup p ↥F := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hF.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  have hbdd : BddAbove {k | ∃ E : Subgroup P, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card P, ?_⟩
    rintro k' ⟨E, -, -, hE⟩
    have h1 : Nat.card E ≤ Nat.card P := Subgroup.card_le_card_group E
    have h2 : k' < p ^ k' := Nat.lt_pow_self hp.one_lt
    rw [hE] at h1
    omega
  have hk2 : k ≤ 2 := by
    have hmem : k ∈ {k | ∃ E : Subgroup P, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian p E ∧
        Nat.card E = p ^ k} := ⟨F, le_top, hF, hk⟩
    have := le_csSup hbdd hmem
    unfold CFSG.Open.pRank at h
    omega
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk2

end Rank

section Linear

theorem chevTwoPClosureOddFamily_linearDiagThree :
    ChevTwoPClosureOddFamily LieFamilyLinearDiagThree := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | A r q =>
    obtain ⟨e⟩ := he
    obtain ⟨hr2, hp3⟩ := hF
    have hdi' : q.p = 2 := hdi
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    haveI : CharP (GaloisField q.p q.exponent) 2 := by
      rw [← hdi']
      infer_instance
    let e1 : L ≃* projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
      e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          (r + 1) (GaloisField q.p q.exponent)))
    subst hr2
    subst hp3
    exact PClosureOdd.of_mulEquiv e1.symm pClosureOdd_projectiveSL_three
  | _ => exact absurd hF (by simp [LieFamilyLinearDiagThree])

theorem chevTwoPClosureOddFamily_linearDiagBig :
    ChevTwoPClosureOddFamily LieFamilyLinearDiagBig := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | A r q =>
    exfalso
    obtain ⟨e⟩ := he
    obtain ⟨hdvd, hne⟩ := hF
    have hpr : p ∣ r + 1 := (Nat.dvd_gcd_iff.1 hdvd).1
    have hpq : p ∣ q.card - 1 := (Nat.dvd_gcd_iff.1 hdvd).2
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hr4 : 4 ≤ r := by
      by_contra hlt
      have hple : p ≤ r + 1 := Nat.le_of_dvd (by omega) hpr
      rcases (show r = 2 ∨ r = 3 by omega) with rfl | rfl
      · have : p ∣ 3 := hpr
        exact hne ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this⟩
      · have h4 : p ∣ 2 ^ 2 := by simpa using hpr
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4)
        exact hp2 this
    exact not_rankLE2_linear hv hp hpq hr4
      (RankLE2.of_mulEquiv e (rankLE2_of_pRank_eq_two hp hrk))
  | _ => exact absurd hF (by simp [LieFamilyLinearDiagBig])

end Linear

section Unitary

theorem chevTwoPClosureOddFamily_unitaryDiagThree :
    ChevTwoPClosureOddFamily LieFamilyUnitaryDiagThree := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | twistedA r q =>
    obtain ⟨e⟩ := he
    obtain ⟨hr2, hp3⟩ := hF
    have hdi' : q.p = 2 := hdi
    obtain ⟨-, K, _, _, hcard, ⟨e1⟩⟩ := statedClassicalModel_of_twistedA r q hv e
    have hU : UnitaryFieldData q.p q.exponent K :=
      ⟨q.prime_p, q.exponent_pos, by rw [hcard, ← pow_mul, mul_comm]⟩
    subst hr2
    subst hp3
    exact PClosureOdd.of_mulEquiv ((unitaryPSUEquiv hU (by omega)).trans e1.symm)
      (pClosureOdd_unitaryPSU_three hdi' hU)
  | _ => exact absurd hF (by simp [LieFamilyUnitaryDiagThree])

theorem chevTwoPClosureOddFamily_unitaryDiagBig :
    ChevTwoPClosureOddFamily LieFamilyUnitaryDiagBig := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | twistedA r q =>
    exfalso
    obtain ⟨e⟩ := he
    obtain ⟨hdvd, hne⟩ := hF
    have hpr : p ∣ r + 1 := (Nat.dvd_gcd_iff.1 hdvd).1
    have hpq : p ∣ q.card + 1 := (Nat.dvd_gcd_iff.1 hdvd).2
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hr4 : 4 ≤ r := by
      by_contra hlt
      have hple : p ≤ r + 1 := Nat.le_of_dvd (by omega) hpr
      rcases (show r = 2 ∨ r = 3 by omega) with rfl | rfl
      · have : p ∣ 3 := hpr
        exact hne ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this⟩
      · have h4 : p ∣ 2 ^ 2 := by simpa using hpr
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4)
        exact hp2 this
    exact not_rankLE2_unitary hv hp hpq hr4
      (RankLE2.of_mulEquiv e (rankLE2_of_pRank_eq_two hp hrk))
  | _ => exact absurd hF (by simp [LieFamilyUnitaryDiagBig])

end Unitary

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
