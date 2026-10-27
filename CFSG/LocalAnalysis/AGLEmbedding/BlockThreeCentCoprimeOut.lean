module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem not_dvd_of_dvd_of_five_le {p m k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : k = 6 ∨ k = 8)
    (hm : m ∣ k) : ¬ p ∣ m := fun h => by
  have hk0 : 0 < k := by omega
  have hpk := h.trans hm
  have hle := Nat.le_of_dvd hk0 hpk
  rcases hk with rfl | rfl <;> interval_cases p <;> revert hp hpk <;> decide

theorem not_dvd_card_outer_of_mulEquiv_of_not_dvd {X X' : Type*} [Group X] [Group X']
    (e : X ≃* X') {p : ℕ} (h : ¬ p ∣ Nat.card (Outer X')) : ¬ p ∣ Nat.card (Outer X) := by
  rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]

theorem not_dvd_card_outer_of_centerQuotient {X : Type*} [Group X] [Group.IsPerfect X] {p : ℕ}
    (h : ¬ p ∣ Nat.card (Outer (X ⧸ Subgroup.center X))) : ¬ p ∣ Nat.card (Outer X) :=
  fun hp => h (hp.trans (card_outer_dvd_card_outer_centerQuotient X))

open CFSG.LocalAnalysis.ComponentInitial in
theorem card_outer_dvd_two_of_psl_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL n 2 1) : Nat.card (Outer X) ∣ 2 := by
  obtain ⟨⟨-, -, hn, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn3 : 3 ≤ n := by
    by_contra h3
    exact hn2 (by rw [show n = 2 by omega]; rfl)
  have e' : X ≃* LinearFlag.projectiveSL n K := e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have hdvd := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound Nat.prime_two
    le_rfl hn3 hK
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact hdvd.trans (by simp)

theorem not_dvd_card_outer_of_psl_two_of_five_le {X : Type} [Group X] {n p : ℕ}
    (h : StatedClassicalModel X .PSL n 2 1) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Outer X) :=
  not_dvd_of_dvd_of_five_le hp hp5 (Or.inl rfl) ((card_outer_dvd_two_of_psl_two h).trans
    (by norm_num))

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag in
theorem not_dvd_card_outer_of_psu_prime_of_five_le {X : Type} [Group X] {n p r : ℕ}
    (h : StatedClassicalModel X .PSU n p 1) (hp : p = 2 ∨ p = 3) (hr : r.Prime) (hr5 : 5 ≤ r) :
    ¬ r ∣ Nat.card (Outer X) := by
  obtain ⟨⟨hpp, hf, hn, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p 1 K := ⟨hpp, hf, by rw [hK]; ring⟩
  have hq : ¬(n = 3 ∧ p ^ 1 = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h1 := (UnitaryHigher.unitary_full_diagonal_outer_order hU hn hq).2.2.2.2.1
  have e' : X ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv, h1]
  have hdvd : 2 * 1 * Nat.gcd n (p ^ 1 + 1) ∣ 2 * (p + 1) := by
    rw [mul_one, pow_one]
    exact Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_right _ _)
  rcases hp with rfl | rfl
  · exact not_dvd_of_dvd_of_five_le hr hr5 (Or.inl rfl) hdvd
  · exact not_dvd_of_dvd_of_five_le hr hr5 (Or.inr rfl) hdvd

open CFSG.LocalAnalysis.ComponentInitial in
theorem not_dvd_card_outer_of_psp_two_of_five_le {X : Type} [Group X] {n p : ℕ}
    (h : StatedClassicalModel X .PSp n 2 1) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Outer X) :=
  not_dvd_of_dvd_of_five_le hp hp5 (Or.inl rfl)
    ((symplectic_model_outer_two_part_bound X n 2 1 h).2.1.trans (by norm_num))

open CFSG.LocalAnalysis.ComponentInitial in
theorem card_outer_dvd_two_of_psl_seven {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 7 1) : Nat.card (Outer X) ∣ 2 := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hdvd := (linear_two_outer_order_divisor (p := 7) (f := 1) (by norm_num) F
    (by simpa using hcard)).2 X ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩
  exact hdvd.trans (by norm_num)

theorem not_dvd_card_outer_of_psl_seven_of_five_le {X : Type} [Group X] {p : ℕ}
    (h : StatedClassicalModel X .PSL 2 7 1) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Outer X) :=
  not_dvd_of_dvd_of_five_le hp hp5 (Or.inl rfl) ((card_outer_dvd_two_of_psl_seven h).trans
    (by norm_num))

theorem not_dvd_card_outer_lie_two {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2IndexTwo d.1 ∨ (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q))
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Outer X) := by
  obtain ⟨d, hv⟩ := d
  rcases hd with hd | ⟨q, hq7, hd⟩ | ⟨q, hq3, hd⟩
  · cases d with
    | A r q =>
      change q.card = 2 at hd
      obtain ⟨hp2, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp2, hf] at h
      exact not_dvd_card_outer_of_psl_two_of_five_le h hp hp5
    | twistedA r q =>
      change q.card = 2 at hd
      obtain ⟨hp2, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hp2, hf] at h
      exact not_dvd_card_outer_of_psu_prime_of_five_le h (Or.inl rfl) hp hp5
    | B r q =>
      change q.card = 2 at hd
      obtain ⟨hp2, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
      have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
      by_cases h2 : r = 2
      · subst h2
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rw [hp2, hf] at h
        exact not_dvd_card_outer_of_psp_two_of_five_le h hp hp5
      · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2
          (by omega) e
        rw [hp2, hf] at h
        exact not_dvd_card_outer_of_psp_two_of_five_le h hp hp5
    | C r q => exact hd.elim
    | D r q =>
      exact not_dvd_card_outer_of_mulEquiv_of_not_dvd e
        (kFactOutOrthTwoPrime_holds ⟨.D r q, hv⟩ ⟨r, q, hd, Or.inl rfl⟩ p hp hp5)
    | twistedD r q =>
      exact not_dvd_card_outer_of_mulEquiv_of_not_dvd e
        (kFactOutOrthTwoPrime_holds ⟨.twistedD r q, hv⟩ ⟨r, q, hd, Or.inr (Or.inl rfl)⟩ p hp hp5)
    | G2 q =>
      change q.card = 2 at hd
      have hq3 : 3 ≤ q.card :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      omega
    | _ => exact hd.elim
  · simp only at hd
    subst hd
    obtain ⟨hp7, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq7
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp7, hf] at h
    exact not_dvd_card_outer_of_psl_seven_of_five_le h hp hp5
  · simp only at hd
    subst hd
    obtain ⟨hp3, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq3
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp3, hf] at h
    exact not_dvd_card_outer_of_psu_prime_of_five_le h (Or.inr rfl) hp hp5

theorem not_dvd_card_outer_of_mulEquiv_alternatingGroup {X : Type*} [Group X] {n : ℕ}
    (e : X ≃* alternatingGroup (Fin n)) (hn : 5 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Outer X) :=
  not_dvd_card_outer_of_mulEquiv_of_not_dvd e
    (not_dvd_card_outer_alternatingGroup n hn p hp (by omega))

end CFSG.AGLEmbedding
