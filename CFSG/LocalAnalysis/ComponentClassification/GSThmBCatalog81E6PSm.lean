module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PT
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PS

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace P211

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem derivedSeries_three_le_projectiveSL {k : Type*} [Field k] [Finite k] :
    derivedSeries (MulAut (projectiveSL 3 k)) 3 ≤
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
  have hR := (automorphism_generation (K := k) (n := 3) le_rfl).1
  have h := (standard_outer_quotients (K := k) (n := 3)).2.2.2.2.2.2.2.2.2
  rw [hR] at h
  simpa only [derivedSeries_succ, derivedSeries_zero] using h

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem exists_equiv_projectiveSL {G : Type} [Group G] {p f : ℕ}
    (h : Blueprint.LieModel G .PSL 3 p f) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nonempty (G ≃* projectiveSL 3 k) := by
  obtain ⟨-, k, _, _, -, ⟨e⟩⟩ := GH74.statedClassicalModel_of_lieModel (by norm_num) h
  exact ⟨k, inferInstance, inferInstance, ⟨e.trans
    ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 k).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 k).symm))⟩⟩

theorem not_ordA_dvd_aux {q N : ℕ} (hq : Odd q) (hq3 : 3 ≤ q)
    (hN : N = 504 ∨ N = 4080 ∨ N = 29120) (h : Open.ordA 1 (q ^ 2) ∣ N) : False := by
  have hdvd := (sq_dvd_ordA' hq).trans h
  rcases hN with rfl | rfl | rfl
  · have h1 : q ^ 2 ∣ 63 := sq_dvd_of_sq_dvd_two_pow_mul (a := 3) hq (by simpa using hdvd)
    have h2 : q ≤ 7 := by
      have := Nat.le_of_dvd (by norm_num) h1
      nlinarith
    interval_cases q <;> revert h h1 <;> decide
  · have h1 : q ^ 2 ∣ 255 := sq_dvd_of_sq_dvd_two_pow_mul (a := 4) hq (by simpa using hdvd)
    have h2 : q ≤ 15 := by
      have := Nat.le_of_dvd (by norm_num) h1
      nlinarith
    interval_cases q <;> revert h1 <;> decide
  · have h1 : q ^ 2 ∣ 455 := sq_dvd_of_sq_dvd_two_pow_mul (a := 6) hq (by simpa using hdvd)
    have h2 : q ≤ 21 := by
      have := Nat.le_of_dvd (by norm_num) h1
      nlinarith
    interval_cases q <;> revert h1 <;> decide

theorem not_ordA_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {N : ℕ}
    (hN : N = 504 ∨ N = 4080 ∨ N = 29120) (h : Open.ordA 1 (p ^ (2 * f)) ∣ N) : False := by
  rw [show p ^ (2 * f) = (p ^ f) ^ 2 by ring] at h
  exact not_ordA_dvd_aux (hp.odd_of_ne_two hp2).pow
    (le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)) hN h

end P211

open P211

theorem cf81E6P211Small : CF81E6P211Small := by
  intro X _ _ _ hC hfam p f hp hp2 hf a J D _ _ _ _ hJt hJF _ _ _ b K _ hb1 hKC hK hKt
  exfalso
  have hdvd := ordA_dvd_card_fstar hJt hJF
  rcases hfam with h | h | h | h
  · rw [GH74.card_of_lieModel_PSL (by norm_num) h] at hdvd
    exact not_ordA_dvd hp hp2 hf (Or.inl (by decide)) hdvd
  · rw [GH74.card_of_lieModel_PSL (by norm_num) h] at hdvd
    exact not_ordA_dvd hp hp2 hf (Or.inr (Or.inl (by decide))) hdvd
  · obtain ⟨k, _, _, ⟨e⟩⟩ := exists_equiv_projectiveSL h
    have hKF := le_fstar_of_perfect hC e derivedSeries_three_le_projectiveSL
      (commutator_eq_of_isPComp hKC hK)
    refine hb1 (eq_one_of_card_le hC hKF hKC ?_)
    rw [GH74.card_of_lieModel_PSL (by norm_num) h]
    exact le_trans (by decide) (le_card_of_socle hp hp2 hf hKt)
  · rw [GH74.card_of_lieModel_twistedB2 h] at hdvd
    exact not_ordA_dvd hp hp2 hf (Or.inr (Or.inr (by decide))) hdvd

end CFSG.ComponentClassification.GSThmB
