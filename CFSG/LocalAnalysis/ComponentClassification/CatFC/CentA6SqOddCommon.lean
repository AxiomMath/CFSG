module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Core
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)

theorem a6sq_lieModel_card_360 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel X τ n p f) (hX : Nat.card X = 360) :
    τ = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2 := by
  obtain ⟨-, hmul, hfac⟩ := hO X τ n p f hadm hm
  have hp := hadm.1
  have hf := hadm.2.1
  rw [hX] at hmul hfac
  have hdvd : p ^ (lieSylowExponent τ n * f) ∣ 360 := by
    rw [← hfac]
    exact Nat.ordProj_dvd 360 p
  rcases lieSylowExponent_ge_three hadm hp2 with ⟨rfl, rfl⟩ | h3
  · refine ⟨rfl, rfl, ?_⟩
    obtain ⟨q, hq⟩ : ∃ q, p ^ f = q := ⟨_, rfl⟩
    simp only [lieOrderDivisor, lieOrderNumerator, Finset.Icc_self, Finset.prod_singleton,
      hq] at hmul
    have hqodd : Odd q := hq ▸ (hp.odd_of_ne_two hp2).pow
    have hg : Nat.gcd 2 (q - 1) = 2 :=
      Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one))
    rw [hg, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at hmul
    obtain ⟨s, hs⟩ : ∃ s, q ^ 2 = s := ⟨_, rfl⟩
    rw [hs] at hmul
    have hsq : s = q * q := by rw [← hs, sq]
    have hq9 : q ≤ 9 := by
      by_contra hlt
      push Not at hlt
      have h1 : 100 ≤ s := by rw [hsq]; nlinarith
      have h2 : 10 * 99 ≤ q * (s - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hq9' : q = 9 := by
      interval_cases q <;> simp_all
    have hp3 : p = 3 := by
      have hpd : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 from rfl, ← hq9', ← hq]
        exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hpd)
    subst hp3
    refine ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) ?_⟩
    change 3 ^ f = 3 ^ 2
    rw [hq, hq9']
  · exfalso
    have h3f : 3 ≤ lieSylowExponent τ n * f := le_trans h3 (Nat.le_mul_of_pos_right _ hf)
    have h27 : p ^ 3 ∣ 360 := (pow_dvd_pow p h3f).trans hdvd
    have hp7 : p ≤ 7 := by
      by_contra hlt
      push Not at hlt
      have h1 : 8 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
      have h2 := Nat.le_of_dvd (by norm_num) h27
      omega
    interval_cases p <;> revert hp hp2 h27 <;> decide

theorem a6sq_lieModel_a6 (hO : LieOrderFormulasInput) {L : Type} [Group L]
    (hA : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)))
    {τ : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (L ⧸ center L) τ n p f) :
    τ = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2 := by
  obtain ⟨eA⟩ := hA
  exact a6sq_lieModel_card_360 hO hadm hp2 hm
    (by rw [Nat.card_congr eA.toEquiv, a6sq_card])

theorem a6sq_range_le_derived {G Q : Type*} [Group G] [Group Q] (φ : Q →* G)
    (hQ : commutator Q = ⊤) : φ.range ≤ commutator G := by
  have h1 : commutator Q = ⁅(⊤ : Subgroup Q), ⊤⁆ := rfl
  have h2 : commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ := rfl
  rw [h1] at hQ
  rw [h2]
  calc φ.range = Subgroup.map φ ⊤ := MonoidHom.range_eq_map φ
    _ = Subgroup.map φ ⁅(⊤ : Subgroup Q), ⊤⁆ := by rw [hQ]
    _ = ⁅Subgroup.map φ ⊤, Subgroup.map φ ⊤⁆ := Subgroup.map_commutator _ _ _
    _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top

theorem a6sq_order_not_dvd (hO : LieOrderFormulasInput) {S : Type} [Group S] {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (hm : LieModel S t n p f)
    (hcase : (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 4) ∨ (t = .PSL ∧ n = 3 ∧ p = 3 ∧ f = 2) ∨
      (t = .PSL ∧ n = 4 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 3 ∧ p = 3 ∧ f = 2) ∨
      (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) ∨ (t = .PSp ∧ n = 2 ∧ p = 3 ∧ f = 1) ∨
      (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨ (t = .POmegaMinus ∧ n = 4 ∧ p = 3 ∧ f = 1))
    (h : 129600 ∣ Nat.card S) : False := by
  obtain ⟨-, hord, -⟩ := hO S t n p f hadm hm
  rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · have h1 : lieOrderNumerator .PSL 2 (3 ^ 4) = 531360 := by decide
    have h2 : lieOrderDivisor .PSL 2 (3 ^ 4) = 2 := by decide
    rw [h1, h2] at hord
    omega
  · have h1 : lieOrderNumerator .PSL 3 (3 ^ 2) = 42456960 := by decide
    have h2 : lieOrderDivisor .PSL 3 (3 ^ 2) = 1 := by decide
    rw [h1, h2] at hord
    omega
  · have h1 : lieOrderNumerator .PSL 4 (3 ^ 1) = 12130560 := by decide
    have h2 : lieOrderDivisor .PSL 4 (3 ^ 1) = 2 := by decide
    rw [h1, h2] at hord
    omega
  · have h1 : lieOrderNumerator .PSU 3 (3 ^ 2) = 42573600 := by decide
    have h2 : lieOrderDivisor .PSU 3 (3 ^ 2) = 1 := by decide
    rw [h1, h2] at hord
    omega
  · have h1 : lieOrderNumerator .PSU 4 (3 ^ 1) = 13063680 := by decide
    have h2 : lieOrderDivisor .PSU 4 (3 ^ 1) = 4 := by decide
    rw [h1, h2] at hord
    omega
  · have h1 : lieOrderNumerator .PSp 2 (3 ^ 1) = 51840 := by decide
    have h2 : lieOrderDivisor .PSp 2 (3 ^ 1) = 2 := by decide
    rw [h1, h2] at hord
    omega
  · have h1 : lieOrderNumerator .POmegaOdd 3 (3 ^ 1) = 9170703360 := by decide
    have h2 : lieOrderDivisor .POmegaOdd 3 (3 ^ 1) = 2 := by decide
    rw [h1, h2] at hord
    omega
  · have h1 : lieOrderNumerator .POmegaMinus 4 (3 ^ 1) = 20303937239040 := by decide
    have h2 : lieOrderDivisor .POmegaMinus 4 (3 ^ 1) = 2 := by decide
    rw [h1, h2] at hord
    omega

end CFSG.ComponentClassification.CatFC
