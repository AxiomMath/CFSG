module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankLin3
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Classify
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossLinearThree
import CFSG.Timmesfeld.Orders.ClassicalLinearThree
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree

public section

namespace CFSG.Blueprint

open CFSG.Open CFSG.SectionRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SectionRank.ClassicalEven (torusDiag torusDiag_mem_SU torusVec prod_torusVec
  torusVec_pow torusVec_one)

variable {X : Type} [Group X]

theorem LieModel.two_le_pRank_psl3_of_dvd [Finite X] {p f r : ℕ} (h : LieModel X .PSL 3 p f)
    (hr : r.Prime) (hrq : r ∣ p ^ f - 1) : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hdvd : r ∣ Nat.card K - 1 := by rw [hK]; exact hrq
  rw [pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_psl3 (F := K) hdvd

theorem LieModel.two_le_pRank_psu3_of_dvd [Finite X] {p f r : ℕ} (h : LieModel X .PSU 3 p f)
    (hr : r.Prime) (hrq : r ∣ p ^ f + 1) : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  have hC := h.statedClassicalModel_of_ne_zero (by norm_num)
  by_cases hr3 : r = 3
  · subst hr3
    exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_three_of_dvd hC hrq
  · obtain ⟨⟨hp, -, -, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := hC
    letI : Field K := hfield
    letI : Finite K := hfinite
    haveI : Fact r.Prime := ⟨hr⟩
    have hq : p ^ f ≠ 0 := (pow_pos hp.pos f).ne'
    have hcard : Nat.card Kˣ = (p ^ f + 1) * (p ^ f - 1) := by
      rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
      (by rw [hcard]; exact hrq.mul_right _)
    have hζq : ζ ^ (p ^ f + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hrq)
    have h0 : torusDiag (torusVec ζ (0 : Fin 3) (2 : Fin 3)) ∈ StatedSU 3 (p ^ f) K :=
      torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one])
    have h1 : torusDiag (torusVec ζ (1 : Fin 3) (2 : Fin 3)) ∈ StatedSU 3 (p ^ f) K :=
      torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one])
    have h2 : 2 ≤ CFSG.Open.pRank r
        (⊤ : Subgroup (StatedProj (StatedSU 3 (p ^ f) K))) :=
      CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_torus (r := r) hr3 hζ
        (i₀ := (0 : Fin 3)) (i₁ := 1) (i₂ := 2) (by decide) (by decide) (by decide) h0 h1
    rw [pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact h2

theorem LieModel.isMulCommutative_sylow_psl3 [Finite X] {p f r : ℕ} (h : LieModel X .PSL 3 p f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) (P : Sylow r X) :
    IsMulCommutative (P : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨hp, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hpK : ¬ r ∣ Nat.card K := by
    rw [hK]
    intro hd
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hd))
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e
    (fun R => CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_statedProj_gl3
      hr hr5 hpK (StatedSL 3 K) R) P

theorem LieModel.isMulCommutative_sylow_psu3 [Finite X] {p f r : ℕ} (h : LieModel X .PSU 3 p f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) (P : Sylow r X) :
    IsMulCommutative (P : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨hp, -, -, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero
    (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hpK : ¬ r ∣ Nat.card K := by
    rw [hK]
    intro hd
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1
      (hr.dvd_of_dvd_pow (hr.dvd_of_dvd_pow hd)))
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e
    (fun R => CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_statedProj_gl3
      hr hr5 hpK (StatedSU 3 (p ^ f) K) R) P

theorem LieModel.card_outer_psl3_dvd {p f : ℕ} (h : LieModel X .PSL 3 p f) :
    Nat.card (Outer X) ∣ 2 * f * Nat.gcd 3 (p ^ f - 1) := by
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
      (p := p) (f := f) (n := 3) hp hf (by norm_num) hK

theorem LieModel.card_outer_psu3 {p f : ℕ} (h : LieModel X .PSU 3 p f) :
    Nat.card (Outer X) = 2 * f * Nat.gcd 3 (p ^ f + 1) := by
  obtain ⟨⟨hp, hf, -, hne⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬ (3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    exact hne (by rw [h2])
  have hout :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU
      (n := 3) (by norm_num) hq
  have e' : X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := 3) (by norm_num)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact hout.2.2.2.2.1

theorem LieModel.not_dvd_card_outer_psl3 {p f r : ℕ} (h : LieModel X .PSL 3 p f) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) : ¬ r ∣ Nat.card (Outer X) := by
  have hout := h.card_outer_psl3_dvd
  have h2 : ¬ r ∣ 2 := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hd
    omega
  have hg : ¬ r ∣ Nat.gcd 3 (p ^ f - 1) := by
    intro hd
    have h3 : r ∣ 3 := hd.trans (Nat.gcd_dvd_left 3 _)
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3
    omega
  intro hd
  have hd' : r ∣ 2 * f * Nat.gcd 3 (p ^ f - 1) := hd.trans hout
  rw [mul_assoc] at hd'
  rcases (hr.dvd_mul).1 hd' with h' | h'
  · exact h2 h'
  · rcases (hr.dvd_mul).1 h' with h' | h'
    · exact hrf h'
    · exact hg h'

theorem LieModel.not_dvd_card_outer_psu3 {p f r : ℕ} (h : LieModel X .PSU 3 p f) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) : ¬ r ∣ Nat.card (Outer X) := by
  have h2 : ¬ r ∣ 2 := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hd
    omega
  have hg : ¬ r ∣ Nat.gcd 3 (p ^ f + 1) := by
    intro hd
    have h3 : r ∣ 3 := hd.trans (Nat.gcd_dvd_left 3 _)
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3
    omega
  intro hd
  rw [h.card_outer_psu3, mul_assoc] at hd
  rcases (hr.dvd_mul).1 hd with h' | h'
  · exact h2 h'
  · rcases (hr.dvd_mul).1 h' with h' | h'
    · exact hrf h'
    · exact hg h'

theorem LieModel.three_thousand_six_hundred_lt_card_psl3 {p f : ℕ} (h : LieModel X .PSL 3 p f)
    (hq : 3 ≤ p ^ f) : 3600 < Nat.card X := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hcard : Nat.card X = Nat.card (StatedProj (StatedSL 3 K)) := Nat.card_congr e.toEquiv
  have hform := CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd (K := K)
  have hqK : 3 ≤ Nat.card K := by rw [hK]; exact hq
  rw [hcard]
  by_cases h3 : Nat.card K = 3
  · rw [h3] at hform
    have hg : Nat.gcd 3 (3 - 1) = 1 := by decide
    rw [hg, mul_one] at hform
    norm_num at hform
    omega
  · have h4 : 4 ≤ Nat.card K := by omega
    have hg : Nat.gcd 3 (Nat.card K - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have h64 : 64 ≤ Nat.card K ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left h4 3
    have h15 : 15 ≤ Nat.card K ^ 2 - 1 := by
      have h : 16 ≤ Nat.card K ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left h4 2
      omega
    have h63 : 63 ≤ Nat.card K ^ 3 - 1 := by omega
    have hA : 60480 ≤ Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
      calc 60480 = 64 * (15 * 63) := by norm_num
        _ ≤ Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
          Nat.mul_le_mul h64 (Nat.mul_le_mul h15 h63)
    nlinarith

theorem LieModel.three_thousand_six_hundred_lt_card_psu3 {p f : ℕ} (h : LieModel X .PSU 3 p f)
    (hq : 3 ≤ p ^ f) : 3600 < Nat.card X := by
  obtain ⟨⟨hp, hf, -, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hcard : Nat.card X = Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) :=
    Nat.card_congr e.toEquiv
  have hform := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd (K := K) hp hf hK
  rw [hcard]
  by_cases h3 : p ^ f = 3
  · rw [h3] at hform ⊢
    have hg : Nat.gcd 3 (3 + 1) = 1 := by decide
    rw [hg, mul_one] at hform
    norm_num at hform
    omega
  · have h4 : 4 ≤ p ^ f := by omega
    have hg : Nat.gcd 3 (p ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have h64 : 64 ≤ (p ^ f) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left h4 3
    have h15 : 15 ≤ (p ^ f) ^ 2 - 1 := by
      have h : 16 ≤ (p ^ f) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left h4 2
      omega
    have h65 : 65 ≤ (p ^ f) ^ 3 + 1 := by omega
    have hA : 62400 ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
      calc 62400 = 64 * (15 * 65) := by norm_num
        _ ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
          Nat.mul_le_mul h64 (Nat.mul_le_mul h15 h65)
    nlinarith

end CFSG.Blueprint
