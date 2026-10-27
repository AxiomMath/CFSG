module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUniquePair

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Open (ordD ordTwistedD)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)

section Arith

theorem ordD_two_pow {g n : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) :
    ordD n (2 ^ g) = (2 ^ g) ^ (n * (n - 1)) * ((2 ^ g) ^ n - 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ g) ^ (2 * i) - 1) := by
  rw [ordD, Timmesfeld.ClassicalOrders.gcd_four_eq_one
    (Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hg hn), Nat.div_one]

theorem ordTwistedD_two_pow {g n : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) :
    ordTwistedD n (2 ^ g) = (2 ^ g) ^ (n * (n - 1)) * ((2 ^ g) ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ g) ^ (2 * i) - 1) := by
  rw [ordTwistedD, Timmesfeld.ClassicalOrders.gcd_four_eq_one
    (Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hg hn), Nat.div_one]

theorem two_pow_pow_sub_one_ne_zero {g m : ℕ} (hg : 1 ≤ g) (hm : 1 ≤ m) : (2 ^ g) ^ m - 1 ≠ 0 :=
  (Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hg hm).pos.ne'

theorem prod_two_pow_sub_one_ne_zero {g n : ℕ} (hg : 1 ≤ g) :
    ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ g) ^ (2 * i) - 1) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi =>
    two_pow_pow_sub_one_ne_zero hg (by have := (Finset.mem_Icc.1 hi).1; omega)

theorem not_two_dvd_prod {g n : ℕ} (hg : 1 ≤ g) :
    ¬ 2 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ g) ^ (2 * i) - 1) := by
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
  rintro ⟨i, hi, h2⟩
  have := (Finset.mem_Icc.1 hi).1
  exact (Nat.not_even_iff_odd.2 (Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hg
    (by omega : 1 ≤ 2 * i))) (even_iff_two_dvd.2 h2)

theorem factorization_two_ordD {g n : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) :
    (ordD n (2 ^ g)).factorization 2 = g * (n * (n - 1)) := by
  have h0 : (2 ^ g) ^ (n * (n - 1)) * ((2 ^ g) ^ n - 1) ≠ 0 :=
    mul_ne_zero (by positivity) (two_pow_pow_sub_one_ne_zero hg hn)
  rw [ordD_two_pow hg hn, Nat.factorization_mul h0 (prod_two_pow_sub_one_ne_zero hg),
    Nat.factorization_mul (by positivity) (two_pow_pow_sub_one_ne_zero hg hn)]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd (not_two_dvd_prod hg),
    Nat.factorization_eq_zero_of_not_dvd (fun h => Nat.not_even_iff_odd.2
      (Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hg hn) (even_iff_two_dvd.2 h)),
    ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem factorization_two_ordTwistedD {g n : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) :
    (ordTwistedD n (2 ^ g)).factorization 2 = g * (n * (n - 1)) := by
  rw [ordTwistedD_two_pow hg hn,
    Nat.factorization_mul (by positivity) (prod_two_pow_sub_one_ne_zero hg),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd (not_two_dvd_prod hg),
    Nat.factorization_eq_zero_of_not_dvd (fun h => Nat.not_even_iff_odd.2
      (Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hg hn) (even_iff_two_dvd.2 h)),
    ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem three_dvd_four_pow_sub_one (g : ℕ) : 3 ∣ 4 ^ g - 1 := by
  have h : 4 ^ g ≡ 1 ^ g [MOD 3] := Nat.ModEq.pow g (by decide)
  rw [one_pow] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h.symm

theorem not_three_dvd_four_pow (g : ℕ) : ¬ 3 ∣ 4 ^ g := fun h =>
  absurd (Nat.prime_three.dvd_of_dvd_pow h) (by decide)

theorem factorization_three_four_pow_pow_sub_one {g m : ℕ} (hg : 1 ≤ g) (hm : m ≠ 0) :
    ((4 ^ g) ^ m - 1).factorization 3 = (4 ^ g - 1).factorization 3 + m.factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 1 < 4 ^ g := Nat.one_lt_pow (by omega) (by norm_num)
  have hdvd : 3 ∣ 4 ^ g - 1 := three_dvd_four_pow_sub_one g
  have h := padicValNat.pow_sub_pow (p := 3) (by decide) h1 hdvd (not_three_dvd_four_pow g) hm
  rw [one_pow] at h
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.factorization_def _ Nat.prime_three, h]

theorem one_le_factorization_three_four_pow_sub_one {g : ℕ} (hg : 1 ≤ g) :
    1 ≤ (4 ^ g - 1).factorization 3 := by
  have h0 : 4 ^ g - 1 ≠ 0 := by
    have : 1 < 4 ^ g := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hd : 3 ^ 1 ∣ 4 ^ g - 1 := by rw [pow_one]; exact three_dvd_four_pow_sub_one g
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three h0).1 hd

theorem two_pow_pow_two_mul (g i : ℕ) : (2 ^ g) ^ (2 * i) = (4 ^ g) ^ i := by
  rw [pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring_nf

theorem two_pow_two_mul_pow (g m : ℕ) : (2 ^ (2 * g)) ^ m = (4 ^ g) ^ m := by
  rw [pow_mul]
  norm_num

theorem factorization_three_prod {g n : ℕ} (hg : 1 ≤ g) :
    (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ g) ^ (2 * i) - 1)).factorization 3 =
      ∑ i ∈ Finset.Icc 1 (n - 1), ((4 ^ g - 1).factorization 3 + i.factorization 3) := by
  rw [Nat.factorization_prod fun i hi =>
    two_pow_pow_sub_one_ne_zero hg (by have := (Finset.mem_Icc.1 hi).1; omega),
    Finset.sum_apply']
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi1 := (Finset.mem_Icc.1 hi).1
  rw [two_pow_pow_two_mul, factorization_three_four_pow_pow_sub_one hg (by omega)]

theorem factorization_three_prod_sq {g n : ℕ} (hg : 1 ≤ g) :
    (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ (2 * g)) ^ (2 * i) - 1)).factorization 3 =
      ∑ i ∈ Finset.Icc 1 (n - 1), ((4 ^ g - 1).factorization 3 + i.factorization 3) := by
  rw [Nat.factorization_prod fun i hi =>
    two_pow_pow_sub_one_ne_zero (by omega : 1 ≤ 2 * g)
      (by have := (Finset.mem_Icc.1 hi).1; omega), Finset.sum_apply']
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi1 := (Finset.mem_Icc.1 hi).1
  rw [two_pow_two_mul_pow, factorization_three_four_pow_pow_sub_one hg (by omega),
    Nat.factorization_mul (by norm_num) (by omega)]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2), zero_add]

theorem le_factorization_three_ord {g n A : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n)
    (hA : A = ordD n (2 ^ g) ∨ A = ordTwistedD n (2 ^ g)) :
    ∑ i ∈ Finset.Icc 1 (n - 1), ((4 ^ g - 1).factorization 3 + i.factorization 3) ≤
      A.factorization 3 := by
  rcases hA with rfl | rfl
  · rw [ordD_two_pow hg hn]
    have h0 : (2 ^ g) ^ (n * (n - 1)) * ((2 ^ g) ^ n - 1) ≠ 0 :=
      mul_ne_zero (by positivity) (two_pow_pow_sub_one_ne_zero hg hn)
    rw [Nat.factorization_mul h0 (prod_two_pow_sub_one_ne_zero hg)]
    simp only [Finsupp.add_apply]
    rw [factorization_three_prod hg]
    omega
  · rw [ordTwistedD_two_pow hg hn]
    rw [Nat.factorization_mul (by positivity) (prod_two_pow_sub_one_ne_zero hg)]
    simp only [Finsupp.add_apply]
    rw [factorization_three_prod hg]
    omega

theorem factorization_three_ord_sq_le {g n C : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n)
    (hC : C = ordD n (2 ^ (2 * g)) ∨ C = ordTwistedD n (2 ^ (2 * g))) :
    C.factorization 3 ≤
      ∑ i ∈ Finset.Icc 1 (n - 1), ((4 ^ g - 1).factorization 3 + i.factorization 3) +
        ((4 ^ g - 1).factorization 3 + n.factorization 3) := by
  have hg2 : 1 ≤ 2 * g := by omega
  have hpow : ((2 ^ (2 * g)) ^ (n * (n - 1))).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h => by
      have := Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h)
      exact absurd this (by decide)
  rcases hC with rfl | rfl
  · rw [ordD_two_pow hg2 hn]
    have h0 : (2 ^ (2 * g)) ^ (n * (n - 1)) * ((2 ^ (2 * g)) ^ n - 1) ≠ 0 :=
      mul_ne_zero (by positivity) (two_pow_pow_sub_one_ne_zero hg2 hn)
    rw [Nat.factorization_mul h0 (prod_two_pow_sub_one_ne_zero hg2),
      Nat.factorization_mul (by positivity) (two_pow_pow_sub_one_ne_zero hg2 hn)]
    simp only [Finsupp.add_apply]
    rw [factorization_three_prod_sq hg, hpow, two_pow_two_mul_pow,
      factorization_three_four_pow_pow_sub_one hg (by omega)]
    omega
  · rw [ordTwistedD_two_pow hg2 hn]
    rw [Nat.factorization_mul (by positivity) (prod_two_pow_sub_one_ne_zero hg2),
      Nat.factorization_mul (by positivity) (by positivity)]
    simp only [Finsupp.add_apply]
    have hplus : ((2 ^ (2 * g)) ^ n + 1).factorization 3 = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun h => ?_
      rw [two_pow_two_mul_pow] at h
      have h1 := three_dvd_four_pow_sub_one (g * n)
      rw [← pow_mul] at h
      have h2 : 1 ≤ 4 ^ (g * n) := Nat.one_le_pow _ _ (by norm_num)
      have h3 : 3 ∣ (4 ^ (g * n) + 1) - (4 ^ (g * n) - 1) := Nat.dvd_sub h h1
      have h4 : (4 ^ (g * n) + 1) - (4 ^ (g * n) - 1) = 2 := by omega
      rw [h4] at h3
      exact absurd h3 (by decide)
    rw [factorization_three_prod_sq hg, hpow, hplus]
    omega

theorem factorization_three_lt {n : ℕ} (hn : 4 ≤ n) : n.factorization 3 + 2 < n := by
  have hdvd := Nat.ordProj_dvd n 3
  have hle : 3 ^ n.factorization 3 ≤ n := Nat.le_of_dvd (by omega) hdvd
  by_contra hcon
  have h1 : n - 2 ≤ n.factorization 3 := by omega
  have h2 : 3 ^ (n - 2) ≤ n := le_trans (Nat.pow_le_pow_right (by norm_num) h1) hle
  have h3 : ∀ k : ℕ, k + 4 < 3 ^ (k + 2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      omega
  have h4 := h3 (n - 4)
  rw [show n - 4 + 2 = n - 2 by omega, show n - 4 + 4 = n by omega] at h4
  omega

theorem not_mul_dvd_ord_sq {g n A B C : ℕ} (hg : 1 ≤ g) (hn : 4 ≤ n)
    (hA : A = ordD n (2 ^ g) ∨ A = ordTwistedD n (2 ^ g))
    (hB : B = ordD n (2 ^ g) ∨ B = ordTwistedD n (2 ^ g))
    (hC : C = ordD n (2 ^ (2 * g)) ∨ C = ordTwistedD n (2 ^ (2 * g))) : ¬ A * B ∣ C := by
  intro hdvd
  have hg2 : 1 ≤ 2 * g := by omega
  have hA0 : A ≠ 0 := by
    rcases hA with rfl | rfl
    · rw [ordD_two_pow hg (by omega)]
      exact mul_ne_zero (mul_ne_zero (by positivity) (two_pow_pow_sub_one_ne_zero hg (by omega)))
        (prod_two_pow_sub_one_ne_zero hg)
    · rw [ordTwistedD_two_pow hg (by omega)]
      exact mul_ne_zero (by positivity) (prod_two_pow_sub_one_ne_zero hg)
  have hB0 : B ≠ 0 := by
    rcases hB with rfl | rfl
    · rw [ordD_two_pow hg (by omega)]
      exact mul_ne_zero (mul_ne_zero (by positivity) (two_pow_pow_sub_one_ne_zero hg (by omega)))
        (prod_two_pow_sub_one_ne_zero hg)
    · rw [ordTwistedD_two_pow hg (by omega)]
      exact mul_ne_zero (by positivity) (prod_two_pow_sub_one_ne_zero hg)
  have hC0 : C ≠ 0 := by
    rcases hC with rfl | rfl
    · rw [ordD_two_pow hg2 (by omega)]
      exact mul_ne_zero (mul_ne_zero (by positivity) (two_pow_pow_sub_one_ne_zero hg2 (by omega)))
        (prod_two_pow_sub_one_ne_zero hg2)
    · rw [ordTwistedD_two_pow hg2 (by omega)]
      exact mul_ne_zero (by positivity) (prod_two_pow_sub_one_ne_zero hg2)
  have hle := (Nat.factorization_le_iff_dvd (mul_ne_zero hA0 hB0) hC0).2 hdvd 3
  rw [Nat.factorization_mul hA0 hB0] at hle
  simp only [Finsupp.add_apply] at hle
  have h1 := le_factorization_three_ord hg (by omega) hA
  have h2 := le_factorization_three_ord hg (by omega) hB
  have h3 := factorization_three_ord_sq_le hg (by omega) hC
  set a := (4 ^ g - 1).factorization 3 with ha
  have ha1 : 1 ≤ a := one_le_factorization_three_four_pow_sub_one hg
  set S := ∑ i ∈ Finset.Icc 1 (n - 1), (a + i.factorization 3) with hS
  have hS' : (n - 1) * a ≤ S := by
    have : ∑ _i ∈ Finset.Icc 1 (n - 1), a ≤ S := Finset.sum_le_sum fun i _ => Nat.le_add_right _ _
    simpa [Nat.card_Icc] using this
  have h4 := factorization_three_lt hn
  have h5 : (n - 2) * a ≤ n.factorization 3 := by
    have : (n - 1) * a = (n - 2) * a + a := by
      rw [show n - 1 = (n - 2) + 1 by omega, add_mul, one_mul]
    omega
  have h6 : n - 2 ≤ (n - 2) * a := Nat.le_mul_of_pos_right _ ha1
  omega

end Arith

section Exclusion

theorem factorization_two_two_mul_le (M : ℕ) :
    (2 * M).factorization 2 ≤ 1 + M.factorization 2 := by
  by_cases hM : M = 0
  · simp [hM]
  · rw [Nat.factorization_mul two_ne_zero hM]
    simp [Nat.Prime.factorization_self Nat.prime_two]

theorem card_coordinatePlus {K : Type} [Field K] [Finite K] {n f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) :
    Nat.card (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus n K)) =
      ordD n (2 ^ f) :=
  (CFSG.Timmesfeld.card_statedClassicalModel_two (t := .POmegaPlus)
    ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK,
      ⟨(CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K
        (MulEquiv.refl _)).symm⟩⟩).2.2.2.1 rfl

theorem card_coordinateMinus {K : Type} [Field K] [Finite K] {n f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (h1 : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus n K h1 b c)) =
      ordTwistedD n (2 ^ f) :=
  (CFSG.Timmesfeld.card_statedClassicalModel_two (t := .POmegaMinus)
    ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirr,
      ⟨(CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusWitnessEquiv K
        h1 b c (MulEquiv.refl _)).symm⟩⟩).2.2.2.2 rfl

end Exclusion

end CFSG.SeitzReduction.OmegaPilot
