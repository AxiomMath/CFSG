module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Arith2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuThm54
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf CFSG.Open

private theorem odd_two_pow_sub_one_aux {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hp : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
  rw [pow_succ]
  exact ⟨2 ^ j - 1, by omega⟩

private theorem odd_two_pow_add_one_aux {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  exact ⟨2 ^ j, by ring⟩

private theorem gcd_two_two_pow_sub_one (m : ℕ) (hm : 1 ≤ m) :
    Nat.gcd 2 (2 ^ m - 1) = 1 :=
  Nat.coprime_two_left.mpr (odd_two_pow_sub_one_aux hm)

private theorem gcd_four_two_pow_sub_one (m : ℕ) (hm : 1 ≤ m) :
    Nat.gcd 4 (2 ^ m - 1) = 1 := by
  have h : Nat.Coprime 2 (2 ^ m - 1) := Nat.coprime_two_left.mpr (odd_two_pow_sub_one_aux hm)
  simpa using h.pow_left 2

private theorem gcd_four_two_pow_add_one (m : ℕ) (hm : 1 ≤ m) :
    Nat.gcd 4 (2 ^ m + 1) = 1 := by
  have h : Nat.Coprime 2 (2 ^ m + 1) := Nat.coprime_two_left.mpr (odd_two_pow_add_one_aux hm)
  simpa using h.pow_left 2

private theorem gcd_five_eq_one_or_five (n : ℕ) :
    Nat.gcd 5 n = 1 ∨ Nat.gcd 5 n = 5 :=
  (Nat.dvd_prime Nat.prime_five).1 (Nat.gcd_dvd_left 5 n)

private theorem prod_Icc_one_two (f : ℕ → ℕ) :
    (∏ i ∈ Finset.Icc 1 2, f i) = f 1 * f 2 := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    Finset.prod_Icc_succ_top (show 1 ≤ (1 : ℕ) + 1 by norm_num)]
  rw [Finset.Icc_self, Finset.prod_singleton]

private theorem prod_Icc_two_four (f : ℕ → ℕ) :
    (∏ i ∈ Finset.Icc 2 4, f i) = (f 2 * f 3) * f 4 := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num,
    Finset.prod_Icc_succ_top (show 2 ≤ (3 : ℕ) + 1 by norm_num)]
  rw [show (3 : ℕ) = 2 + 1 by norm_num,
    Finset.prod_Icc_succ_top (show 2 ≤ (2 : ℕ) + 1 by norm_num)]
  rw [Finset.Icc_self, Finset.prod_singleton]

private theorem prod_Icc_two_five (f : ℕ → ℕ) :
    (∏ i ∈ Finset.Icc 2 5, f i) = ((f 2 * f 3) * f 4) * f 5 := by
  rw [show (5 : ℕ) = 4 + 1 by norm_num,
    Finset.prod_Icc_succ_top (show 2 ≤ (4 : ℕ) + 1 by norm_num)]
  rw [show (4 : ℕ) = 3 + 1 by norm_num,
    Finset.prod_Icc_succ_top (show 2 ≤ (3 : ℕ) + 1 by norm_num)]
  rw [show (3 : ℕ) = 2 + 1 by norm_num,
    Finset.prod_Icc_succ_top (show 2 ≤ (2 : ℕ) + 1 by norm_num)]
  rw [Finset.Icc_self, Finset.prod_singleton]

private theorem toNat_pow_even (x i : ℕ) (hi : Even i) (hx : 1 ≤ x) :
    (((x : ℤ) ^ i) - (-1 : ℤ) ^ i).toNat = x ^ i - 1 := by
  have h1 : 1 ≤ x ^ i := Nat.one_le_pow i x hx
  have hcast : ((x : ℤ) ^ i - (-1 : ℤ) ^ i) = ((x ^ i - 1 : ℕ) : ℤ) := by
    rw [hi.neg_one_pow]; push_cast [h1]; ring
  rw [hcast, Int.toNat_natCast]

private theorem toNat_pow_odd (x i : ℕ) (hi : Odd i) :
    (((x : ℤ) ^ i) - (-1 : ℤ) ^ i).toNat = x ^ i + 1 := by
  have hcast : ((x : ℤ) ^ i - (-1 : ℤ) ^ i) = ((x ^ i + 1 : ℕ) : ℤ) := by
    rw [hi.neg_one_pow]; push_cast; ring
  rw [hcast, Int.toNat_natCast]

private theorem ordBC_two (m : ℕ) (hm : 1 ≤ m) :
    ordBC 2 (2 ^ m) = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := by
  have hg : Nat.gcd 2 (2 ^ m - 1) = 1 := gcd_two_two_pow_sub_one m hm
  unfold ordBC
  rw [hg, Nat.div_one, prod_Icc_one_two]
  rw [show (2 ^ m) ^ (2 * 2) = 2 ^ (4 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ (2 * 1) = 2 ^ (2 * m) by rw [← pow_mul]; congr 1; ring]

private theorem ordTwistedA_three (m : ℕ) (hm : 1 ≤ m) :
    ordTwistedA 3 (2 ^ m) =
      2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))) := by
  have hg : Nat.gcd 4 (2 ^ m + 1) = 1 := gcd_four_two_pow_add_one m hm
  unfold ordTwistedA
  rw [show (3 : ℕ) * (3 + 1) / 2 = 6 by norm_num,
    show (3 : ℕ) + 1 = 4 by norm_num]
  rw [hg, Nat.div_one, prod_Icc_two_four]
  rw [toNat_pow_even (2 ^ m) 2 (by decide) (Nat.one_le_two_pow),
    toNat_pow_odd (2 ^ m) 3 (by decide),
    toNat_pow_even (2 ^ m) 4 (by decide) (Nat.one_le_two_pow)]
  rw [show (2 ^ m) ^ 2 = 2 ^ (2 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 3 = 2 ^ (3 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 4 = 2 ^ (4 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 6 = 2 ^ (6 * m) by rw [← pow_mul]; congr 1; ring]
  ring

private theorem ordA_three (m : ℕ) (hm : 1 ≤ m) :
    ordA 3 (2 ^ m) =
      2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))) := by
  have hg : Nat.gcd 4 (2 ^ m - 1) = 1 := gcd_four_two_pow_sub_one m hm
  unfold ordA
  rw [show (3 : ℕ) * (3 + 1) / 2 = 6 by norm_num,
    show (3 : ℕ) + 1 = 4 by norm_num]
  rw [hg, Nat.div_one, prod_Icc_two_four]
  rw [show (2 ^ m) ^ 2 = 2 ^ (2 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 3 = 2 ^ (3 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 4 = 2 ^ (4 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 6 = 2 ^ (6 * m) by rw [← pow_mul]; congr 1; ring]
  ring

private theorem ordTwistedA_four_mul (m : ℕ) (hm : 1 ≤ m) :
    ordTwistedA 4 (2 ^ m) * Nat.gcd 5 (2 ^ m + 1) =
      2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := by
  have hdvd : Nat.gcd 5 (2 ^ m + 1) ∣
      (2 ^ m) ^ 10 * (∏ i ∈ Finset.Icc 2 5,
        (((2 ^ m : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) := by
    have hgt : (2 ^ m + 1) ∣ (((2 ^ m : ℕ) : ℤ) ^ 5 - (-1 : ℤ) ^ 5).toNat := by
      rw [toNat_pow_odd (2 ^ m) 5 (by decide)]
      simpa using (show Odd 5 by decide).nat_add_dvd_pow_add_pow (2 ^ m) 1
    exact (Nat.gcd_dvd_right 5 (2 ^ m + 1)).trans
      (hgt.trans (dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩))
        ((2 ^ m) ^ 10)))
  unfold ordTwistedA
  rw [show (4 : ℕ) * (4 + 1) / 2 = 10 by norm_num,
    show (4 : ℕ) + 1 = 5 by norm_num]
  rw [Nat.div_mul_cancel hdvd, prod_Icc_two_five]
  rw [toNat_pow_even (2 ^ m) 2 (by decide) (Nat.one_le_two_pow),
    toNat_pow_odd (2 ^ m) 3 (by decide),
    toNat_pow_even (2 ^ m) 4 (by decide) (Nat.one_le_two_pow),
    toNat_pow_odd (2 ^ m) 5 (by decide)]
  rw [show (2 ^ m) ^ 2 = 2 ^ (2 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 3 = 2 ^ (3 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 4 = 2 ^ (4 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 5 = 2 ^ (5 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 10 = 2 ^ (10 * m) by rw [← pow_mul]; congr 1; ring]
  ring

private theorem ordA_four_mul (m : ℕ) (hm : 1 ≤ m) :
    ordA 4 (2 ^ m) * Nat.gcd 5 (2 ^ m - 1) =
      2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := by
  have hdvd : Nat.gcd 5 (2 ^ m - 1) ∣
      (2 ^ m) ^ 10 * (∏ i ∈ Finset.Icc 2 5, ((2 ^ m) ^ i - 1)) := by
    have h5 : (2 ^ m - 1) ∣ (2 ^ m) ^ 5 - 1 := Nat.sub_one_dvd_pow_sub_one (2 ^ m) 5
    exact (Nat.gcd_dvd_right 5 (2 ^ m - 1)).trans
      (h5.trans (dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩))
        ((2 ^ m) ^ 10)))
  unfold ordA
  rw [show (4 : ℕ) * (4 + 1) / 2 = 10 by norm_num,
    show (4 : ℕ) + 1 = 5 by norm_num]
  rw [Nat.div_mul_cancel hdvd, prod_Icc_two_five]
  rw [show (2 ^ m) ^ 2 = 2 ^ (2 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 3 = 2 ^ (3 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 4 = 2 ^ (4 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 5 = 2 ^ (5 * m) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ m) ^ 10 = 2 ^ (10 * m) by rw [← pow_mul]; congr 1; ring]
  ring

theorem thm54OrderLie_of_psp {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    (h : LieModel X .PSp 2 2 m) : Thm54OrderLie (Nat.card X) := by
  have hcard : Nat.card X = ordBC 2 (2 ^ m) :=
    LieModel.card_eq_lieOrd (n := 2) (by norm_num) h
  exact Or.inl ⟨m, hm, by rw [hcard]; exact ordBC_two m (by omega)⟩

theorem thm54OrderLie_of_psu_four {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    (h : LieModel X .PSU 4 2 m) : Thm54OrderLie (Nat.card X) := by
  have hcard : Nat.card X = ordTwistedA 3 (2 ^ m) :=
    LieModel.card_eq_lieOrd (n := 4) (by norm_num) h
  exact Or.inr (Or.inl ⟨m, hm, by rw [hcard]; exact ordTwistedA_three m (by omega)⟩)

theorem thm54OrderLie_of_psl_four {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    (h : LieModel X .PSL 4 2 m) : Thm54OrderLie (Nat.card X) := by
  have hcard : Nat.card X = ordA 3 (2 ^ m) :=
    LieModel.card_eq_lieOrd (n := 4) (by norm_num) h
  exact Or.inr (Or.inr (Or.inl ⟨m, hm, by rw [hcard]; exact ordA_three m (by omega)⟩))

theorem thm54OrderLie_of_psu_five {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    (h : LieModel X .PSU 5 2 m) : Thm54OrderLie (Nat.card X) := by
  have hcard : Nat.card X = ordTwistedA 4 (2 ^ m) :=
    LieModel.card_eq_lieOrd (n := 5) (by norm_num) h
  refine Or.inr (Or.inr (Or.inr (Or.inl
    ⟨m, Nat.gcd 5 (2 ^ m + 1), hm, gcd_five_eq_one_or_five _, ?_⟩)))
  rw [hcard]
  exact ordTwistedA_four_mul m (by omega)

theorem thm54OrderLie_of_psl_five {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    (h : LieModel X .PSL 5 2 m) : Thm54OrderLie (Nat.card X) := by
  have hcard : Nat.card X = ordA 4 (2 ^ m) :=
    LieModel.card_eq_lieOrd (n := 5) (by norm_num) h
  refine Or.inr (Or.inr (Or.inr (Or.inr
    ⟨m, Nat.gcd 5 (2 ^ m - 1), hm, gcd_five_eq_one_or_five _, ?_⟩)))
  rw [hcard]
  exact ordA_four_mul m (by omega)

theorem card_eq_of_suzukiModel (hO : LieOrderFormulasInput) {X : Type} [Group X] {f : ℕ}
    (h : SuzukiModel X 2 f) :
    Nat.card X = 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1)) := by
  have hLie : LieModel X .twistedB2 0 2 f := Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))
  have hadm : StatedLieAdmissible .twistedB2 0 2 f := LieModel.admissible hLie
  obtain ⟨-, hnum, -⟩ := hO X .twistedB2 0 2 f hadm hLie
  simp only [lieOrderDivisor, lieOrderNumerator, mul_one] at hnum
  rw [hnum]
  rw [show (2 ^ f) ^ 2 = 2 ^ (2 * f) by rw [← pow_mul]; congr 1; ring]
  ring

theorem thm54Order_of_types (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : Sol78Thm54Types X) : Thm54Order (Nat.card X) := by
  rcases h with ⟨n, hn, h⟩ | ⟨m, hm, h | h | h | h | h⟩
  · exact Or.inl ⟨2 * n + 1, by omega, ⟨n, rfl⟩, card_eq_of_suzukiModel hO h⟩
  · exact Or.inr (thm54OrderLie_of_psp hm h)
  · exact Or.inr (thm54OrderLie_of_psu_four hm h)
  · exact Or.inr (thm54OrderLie_of_psl_four hm h)
  · exact Or.inr (thm54OrderLie_of_psu_five hm h)
  · exact Or.inr (thm54OrderLie_of_psl_five hm h)

theorem suzukiModel_of_types_of_card_eq (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : Sol78Thm54Types X) (hc : Nat.card X = 29120) : SuzukiModel X 2 3 := by
  rcases h with ⟨n, hn, h⟩ | ⟨m, hm, h | h | h | h | h⟩
  · have hcard := card_eq_of_suzukiModel hO h
    rw [hc] at hcard
    have hf := Thm54Order.sz_eq_29120 (by omega : 3 ≤ 2 * n + 1) hcard.symm
    have : 2 * n + 1 = 3 := hf
    rw [this] at h
    exact h
  · exfalso
    have := Thm54OrderLie.gt (thm54OrderLie_of_psp hm h)
    omega
  · exfalso
    have := Thm54OrderLie.gt (thm54OrderLie_of_psu_four hm h)
    omega
  · exfalso
    have := Thm54OrderLie.gt (thm54OrderLie_of_psl_four hm h)
    omega
  · exfalso
    have := Thm54OrderLie.gt (thm54OrderLie_of_psu_five hm h)
    omega
  · exfalso
    have := Thm54OrderLie.gt (thm54OrderLie_of_psl_five hm h)
    omega

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
