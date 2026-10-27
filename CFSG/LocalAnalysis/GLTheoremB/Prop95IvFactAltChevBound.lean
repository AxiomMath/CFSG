module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersRee
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

theorem two_mul_tri (r : ℕ) : 2 * (r * (r + 1) / 2) = r * (r + 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self r)

theorem sum_Icc_two_mul (r : ℕ) : 2 * ∑ i ∈ Finset.Icc 2 (r + 1), i = r * (r + 3) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ r + 1 + 1), mul_add, ih]
    ring

theorem sum_Icc_eq (r : ℕ) : ∑ i ∈ Finset.Icc 2 (r + 1), i = r * (r + 1) / 2 + r := by
  have h1 := sum_Icc_two_mul r
  have h2 := two_mul_tri r
  have h3 : r * (r + 3) = r * (r + 1) + 2 * r := by ring
  omega

theorem sub_one_le_pow (q k : ℕ) : q ^ k - 1 ≤ q ^ k := Nat.sub_le _ _

theorem add_one_le_pow_succ {q : ℕ} (hq : 2 ≤ q) (k : ℕ) : q ^ k + 1 ≤ q ^ (k + 1) := by
  rw [pow_succ]
  have := Nat.one_le_pow k q (by omega)
  nlinarith

theorem card_Icc_two_succ (r : ℕ) : (Finset.Icc 2 (r + 1)).card = r := by
  rw [Nat.card_Icc]
  omega

theorem card_Icc_one (n : ℕ) : (Finset.Icc 1 n).card = n := by
  rw [Nat.card_Icc]
  omega

theorem two_pow_pow (f c N : ℕ) : (2 ^ f) ^ (c * N) = 2 ^ (c * (f * N)) := by
  rw [← pow_mul]
  congr 1
  ring

theorem toNat_le_two_mul (q i : ℕ) (hq : 1 ≤ q) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat ≤ 2 * q ^ i := by
  have hq1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hq)
  apply Int.toNat_le.mpr
  have hq2 : ((2 * q ^ i : ℕ) : ℤ) = 2 * (q : ℤ) ^ i := by push_cast; ring
  rw [hq2]
  rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> linarith

theorem toNat_le_of_even (q i : ℕ) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat ≤ q ^ i := by
  rw [hi.neg_one_pow]
  apply Int.toNat_le.mpr
  push_cast
  have : (0 : ℤ) ≤ (q : ℤ) ^ i := by positivity
  linarith

theorem prod_twistedA_le (q r : ℕ) (hq : 1 ≤ q) :
    ∏ i ∈ Finset.Icc 2 (r + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat ≤
      2 ^ r * q ^ (∑ i ∈ Finset.Icc 2 (r + 1), i) := by
  have h := Finset.prod_le_prod (s := Finset.Icc 2 (r + 1))
    (f := fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) (g := fun i => 2 * q ^ i)
    (fun i _ => toNat_le_two_mul q i hq)
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_Icc_two_succ,
    Finset.prod_pow_eq_pow_sum] at h
  exact h

theorem ordA_le {r q : ℕ} (hr : 1 ≤ r) (hq : 1 ≤ q) :
    ordA r q ≤ q ^ (3 * (r * (r + 1) / 2)) := by
  unfold ordA
  refine (Nat.div_le_self _ _).trans ?_
  have hP : ∏ i ∈ Finset.Icc 2 (r + 1), (q ^ i - 1) ≤ (q ^ (r + 1)) ^ r := by
    have h := Finset.prod_le_pow_card (Finset.Icc 2 (r + 1)) (fun i => q ^ i - 1)
      (q ^ (r + 1)) (fun i hi => by
        rw [Finset.mem_Icc] at hi
        exact (sub_one_le_pow q i).trans (Nat.pow_le_pow_right hq hi.2))
    rwa [card_Icc_two_succ] at h
  have h2 := two_mul_tri r
  calc q ^ (r * (r + 1) / 2) * ∏ i ∈ Finset.Icc 2 (r + 1), (q ^ i - 1)
      ≤ q ^ (r * (r + 1) / 2) * (q ^ (r + 1)) ^ r := Nat.mul_le_mul_left _ hP
    _ = q ^ (r * (r + 1) / 2 + r * (r + 1)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        rw [mul_comm (r + 1) r]
    _ ≤ q ^ (3 * (r * (r + 1) / 2)) := Nat.pow_le_pow_right hq (by omega)

theorem ordTwistedA_le_three {r q : ℕ} (hr : 3 ≤ r) (hq : 2 ≤ q) :
    ordTwistedA r q ≤ q ^ (3 * (r * (r + 1) / 2)) := by
  unfold ordTwistedA
  refine (Nat.div_le_self _ _).trans ?_
  have hP := prod_twistedA_le q r (by omega)
  rw [sum_Icc_eq r] at hP
  have h2N := two_mul_tri r
  have h4 : 4 * r ≤ r * (r + 1) := by nlinarith
  have hrN : 2 * r ≤ r * (r + 1) / 2 := by omega
  have hpow : 2 ^ r ≤ q ^ r := Nat.pow_le_pow_left hq r
  set N := r * (r + 1) / 2 with hNdef
  have hP' : ∏ i ∈ Finset.Icc 2 (r + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat ≤
      q ^ (N + 2 * r) := by
    calc _ ≤ 2 ^ r * q ^ (N + r) := hP
      _ ≤ q ^ r * q ^ (N + r) := Nat.mul_le_mul_right _ hpow
      _ = q ^ (N + 2 * r) := by rw [← pow_add]; congr 1; ring
  calc q ^ N * ∏ i ∈ Finset.Icc 2 (r + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat
      ≤ q ^ N * q ^ (N + 2 * r) := Nat.mul_le_mul_left _ hP'
    _ = q ^ (2 * N + 2 * r) := by rw [← pow_add]; congr 1; ring
    _ ≤ q ^ (3 * N) := Nat.pow_le_pow_right (by omega) (by omega)

theorem ordTwistedA_two {q : ℕ} (hq : 2 ≤ q) : ordTwistedA 2 q ≤ q ^ (3 * (2 * (2 + 1) / 2)) := by
  unfold ordTwistedA
  refine (Nat.div_le_self _ _).trans ?_
  have hI : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  have h2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat ≤ q ^ 2 := toNat_le_of_even q 2 (by decide)
  have h3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat ≤ 2 * q ^ 3 := toNat_le_two_mul q 3 (by omega)
  calc q ^ (2 * (2 + 1) / 2) * (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat *
        ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat)
      ≤ q ^ (2 * (2 + 1) / 2) * (q ^ 2 * (2 * q ^ 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3)
    _ = 2 * q ^ 8 := by ring
    _ ≤ q ^ 9 := by
        calc 2 * q ^ 8 ≤ q * q ^ 8 := Nat.mul_le_mul_right _ hq
          _ = q ^ 9 := by ring
    _ = q ^ (3 * (2 * (2 + 1) / 2)) := by norm_num

theorem ordBC_le {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    ordBC n q ≤ q ^ (3 * (n * n)) := by
  unfold ordBC
  refine (Nat.div_le_self _ _).trans ?_
  have hP : ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) ≤ (q ^ (2 * n)) ^ n := by
    have h := Finset.prod_le_pow_card (Finset.Icc 1 n) (fun i => q ^ (2 * i) - 1)
      (q ^ (2 * n)) (fun i hi => by
        rw [Finset.mem_Icc] at hi
        exact (sub_one_le_pow q (2 * i)).trans (Nat.pow_le_pow_right hq (by omega)))
    rwa [card_Icc_one] at h
  calc q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
      ≤ q ^ (n * n) * (q ^ (2 * n)) ^ n := Nat.mul_le_mul_left _ hP
    _ = q ^ (3 * (n * n)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

theorem ordD_le {n q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q) :
    ordD n q ≤ q ^ (3 * (n * (n - 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold ordD
  simp only [Nat.add_sub_cancel]
  refine (Nat.div_le_self _ _).trans ?_
  have hP : ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ (q ^ (2 * m)) ^ m := by
    have h := Finset.prod_le_pow_card (Finset.Icc 1 m) (fun i => q ^ (2 * i) - 1)
      (q ^ (2 * m)) (fun i hi => by
        rw [Finset.mem_Icc] at hi
        exact (sub_one_le_pow q (2 * i)).trans (Nat.pow_le_pow_right hq (by omega)))
    rwa [card_Icc_one] at h
  have hA : q ^ (m + 1) - 1 ≤ q ^ (m + 1) := sub_one_le_pow q (m + 1)
  have hexp : (m + 1) * m + (m + 1) + 2 * m * m ≤ 3 * ((m + 1) * m) := by nlinarith
  calc q ^ ((m + 1) * m) * (q ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1)
      ≤ q ^ ((m + 1) * m) * q ^ (m + 1) * (q ^ (2 * m)) ^ m :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hA) hP
    _ = q ^ ((m + 1) * m + (m + 1) + 2 * m * m) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ q ^ (3 * ((m + 1) * m)) := Nat.pow_le_pow_right (by omega) hexp

theorem ordTwistedD_le {n q : ℕ} (hn : 4 ≤ n) (hq : 2 ≤ q) :
    ordTwistedD n q ≤ q ^ (3 * (n * (n - 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold ordTwistedD
  simp only [Nat.add_sub_cancel]
  refine (Nat.div_le_self _ _).trans ?_
  have hP : ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ (q ^ (2 * m)) ^ m := by
    have h := Finset.prod_le_pow_card (Finset.Icc 1 m) (fun i => q ^ (2 * i) - 1)
      (q ^ (2 * m)) (fun i hi => by
        rw [Finset.mem_Icc] at hi
        exact (sub_one_le_pow q (2 * i)).trans (Nat.pow_le_pow_right (by omega) (by omega)))
    rwa [card_Icc_one] at h
  have hA : q ^ (m + 1) + 1 ≤ q ^ (m + 1 + 1) := add_one_le_pow_succ hq (m + 1)
  have hexp : (m + 1) * m + (m + 1 + 1) + 2 * m * m ≤ 3 * ((m + 1) * m) := by nlinarith
  calc q ^ ((m + 1) * m) * (q ^ (m + 1) + 1) * ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1)
      ≤ q ^ ((m + 1) * m) * q ^ (m + 1 + 1) * (q ^ (2 * m)) ^ m :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hA) hP
    _ = q ^ ((m + 1) * m + (m + 1 + 1) + 2 * m * m) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ q ^ (3 * ((m + 1) * m)) := Nat.pow_le_pow_right (by omega) hexp

theorem ordE6_le {q : ℕ} (hq : 1 ≤ q) : ordE6 q ≤ q ^ (3 * 36) := by
  unfold ordE6
  refine (Nat.div_le_self _ _).trans ?_
  calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)
      ≤ q ^ 36 * q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 := by
        gcongr <;> exact sub_one_le_pow _ _
    _ = q ^ 78 := by ring
    _ ≤ q ^ (3 * 36) := Nat.pow_le_pow_right hq (by norm_num)

theorem ordTwistedE6_le {q : ℕ} (hq : 2 ≤ q) : ordTwistedE6 q ≤ q ^ (3 * 36) := by
  unfold ordTwistedE6
  refine (Nat.div_le_self _ _).trans ?_
  calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
      ≤ q ^ 36 * q ^ 12 * q ^ (9 + 1) * q ^ 8 * q ^ 6 * q ^ (5 + 1) * q ^ 2 := by
        gcongr <;> first | exact Nat.sub_le _ _ | exact add_one_le_pow_succ hq _
    _ = q ^ 80 := by ring
    _ ≤ q ^ (3 * 36) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem ordE7_le {q : ℕ} (hq : 1 ≤ q) : ordE7 q ≤ q ^ (3 * 63) := by
  unfold ordE7
  refine (Nat.div_le_self _ _).trans ?_
  calc q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 63 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact sub_one_le_pow _ _
    _ = q ^ 133 := by ring
    _ ≤ q ^ (3 * 63) := Nat.pow_le_pow_right hq (by norm_num)

theorem ordE8_le {q : ℕ} (hq : 1 ≤ q) : ordE8 q ≤ q ^ (3 * 120) := by
  unfold ordE8
  calc q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
        (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
      ≤ q ^ 120 * q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 := by
        gcongr <;> exact sub_one_le_pow _ _
    _ = q ^ 248 := by ring
    _ ≤ q ^ (3 * 120) := Nat.pow_le_pow_right hq (by norm_num)

theorem ordF4_le {q : ℕ} (hq : 1 ≤ q) : ordF4 q ≤ q ^ (3 * 24) := by
  unfold ordF4
  calc q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 24 * q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact sub_one_le_pow _ _
    _ = q ^ 52 := by ring
    _ ≤ q ^ (3 * 24) := Nat.pow_le_pow_right hq (by norm_num)

theorem ordG2_le {q : ℕ} (hq : 1 ≤ q) : ordG2 q ≤ q ^ (3 * 6) := by
  unfold ordG2
  calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact sub_one_le_pow _ _
    _ = q ^ 14 := by ring
    _ ≤ q ^ (3 * 6) := Nat.pow_le_pow_right hq (by norm_num)

theorem ordTrialityD4_le {q : ℕ} (hq : 2 ≤ q) : ordTrialityD4 q ≤ q ^ (3 * 12) := by
  unfold ordTrialityD4
  have h9 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
    have h1 : q ^ 4 + 1 ≤ q ^ 8 := by
      have : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have : 2 ≤ q ^ 4 := by
        calc 2 ≤ q := hq
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      nlinarith
    have h2 : q ^ 9 = q * q ^ 8 := by ring
    rw [h2]
    nlinarith [Nat.mul_le_mul_right (q ^ 8) hq, h1]
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * q ^ 9 * q ^ 6 * q ^ 2 := by
        gcongr <;> first | exact h9 | exact Nat.sub_le _ _
    _ = q ^ 29 := by ring
    _ ≤ q ^ (3 * 12) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem ordSuzuki_le {q : ℕ} (hq : 2 ≤ q) : ordSuzuki q ≤ q ^ (3 * 2) := by
  unfold ordSuzuki
  have h3 : q ^ 2 + 1 ≤ q ^ 3 := by
    have : q ^ 3 = q * q ^ 2 := by ring
    rw [this]
    nlinarith
  calc q ^ 2 * (q ^ 2 + 1) * (q - 1) ≤ q ^ 2 * q ^ 3 * q := by
        gcongr <;> first | exact h3 | exact Nat.sub_le _ _
    _ = q ^ 6 := by ring
    _ ≤ q ^ (3 * 2) := le_rfl

theorem ordTwistedF4_le {q : ℕ} (hq : 2 ≤ q) : ordTwistedF4 q ≤ q ^ (3 * 12) := by
  unfold ordTwistedF4
  have h7 : q ^ 6 + 1 ≤ q ^ 7 := add_one_le_pow_succ hq 6
  have h4 : q ^ 3 + 1 ≤ q ^ 4 := add_one_le_pow_succ hq 3
  calc q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
      ≤ q ^ 12 * q ^ 7 * q ^ 4 * q ^ 4 * q := by
        gcongr <;> first | exact h7 | exact h4 | exact Nat.sub_le _ _
    _ = q ^ 28 := by ring
    _ ≤ q ^ (3 * 12) := Nat.pow_le_pow_right (by omega) (by norm_num)

end CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact
