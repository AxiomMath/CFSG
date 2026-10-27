module

public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

private lemma nat_eq_zero_or_eq_of_dvd_of_lt {n m : ℕ} (hn : 0 < n) (hdvd : n ∣ m)
    (hlt : m < 2 * n) : m = 0 ∨ m = n := by
  rcases hdvd with ⟨k, rfl⟩
  have hlt' : n * k < n * 2 := by
    rw [mul_comm 2 n] at hlt
    exact hlt
  have hk : k < 2 := (mul_lt_mul_iff_right₀ hn).mp hlt'
  interval_cases k
  · left; ring
  · right; ring

private lemma zmod_two_eq_zero {n : ℕ} [NeZero n] {i : ZMod (2 * n)} (h : i + i = 0) :
    i = 0 ∨ i = n := by
  haveI : NeZero (2 * n) := ⟨mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  have hn : 0 < n := Nat.pos_of_neZero n
  have hcast : ((2 * i.val : ℕ) : ZMod (2 * n)) = 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ← ZMod.natCast_zmod_val i]
    simpa [two_mul] using h
  have hdvd : 2 * n ∣ 2 * i.val := (ZMod.natCast_eq_zero_iff (2 * i.val) (2 * n)).mp hcast
  have hdvd' : n ∣ i.val :=
    (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp (by simpa using hdvd)
  have hlt : i.val < 2 * n := ZMod.val_lt i
  rcases nat_eq_zero_or_eq_of_dvd_of_lt hn hdvd' hlt with h0 | hn'
  · left; exact (ZMod.val_eq_zero i).mp h0
  · right; rw [← ZMod.natCast_zmod_val i, hn']

theorem z18_quat_unique_invol {n : ℕ} [NeZero n] {x y : QuaternionGroup n}
    (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hna_ne : (n : ZMod (2 * n)) ≠ 0 := by
    intro hna
    have hdvd : 2 * n ∣ n := (ZMod.natCast_eq_zero_iff n (2 * n)).mp hna
    have hle : 2 * n ≤ n := Nat.le_of_dvd (Nat.pos_of_neZero n) hdvd
    have hn : 0 < n := Nat.pos_of_neZero n
    omega
  have hxa_sq_ne : ∀ i : ZMod (2 * n), (QuaternionGroup.xa i) ^ 2 ≠ 1 := by
    intro i h2
    apply hna_ne
    rw [QuaternionGroup.xa_sq] at h2
    have h3 : QuaternionGroup.a (n : ZMod (2 * n)) = QuaternionGroup.a (0 : ZMod (2 * n)) := by
      rw [h2, QuaternionGroup.one_def]
    exact QuaternionGroup.a.inj h3
  have key : ∀ z : QuaternionGroup n, z * z = 1 → z ≠ 1 → z = QuaternionGroup.a n := by
    intro z hz hz1
    rcases z with i | i
    · have hi : i + i = 0 := by
        have h2 : QuaternionGroup.a (i + i) = QuaternionGroup.a (0 : ZMod (2 * n)) := by
          rw [← QuaternionGroup.a_mul_a, hz, QuaternionGroup.one_def]
        exact QuaternionGroup.a.inj h2
      rcases zmod_two_eq_zero hi with h0 | hn'
      · exfalso
        apply hz1
        rw [h0, QuaternionGroup.one_def]
      · rw [hn']
    · exfalso
      exact hxa_sq_ne i (by rw [sq]; exact hz)
  rw [key x hx hx1, key y hy hy1]

theorem z18_sd_not_exp4 {n : ℕ} (hn : 4 ≤ n) :
    ∃ g : CFSG.Open.SemidihedralGroup n, g ^ 4 ≠ 1 := by
  refine ⟨CFSG.Semidihedral.r n, fun h => ?_⟩
  have hdvd : CFSG.Semidihedral.modulus n ∣ 4 := by
    rw [← CFSG.Semidihedral.orderOf_r n (by omega)]
    exact orderOf_dvd_iff_pow_eq_one.mpr h
  rw [CFSG.Semidihedral.modulus] at hdvd
  have hle : 2 ^ (n - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 8 ≤ 2 ^ (n - 1) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem z18_dih_exp {m : ℕ} (h : ∀ g : DihedralGroup (2 ^ m), g ^ 4 = 1) : m ≤ 2 := by
  have h4 : (DihedralGroup.r (1 : ZMod (2 ^ m))) ^ 4 = 1 := h _
  have hdvd : 2 ^ m ∣ 4 := by
    rw [← DihedralGroup.orderOf_r_one (n := 2 ^ m)]
    exact orderOf_dvd_iff_pow_eq_one.mpr h4
  have hle : 2 ^ m ≤ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact Nat.le_of_dvd (by norm_num) hdvd
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hle

theorem z18_d8_check {a b : DihedralGroup 4} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hC : ∀ x : DihedralGroup 4, x * a = a * x → x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    (hconj : ∀ g : DihedralGroup 4, g * a * g⁻¹ ≠ b) :
    (∀ i : ZMod 4, DihedralGroup.r i ≠ a) ∧
      ∀ i : ZMod 4, DihedralGroup.r i * DihedralGroup.r i = 1 →
        DihedralGroup.r i = 1 ∨ DihedralGroup.r i = b := by
  have h : ∀ a b : DihedralGroup 4, a * a = 1 → b * b = 1 → a * b = b * a →
      a ≠ 1 → b ≠ 1 → a ≠ b →
      (∀ x : DihedralGroup 4, x * a = a * x → x = 1 ∨ x = a ∨ x = b ∨ x = a * b) →
      (∀ g : DihedralGroup 4, g * a * g⁻¹ ≠ b) →
      (∀ i : ZMod 4, DihedralGroup.r i ≠ a) ∧
        ∀ i : ZMod 4, DihedralGroup.r i * DihedralGroup.r i = 1 →
          DihedralGroup.r i = 1 ∨ DihedralGroup.r i = b := by
    set_option synthInstance.maxSize 1000 in
    decide +kernel
  exact h a b ha hb hab ha1 hb1 hne hC hconj

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
