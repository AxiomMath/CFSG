module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem exists_conj_of_inv_odd {G : Type*} [Group G] {a b o : G} (hb2 : b * b = 1)
    (ha2 : a * a = 1) (hao : a = b * o) (hodd : Odd (orderOf o)) :
    ∃ h : G, a = h * b * h⁻¹ := by
  obtain ⟨k, hk⟩ := hodd
  have ha2' : b * o * (b * o) = 1 := by rw [← hao]; exact ha2
  have hbob : b * o * b = o⁻¹ :=
    eq_inv_of_mul_eq_one_left ((mul_assoc (b * o) b o).trans ha2')
  have hob : o * b = b * o⁻¹ := by
    calc o * b = b * b * o * b := by rw [hb2, one_mul]
      _ = b * (b * o * b) := by simp only [mul_assoc]
      _ = b * o⁻¹ := by rw [hbob]
  have hconj : ∀ n : ℕ, o ^ n * b = b * o⁻¹ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc o ^ (n + 1) * b = o * (o ^ n * b) := by rw [pow_succ', mul_assoc]
        _ = o * (b * o⁻¹ ^ n) := by rw [ih]
        _ = o * b * o⁻¹ ^ n := by rw [mul_assoc]
        _ = b * o⁻¹ * o⁻¹ ^ n := by rw [hob]
        _ = b * o⁻¹ ^ (n + 1) := by rw [pow_succ', mul_assoc]
  have hkk : k + k + 1 = orderOf o := by omega
  have hpow : o ^ (k + k + 1) = 1 := by rw [hkk]; exact pow_orderOf_eq_one o
  have hinv : o ^ (k + k) = o⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hpow)
  refine ⟨o ^ k, ?_⟩
  calc a = b * o := hao
    _ = b * o⁻¹ ^ (k + k) := by rw [inv_pow, hinv, inv_inv]
    _ = b * o⁻¹ ^ k * o⁻¹ ^ k := by rw [mul_assoc, ← pow_add]
    _ = o ^ k * b * (o ^ k)⁻¹ := by rw [hconj k, inv_pow]

theorem pow_conj_of_order8 {G : Type*} [Group G] {z s₀ : G} (hzs : z * s₀ * z⁻¹ = s₀⁻¹)
    (k : ℕ) : z * s₀ ^ k * z⁻¹ = (s₀ ^ k)⁻¹ := by
  rw [← conj_pow, hzs, inv_pow]

theorem conj_pow_of_conj {G : Type*} [Group G] {σ s₀ : G} {j : ℕ} (h : σ * s₀ * σ⁻¹ = s₀ ^ j)
    (k : ℕ) : σ * s₀ ^ k * σ⁻¹ = (s₀ ^ k) ^ j := by
  rw [← conj_pow, h, pow_right_comm]

theorem order8_in_dihedral {G : Type*} [Group G] {S : Subgroup G} {z s₀ s : G} (hz2 : z * z = 1)
    (hzs : z * s₀ * z⁻¹ = s₀⁻¹) (h8 : orderOf s₀ = 8)
    (hgen : ∀ y ∈ S, ∃ i j : ℕ, y = s₀ ^ i * z ^ j) (hs : s ∈ S) (hso : orderOf s = 8) :
    ∃ k : ℕ, Odd k ∧ s = s₀ ^ k := by
  obtain ⟨i, j, hij⟩ := hgen s hs
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hs8 : s₀ ^ 8 = 1 := by rw [← h8]; exact pow_orderOf_eq_one s₀
  have hz2m : ∀ m : ℕ, z ^ (2 * m) = 1 := by
    intro m
    rw [pow_mul, pow_two, hz2, one_pow]
  have hconjs : z * s₀ ^ i * z = (s₀ ^ i)⁻¹ := by
    have h := pow_conj_of_order8 hzs i
    rwa [hzinv] at h
  rcases Nat.even_or_odd' j with ⟨m, hm | hm⟩
  ·
    have hsi : s = s₀ ^ i := by rw [hij, hm, hz2m, mul_one]
    refine ⟨i, ?_, hsi⟩
    rcases Nat.even_or_odd i with ⟨n, hn⟩ | ho
    ·
      exfalso
      have h4 : s ^ 4 = 1 := by
        rw [hsi, ← pow_mul, show i * 4 = 8 * n by omega, pow_mul, hs8, one_pow]
      have hd := orderOf_dvd_of_pow_eq_one h4
      rw [hso] at hd
      omega
    · exact ho
  ·
    exfalso
    have hzj : z ^ j = z := by rw [hm, pow_succ, hz2m, one_mul]
    have hss : s * s = 1 := by
      rw [hij, hzj]
      calc s₀ ^ i * z * (s₀ ^ i * z) = s₀ ^ i * (z * s₀ ^ i * z) := by simp only [mul_assoc]
        _ = s₀ ^ i * (s₀ ^ i)⁻¹ := by rw [hconjs]
        _ = 1 := mul_inv_cancel _
    have h2 : s ^ 2 = 1 := by rw [pow_two]; exact hss
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hso] at hd
    omega

end CFSG.EvenSporadicStandard.Fin76b
