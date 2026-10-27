module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Asc77.C25H

theorem zpow_eq_one_or_self {G : Type*} [Group G] {z : G} (hz : z * z = 1) (b : ℤ) :
    z ^ b = 1 ∨ z ^ b = z := by
  obtain ⟨c, rfl | rfl⟩ := Int.even_or_odd' b
  · left
    rw [zpow_mul, zpow_two, hz, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hz, one_zpow, one_mul, zpow_one]

theorem exists_conj_mul_of_inverted {G : Type*} [Group G] [Finite G] {t z m : G} (ht : t * t = 1)
    (hz : z * z = 1) (htm : t * m * t = m⁻¹)
    (h2 : ∀ (i : ℕ) (y : G), y ∈ Subgroup.zpowers m → orderOf y = 2 ^ i → y = 1 ∨ y = z) :
    ∃ (g : G) (ε : ℕ), g ∈ Subgroup.zpowers m ∧ ε ≤ 1 ∧ g * (t * z ^ ε) * g⁻¹ = t * m := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htpow : ∀ j : ℤ, t * m ^ j * t = m ^ (-j) := by
    intro j
    have h1 := map_zpow (MulAut.conj t) m j
    simp only [MulAut.conj_apply, hti, htm] at h1
    rw [h1, inv_zpow']
  have hinv : ∀ x ∈ Subgroup.zpowers m, t * x * t = x⁻¹ := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [htpow, zpow_neg]
  have hcomm : ∀ x ∈ Subgroup.zpowers m, ∀ y ∈ Subgroup.zpowers m, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self m i j).eq
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  have hcop : Nat.Coprime (2 ^ k) o := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ho)
  obtain ⟨α, β, hαβ⟩ : ∃ α β : ℤ, α * ((2 ^ k : ℕ) : ℤ) + β * (o : ℤ) = 1 := by
    refine ⟨Nat.gcdA (2 ^ k) o, Nat.gcdB (2 ^ k) o, ?_⟩
    have h1 := Nat.gcd_eq_gcd_ab (2 ^ k) o
    rw [hcop.gcd_eq_one, Nat.cast_one] at h1
    rw [mul_comm (Nat.gcdA (2 ^ k) o), mul_comm (Nat.gcdB (2 ^ k) o)]
    exact h1.symm
  have hmo : orderOf (m ^ o) = 2 ^ k := by
    have h1 : o ∣ orderOf m := ⟨2 ^ k, by rw [hko, mul_comm]⟩
    rw [orderOf_pow_of_dvd ho.pos.ne' h1, hko, Nat.mul_div_cancel _ ho.pos]
  have hw1 : m ^ o = 1 ∨ m ^ o = z :=
    h2 k (m ^ o) (Subgroup.pow_mem _ (Subgroup.mem_zpowers m) o) hmo
  set o' : G := m ^ (α * ((2 ^ k : ℕ) : ℤ)) with ho'
  set w : G := m ^ (β * (o : ℤ)) with hw'
  have hmow : m = o' * w := by
    calc m = m ^ (1 : ℤ) := (zpow_one m).symm
      _ = m ^ (α * ((2 ^ k : ℕ) : ℤ) + β * (o : ℤ)) := by rw [hαβ]
      _ = o' * w := zpow_add m _ _
  have hwz : w = 1 ∨ w = z := by
    have e : w = (m ^ o) ^ β := by
      rw [hw', mul_comm, zpow_mul, zpow_natCast]
    rw [e]
    rcases hw1 with h | h
    · left
      rw [h, one_zpow]
    · rw [h]
      exact zpow_eq_one_or_self hz β
  obtain ⟨ε, hε1, hεw⟩ : ∃ ε : ℕ, ε ≤ 1 ∧ z ^ ε = w := by
    rcases hwz with h | h
    · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
    · exact ⟨1, le_rfl, by rw [h, pow_one]⟩
  have ho'm : o' ∈ Subgroup.zpowers m := Subgroup.zpow_mem _ (Subgroup.mem_zpowers m) _
  have hwm : w ∈ Subgroup.zpowers m := Subgroup.zpow_mem _ (Subgroup.mem_zpowers m) _
  have ho'o : o' ^ o = 1 := by
    have h1 : o' ^ o = (m ^ (2 ^ k * o)) ^ α := by
      rw [ho', ← zpow_natCast, ← zpow_mul, ← zpow_natCast m (2 ^ k * o), ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [h1, ← hko, pow_orderOf_eq_one, one_zpow]
  obtain ⟨c, hc⟩ := ho
  set v : G := o' ^ (c + 1) with hv
  have hvm : v ∈ Subgroup.zpowers m := Subgroup.pow_mem _ ho'm _
  have hvv : v * v = o' := by
    have h1 : v * v = o' ^ (o + 1) := by
      rw [hv, ← pow_add]
      congr 1
      omega
    rw [h1, pow_succ, ho'o, one_mul]
  have hvt : v⁻¹ * t = t * v := by
    have h1 : t * v * t = v⁻¹ := hinv v hvm
    calc v⁻¹ * t = (t * v * t) * t := by rw [h1]
      _ = t * v * (t * t) := by rw [mul_assoc]
      _ = t * v := by rw [ht, mul_one]
  refine ⟨v⁻¹, ε, Subgroup.inv_mem _ hvm, hε1, ?_⟩
  rw [inv_inv, hεw]
  calc v⁻¹ * (t * w) * v = (v⁻¹ * t) * (w * v) := by simp only [mul_assoc]
    _ = (t * v) * (v * w) := by rw [hvt, hcomm w hwm v hvm]
    _ = t * (v * v) * w := by simp only [mul_assoc]
    _ = t * o' * w := by rw [hvv]
    _ = t * (o' * w) := by rw [mul_assoc]
    _ = t * m := by rw [← hmow]

end CFSG.ClassicalInvolution.Asc77.C25H
