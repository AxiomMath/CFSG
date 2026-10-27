module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

open Subgroup

theorem inv_mul_conj_mem_of_powerMap {Y : Type} [Group Y] {B U : Subgroup Y} {t x : Y}
    (htU : t ∈ normalizer (U : Set Y))
    (hxU : x ∈ normalizer (U : Set Y))
    (hU2 : IsPGroup 2 U) {e j : ℕ} (hte : t ^ 2 ^ e = 1)
    (hj : ∀ b ∈ B, t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U)
    {s r : ℕ} (hs : Odd s) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1)
    (hxB : x ∈ B) (hxr : orderOf x = r) : x⁻¹ * (t * x * t⁻¹) ∈ U := by
  have key : ∀ a y w v : Y, a * (y * w⁻¹) * a⁻¹ * (a * w * a⁻¹ * v⁻¹) = a * y * a⁻¹ * v⁻¹ := by
    intro a y w v; group
  have hiter : ∀ k : ℕ, t ^ k * x * (t ^ k)⁻¹ * (x ^ 2 ^ (j * k))⁻¹ ∈ U := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzB : x ^ 2 ^ (j * k) ∈ B := B.pow_mem hxB _
      have h1 : t * (t ^ k * x * (t ^ k)⁻¹ * (x ^ 2 ^ (j * k))⁻¹) * t⁻¹ ∈ U :=
        (mem_normalizer_iff.mp htU _).mp ih
      have h2 := hj _ hzB
      have hz : x ^ 2 ^ (j * (k + 1)) = (x ^ 2 ^ (j * k)) ^ 2 ^ j := by
        rw [← pow_mul, ← pow_add, mul_add, mul_one]
      have hL : t ^ (k + 1) * x * (t ^ (k + 1))⁻¹ = t * (t ^ k * x * (t ^ k)⁻¹) * t⁻¹ := by
        rw [pow_succ']; group
      rw [hz, hL, ← key t (t ^ k * x * (t ^ k)⁻¹) (x ^ 2 ^ (j * k))]
      exact U.mul_mem h1 h2
  have h0 := hiter (2 ^ e)
  simp only [hte, one_mul, inv_one, mul_one] at h0
  set N := 2 ^ (j * 2 ^ e) with hN
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hs0 : s ≠ 0 := by obtain ⟨k, hk⟩ := hs; omega
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have h2 : 2 ∣ 2 ^ s := dvd_pow_self 2 hs0
    have h3 := Nat.dvd_sub h2 hrs
    rw [Nat.sub_sub_self h1] at h3
    omega
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hw1 : x * (x ^ N)⁻¹ = 1 := by
    obtain ⟨k, hk⟩ := hU2 ⟨_, h0⟩
    have hk' : (x * (x ^ N)⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hzp : x * (x ^ N)⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.zpowers x).mul_mem (Subgroup.mem_zpowers x)
        ((Subgroup.zpowers x).inv_mem ((Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) _))
    have hd1 : orderOf (x * (x ^ N)⁻¹) ∣ r := hxr ▸ orderOf_dvd_of_mem_zpowers hzp
    have hd2 : orderOf (x * (x ^ N)⁻¹) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime r (2 ^ k) := Nat.Coprime.pow_right k hrodd.coprime_two_right
    have h1 : orderOf (x * (x ^ N)⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact orderOf_eq_one_iff.mp h1
  have hxN : x ^ N = x ^ 1 := by rw [pow_one]; exact (mul_inv_eq_one.mp hw1).symm
  have hNmod : N ≡ 1 [MOD r] := hxr ▸ pow_eq_pow_iff_modEq.mp hxN
  have hsmod : 2 ^ s ≡ 1 [MOD r] := ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hrs).symm
  have hZ1 : (2 : ZMod r) ^ (j * 2 ^ e) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hNmod
    push_cast [hN] at this
    exact this
  have hZ2 : (2 : ZMod r) ^ s = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hsmod
    push_cast at this
    exact this
  have hodd : Odd (orderOf (2 : ZMod r)) := hs.of_dvd_nat (orderOf_dvd_of_pow_eq_one hZ2)
  have hdj : orderOf (2 : ZMod r) ∣ j :=
    (Nat.Coprime.pow_right e hodd.coprime_two_right).dvd_of_dvd_mul_right
      (orderOf_dvd_of_pow_eq_one hZ1)
  have hZj : (2 : ZMod r) ^ j = 1 := orderOf_dvd_iff_pow_eq_one.mp hdj
  have hjmod : 2 ^ j ≡ 1 [MOD r] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    exact hZj
  have hxj : x ^ 2 ^ j = x := by
    rw [← pow_one x, ← pow_mul, one_mul]
    exact pow_eq_pow_iff_modEq.mpr (hxr ▸ hjmod)
  have hfin := hj x hxB
  rw [hxj] at hfin
  have hconj := (mem_normalizer_iff.mp (inv_mem hxU) _).mp hfin
  have heq : x⁻¹ * (t * x * t⁻¹ * x⁻¹) * x⁻¹⁻¹ = x⁻¹ * (t * x * t⁻¹) := by group
  rwa [heq] at hconj

end CFSG.GroupTheory
