module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem exists_index_two_involutions_central_of_quaternion_pair
    {T : Type*} [Group T] [Finite T] (hcard : Nat.card T = 16)
    {z a b : T} (hz : z ∈ center T) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (ha : a * a = z) (hb : b * b = z) (hba : b * a * b⁻¹ = z * a)
    (hnorm : ∀ g : T, g * a * g⁻¹ = a ∨ g * a * g⁻¹ = z * a) :
    ∃ M : Subgroup T, M.index = 2 ∧ ∀ u ∈ M, u * u = 1 → u ∈ center T := by
  have ha2 : a ^ 2 = z := by rw [pow_two, ha]
  have hb2 : b ^ 2 = z := by rw [pow_two, hb]
  have hzsq : z ^ 2 = 1 := by rw [pow_two, hz2]
  have hapow2 : a ^ (2 : ℤ) = z := by
    rw [show (2 : ℤ) = (2 : ℕ) by norm_num, zpow_natCast, ha2]
  have hazpow2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = (2 : ℕ) by norm_num, zpow_natCast, hzsq]
  have ha4 : a ^ 4 = 1 := by
    calc a ^ 4 = (a ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = z ^ 2 := by rw [ha2]
      _ = 1 := hzsq
  have ha_ne_one : a ≠ 1 := by
    intro h
    rw [h, mul_one] at ha
    exact hz1 ha.symm
  have ha2_ne_one : a ^ 2 ≠ 1 := by rw [ha2]; exact hz1
  have hordera : orderOf a = 4 := by
    rw [orderOf_eq_iff (by norm_num : (0 : ℕ) < 4)]
    refine ⟨ha4, ?_⟩
    intro m hm hm0
    interval_cases m
    · simpa using ha_ne_one
    · exact ha2_ne_one
    · intro h3
      have h1 : a = 1 := by
        calc a = a ^ 3 * a := by rw [h3, one_mul]
          _ = a ^ 4 := (pow_succ a 3).symm
          _ = 1 := ha4
      exact ha_ne_one h1
  let N : Subgroup T := Subgroup.zpowers a
  have hNcard : Nat.card N = 4 := by
    show Nat.card (Subgroup.zpowers a) = 4
    rw [Nat.card_zpowers, hordera]
  have hNindex : N.index = 4 := by
    have h := Subgroup.card_mul_index N
    rw [hNcard, hcard] at h
    omega
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← hk]
    rw [show g * a ^ k * g⁻¹ = (g * a * g⁻¹) ^ k from (conj_zpow).symm]
    have hmem : g * a * g⁻¹ ∈ N := by
      rcases hnorm g with h | h
      · rw [h]; exact Subgroup.mem_zpowers a
      · rw [h]
        show z * a ∈ Subgroup.zpowers a
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨3, ?_⟩
        rw [show (3 : ℤ) = (2 : ℤ) + 1 by norm_num, zpow_add, zpow_one, hapow2]
    exact Subgroup.zpow_mem N hmem k
  haveI : N.Normal := hNnormal
  let b' : T ⧸ N := QuotientGroup.mk' N b
  have hQcard : Nat.card (T ⧸ N) = 4 := by
    rw [← Subgroup.index_eq_card N, hNindex]
  have hb'2 : b' ^ 2 = 1 := by
    change (QuotientGroup.mk' N b) ^ 2 = 1
    rw [← map_pow, hb2]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    show z ∈ Subgroup.zpowers a
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨2, hapow2⟩
  have hb'zpow2 : b' ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = (2 : ℕ) by norm_num, zpow_natCast, hb'2]
  have hbN : b ∉ N := by
    intro hbN'
    have hbcomm : b * a = a * b := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbN'
      rw [← hk]
      exact (Commute.refl a).zpow_left k
    have hbconj : b * a * b⁻¹ = a := by rw [hbcomm]; simp
    have h1 : a = z * a := hbconj.symm.trans hba
    have h2 : (1 : T) = z := by
      have := congrArg (· * a⁻¹) h1
      simpa using this
    exact hz1 h2.symm
  have hb'ne : b' ≠ 1 := by
    intro h
    apply hbN
    have h1 : QuotientGroup.mk' N b = 1 := h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hb'order : orderOf b' = 2 := by
    rw [orderOf_eq_iff (by norm_num : (0 : ℕ) < 2)]
    refine ⟨hb'2, ?_⟩
    intro m hm hm0
    interval_cases m
    · simpa using hb'ne
  have hbzcard : Nat.card (Subgroup.zpowers b') = 2 := by
    rw [Nat.card_zpowers, hb'order]
  have hidx_zp : (Subgroup.zpowers b').index = 2 := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers b')
    rw [hbzcard, hQcard] at h
    omega
  let M : Subgroup T := (Subgroup.zpowers b').comap (QuotientGroup.mk' N)
  have hMindex : M.index = 2 := by
    show ((Subgroup.zpowers b').comap (QuotientGroup.mk' N)).index = 2
    rw [Subgroup.index_comap_of_surjective (Subgroup.zpowers b')
      (QuotientGroup.mk'_surjective N)]
    exact hidx_zp
  have hb'pow : ∀ k : ℤ, b' ^ k = 1 ∨ b' ^ k = b' := by
    intro k
    rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
    · left
      rw [hm, zpow_mul, hb'zpow2, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, hb'zpow2, one_zpow, one_mul, zpow_one]
  refine ⟨M, hMindex, ?_⟩
  intro u hu hu2
  have hπu : QuotientGroup.mk' N u ∈ Subgroup.zpowers b' := hu
  have hpair : QuotientGroup.mk' N u = 1 ∨ QuotientGroup.mk' N u = b' := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hπu
    rw [← hk]
    exact hb'pow k
  rcases hpair with h1 | hb1
  · have huN : u ∈ N := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huN
    have hzk : z ^ k = 1 := by
      have huu : a ^ k * a ^ k = 1 := by rw [hk]; exact hu2
      have h2 : z ^ k = a ^ k * a ^ k := by
        calc z ^ k = (a ^ (2 : ℤ)) ^ k := by rw [hapow2]
          _ = a ^ (2 * k) := (zpow_mul a 2 k).symm
          _ = a ^ (k + k) := by congr 1; ring
          _ = a ^ k * a ^ k := zpow_add a k k
      rw [h2, huu]
    have h2dvd : (2 : ℤ) ∣ k := by
      have hzorder : orderOf z = 2 := by
        rw [orderOf_eq_iff (by norm_num : (0 : ℕ) < 2)]
        refine ⟨hzsq, ?_⟩
        intro m hm hm0
        interval_cases m
        · simpa using hz1
      have h := orderOf_dvd_iff_zpow_eq_one.mpr hzk
      rwa [hzorder] at h
    obtain ⟨m, hm⟩ := h2dvd
    have huz : u = z ^ m := by
      rw [← hk, hm, zpow_mul, hapow2]
    rw [Subgroup.mem_center_iff]
    intro g
    rw [huz]
    exact Commute.zpow_right (Subgroup.mem_center_iff.mp hz g) m
  · have hbuN : b⁻¹ * u ∈ N := by
      have h1 : QuotientGroup.mk' N (b⁻¹ * u) = 1 := by
        rw [map_mul, map_inv, hb1]
        rw [show QuotientGroup.mk' N b = b' from rfl]
        exact inv_mul_cancel b'
      rw [QuotientGroup.mk'_apply] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbuN
    have hu_eq : u = b * a ^ k := by
      rw [hk, ← mul_assoc, mul_inv_cancel, one_mul]
    have hza_comm : ∀ n : ℤ, a ^ n * z = z * a ^ n := fun n =>
      Subgroup.mem_center_iff.mp hz (a ^ n)
    have hz1k : z ^ k * z = z ^ (k + 1) := by
      calc z ^ k * z = z ^ k * z ^ (1 : ℤ) := by rw [zpow_one]
        _ = z ^ (k + 1) := (zpow_add z k 1).symm
    have haa : a ^ k * a ^ k = a ^ (2 * k) := by
      calc a ^ k * a ^ k = a ^ (k + k) := (zpow_add a k k).symm
        _ = a ^ (2 * k) := by congr 1; ring
    have ha2k : a ^ (2 * k) = z ^ k := by
      calc a ^ (2 * k) = (a ^ (2 : ℤ)) ^ k := zpow_mul a 2 k
        _ = z ^ k := by rw [hapow2]
    have hz2k1 : z ^ (2 * k + 1) = z := by
      calc z ^ (2 * k + 1) = z ^ (2 * k) * z ^ (1 : ℤ) := zpow_add z (2 * k) 1
        _ = (z ^ (2 : ℤ)) ^ k * z := by rw [zpow_mul, zpow_one]
        _ = 1 ^ k * z := by rw [hazpow2]
        _ = 1 * z := by rw [one_zpow]
        _ = z := one_mul z
    have hconj : b * a ^ k * b⁻¹ = z ^ k * a ^ k := by
      calc b * a ^ k * b⁻¹ = (b * a * b⁻¹) ^ k := (conj_zpow).symm
        _ = (z * a) ^ k := by rw [hba]
        _ = z ^ k * a ^ k :=
          Commute.mul_zpow ((Subgroup.mem_center_iff.mp hz a).symm) k
    have hfinal : (z ^ k * a ^ k) * z * a ^ k = z := by
      calc (z ^ k * a ^ k) * z * a ^ k
          = (z ^ k * (a ^ k * z)) * a ^ k := by rw [mul_assoc (z ^ k) (a ^ k) z]
        _ = (z ^ k * (z * a ^ k)) * a ^ k := by rw [hza_comm k]
        _ = (z ^ k * z) * (a ^ k * a ^ k) := by
              rw [← mul_assoc (z ^ k) z (a ^ k),
                mul_assoc (z ^ k * z) (a ^ k) (a ^ k)]
        _ = z ^ (k + 1) * a ^ (2 * k) := by rw [hz1k, haa]
        _ = z ^ (k + 1) * z ^ k := by rw [ha2k]
        _ = z ^ (k + 1 + k) := (zpow_add z (k + 1) k).symm
        _ = z ^ (2 * k + 1) := by congr 1; ring
        _ = z := hz2k1
    have hsqu : (b * a ^ k) * (b * a ^ k) = z := by
      have h1 : (b * a ^ k) * (b * a ^ k) =
          (b * a ^ k * b⁻¹) * (b * b) * a ^ k := by group
      rw [h1, hconj, hb]
      exact hfinal
    exfalso
    have hz1' : z = 1 := by
      rw [← hsqu, ← hu_eq]
      exact hu2
    exact hz1 hz1'

end CFSG.GroupTheory.SmallFixedTwoGroup
