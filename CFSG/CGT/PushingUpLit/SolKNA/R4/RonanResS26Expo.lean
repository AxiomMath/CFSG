module

public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TL4

theorem expo_quat_pow_two_mul {n : ℕ} [NeZero n] (hn : 2 ∣ n) (x : QuaternionGroup n) :
    x ^ (2 * n) = 1 := by
  cases x with
  | a i =>
    have h : orderOf (QuaternionGroup.a i : QuaternionGroup n) ∣ 2 * n := by
      rw [QuaternionGroup.orderOf_a]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    exact orderOf_dvd_iff_pow_eq_one.1 h
  | xa i =>
    have h : orderOf (QuaternionGroup.xa i : QuaternionGroup n) ∣ 2 * n := by
      rw [QuaternionGroup.orderOf_xa]
      obtain ⟨k, hk⟩ := hn
      exact ⟨k, by omega⟩
    exact orderOf_dvd_iff_pow_eq_one.1 h

theorem two_elt_pow_eq_one_of_mem {r : ℕ} (hr : 3 ≤ r) {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hΦ : TypeRFam r Φ) {A : Subgroup X} (hA : A ∈ Φ) {c : X} (hc : c ∈ A)
    {k : ℕ} (hck : c ^ 2 ^ k = 1) : c ^ 2 ^ (r - 1) = 1 := by
  have hA2 : (⟨c, hc⟩ : A) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hck)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hA2)
  have hZ : IsPGroup 2 (Subgroup.zpowers (⟨c, hc⟩ : A)) :=
    IsPGroup.iff_card.mpr ⟨i, by rw [Nat.card_zpowers, hi]⟩
  obtain ⟨S, hSZ⟩ := IsPGroup.exists_le_sylow hZ
  have hcP : c ∈ (S : Subgroup A).map A.subtype :=
    Subgroup.mem_map_of_mem A.subtype (hSZ (Subgroup.mem_zpowers _))
  obtain ⟨e⟩ := hΦ.quat A hA _ (isSylow2In_map_subtype A S)
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hn : 2 ∣ 2 ^ (r - 2) := dvd_pow_self 2 (by omega)
  have h1 : (⟨c, hcP⟩ : ↥((S : Subgroup A).map A.subtype)) ^ (2 * 2 ^ (r - 2)) = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact expo_quat_pow_two_mul hn _
  have h2 : c ^ (2 * 2 ^ (r - 2)) = 1 := by
    simpa using congrArg Subtype.val h1
  have h3 : 2 * 2 ^ (r - 2) = 2 ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [← h3]
  exact h2

theorem r_eq_of_card_sylow {r m : ℕ} (hr : 3 ≤ r) {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hΦ : TypeRFam r Φ) {A : Subgroup X} (hA : A ∈ Φ) {P : Subgroup X}
    (hP : IsSylow2In P A) (hcard : Nat.card P = 2 ^ (m + 2)) : m + 2 = r := by
  obtain ⟨e⟩ := hΦ.quat A hA P hP
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have h4 : 2 ^ r = 4 * 2 ^ (r - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have h1 : Nat.card P = 2 ^ r := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card, h4]
  rw [hcard] at h1
  exact Nat.pow_right_injective le_rfl h1

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
