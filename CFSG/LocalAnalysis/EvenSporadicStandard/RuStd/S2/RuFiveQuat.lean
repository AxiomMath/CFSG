module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open QuaternionGroup

section Quat

variable {G : Type*} [Group G]

theorem conj_pow_eq_inv {i j : G} (hji : j * i * j⁻¹ = i⁻¹) (m : ℕ) :
    j * i ^ m * j⁻¹ = (i ^ m)⁻¹ := by
  have h : MulAut.conj j i = i⁻¹ := by simpa using hji
  have := map_pow (MulAut.conj j) i m
  rw [h, inv_pow] at this
  simpa using this

theorem pow_mul_conj {i j : G} (hji : j * i * j⁻¹ = i⁻¹) (m : ℕ) :
    i ^ m * j = j * (i ^ m)⁻¹ := by
  have h1 := conj_pow_eq_inv hji m
  have h2 : j * (i ^ m)⁻¹ * j⁻¹ = i ^ m := by
    have := congrArg (fun x : G => x⁻¹) h1
    simpa [mul_assoc] using this
  calc i ^ m * j = j * (i ^ m)⁻¹ * j⁻¹ * j := by rw [h2]
    _ = j * (i ^ m)⁻¹ := by group

variable {n : ℕ} [NeZero n]

theorem val_add_pow {i : G} (hi : i ^ (2 * n) = 1) (k l : ZMod (2 * n)) :
    i ^ (k + l).val = i ^ k.val * i ^ l.val := by
  rw [ZMod.val_add, ← pow_add, pow_eq_pow_mod (k.val + l.val) hi]

theorem val_neg_pow {i : G} (hi : i ^ (2 * n) = 1) (k : ZMod (2 * n)) :
    i ^ (-k).val = (i ^ k.val)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← val_add_pow hi, add_neg_cancel, ZMod.val_zero, pow_zero]

theorem val_natCast_pow {i : G} : i ^ ((n : ZMod (2 * n)).val) = i ^ n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  have := NeZero.pos n
  omega

@[expose] def quatFun (i j : G) : QuaternionGroup n → G
  | QuaternionGroup.a k => i ^ k.val
  | QuaternionGroup.xa k => j * i ^ k.val

theorem quatFun_mul {i j : G} (hi : i ^ (2 * n) = 1) (hj : j ^ 2 = i ^ n)
    (hji : j * i * j⁻¹ = i⁻¹) (x y : QuaternionGroup n) :
    quatFun i j (x * y) = quatFun i j x * quatFun i j y := by
  have hc : ∀ a b : ℕ, Commute (i ^ a) (i ^ b) := fun a b => (Commute.refl i).pow_pow a b
  rcases x with k | k <;> rcases y with l | l
  · simp only [QuaternionGroup.a_mul_a, quatFun]
    exact val_add_pow hi k l
  · simp only [QuaternionGroup.a_mul_xa, quatFun, sub_eq_add_neg]
    rw [val_add_pow hi, val_neg_pow hi]
    calc j * (i ^ l.val * (i ^ k.val)⁻¹) = j * ((i ^ k.val)⁻¹ * i ^ l.val) := by
          rw [((hc k.val l.val).inv_left).eq]
      _ = (j * (i ^ k.val)⁻¹) * i ^ l.val := (mul_assoc _ _ _).symm
      _ = (i ^ k.val * j) * i ^ l.val := by rw [pow_mul_conj hji]
      _ = i ^ k.val * (j * i ^ l.val) := mul_assoc _ _ _
  · simp only [QuaternionGroup.xa_mul_a, quatFun]
    rw [val_add_pow hi, mul_assoc]
  · simp only [QuaternionGroup.xa_mul_xa, quatFun, sub_eq_add_neg]
    rw [val_add_pow hi, val_add_pow hi, val_neg_pow hi, val_natCast_pow]
    calc i ^ n * i ^ l.val * (i ^ k.val)⁻¹ = i ^ n * ((i ^ k.val)⁻¹ * i ^ l.val) := by
          rw [mul_assoc, ((hc k.val l.val).inv_left).eq]
      _ = j * j * ((i ^ k.val)⁻¹ * i ^ l.val) := by rw [← sq, hj]
      _ = j * (j * (i ^ k.val)⁻¹) * i ^ l.val := by simp only [mul_assoc]
      _ = j * (i ^ k.val * j) * i ^ l.val := by rw [pow_mul_conj hji]
      _ = j * i ^ k.val * (j * i ^ l.val) := by simp only [mul_assoc]

@[expose] def quatHom (i j : G) (hi : i ^ (2 * n) = 1) (hj : j ^ 2 = i ^ n)
    (hji : j * i * j⁻¹ = i⁻¹) : QuaternionGroup n →* G where
  toFun := quatFun i j
  map_one' := by
    rw [QuaternionGroup.one_def]
    simp [quatFun]
  map_mul' := quatFun_mul hi hj hji

end Quat

theorem quat2_unique_involution :
    ∀ x y : QuaternionGroup 2, x ^ 2 = 1 → x ≠ 1 → y ^ 2 = 1 → y ≠ 1 → x = y := by
  decide

theorem card_quat2 : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

section Inj

variable {G : Type*} [Group G]

theorem quatHom_injective {i j : G} (hi4 : i ^ 4 = 1) (hi2 : i ^ 2 ≠ 1) (hj : j ^ 2 = i ^ 2)
    (hji : j * i * j⁻¹ = i⁻¹) :
    Function.Injective (quatHom (n := 2) i j (by simpa using hi4) hj hji) := by
  have hord : orderOf i = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := i) (by simpa using hi2)
      (by simpa using hi4)
    simpa using this
  rw [injective_iff_map_eq_one]
  rintro (k | k) h
  · have h1 : i ^ k.val = 1 := h
    have h2 : 4 ∣ k.val := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one h1
    have h3 : k.val < 4 := ZMod.val_lt k
    have h4 : k.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 h3
    have : k = 0 := by simpa using (ZMod.val_eq_zero k).1 h4
    rw [this]
    exact QuaternionGroup.a_zero
  · exfalso
    have h1 : j * i ^ k.val = 1 := h
    have h2 : j = (i ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (i ^ k.val)⁻¹ * i * i ^ k.val = i := by
      have hc : Commute i (i ^ k.val) := (Commute.refl i).pow_right k.val
      rw [← hc.inv_right.eq, inv_mul_cancel_right]
    rw [h2, inv_inv, h3] at hji
    apply hi2
    calc i ^ 2 = i * i := sq i
      _ = 1 := by nth_rewrite 1 [hji]; exact inv_mul_cancel i

end Inj

end CFSG.EvenSporadicStandard.RuStd.S2
