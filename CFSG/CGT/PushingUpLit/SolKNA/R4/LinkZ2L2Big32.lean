module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigQuatAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.QuatAutH

open QuaternionGroup

noncomputable def doublePhi (n : ℕ) : ZMod (2 * n) →+ ZMod (2 * (2 * n)) :=
  ZMod.lift (2 * n)
    ⟨(AddMonoidHom.mulLeft (2 : ZMod (2 * (2 * n)))).comp
        (Int.castAddHom (ZMod (2 * (2 * n)))), by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, Int.coe_castAddHom,
        AddMonoidHom.coe_mulLeft]
      have : (2 : ZMod (2 * (2 * n))) * (((2 * n : ℕ) : ℤ) : ZMod (2 * (2 * n))) =
          ((2 * (2 * n) : ℕ) : ZMod (2 * (2 * n))) := by
        push_cast
        ring
      rw [this]
      exact ZMod.natCast_self _⟩

theorem doublePhi_intCast (n : ℕ) (k : ℤ) :
    doublePhi n (k : ZMod (2 * n)) = (2 : ZMod (2 * (2 * n))) * (k : ZMod (2 * (2 * n))) := by
  unfold doublePhi
  rw [ZMod.lift_coe]
  rfl

theorem doublePhi_natCast (n : ℕ) (k : ℕ) :
    doublePhi n (k : ZMod (2 * n)) = (2 : ZMod (2 * (2 * n))) * (k : ZMod (2 * (2 * n))) := by
  rw [← Int.cast_natCast (R := ZMod (2 * n)), doublePhi_intCast]
  push_cast
  ring

theorem doublePhi_central (n : ℕ) :
    doublePhi n ((n : ℕ) : ZMod (2 * n)) = ((2 * n : ℕ) : ZMod (2 * (2 * n))) := by
  rw [doublePhi_natCast]
  push_cast
  ring

theorem doublePhi_val (n : ℕ) [NeZero n] (j : ZMod (2 * n)) :
    doublePhi n j = (2 : ZMod (2 * (2 * n))) * (j.val : ZMod (2 * (2 * n))) := by
  haveI : NeZero (2 * n) := ⟨by have := NeZero.pos n; omega⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val j]
  rw [doublePhi_natCast]

@[expose] noncomputable def doubleHom (n : ℕ) (δ : ZMod (2 * (2 * n))) :
    QuaternionGroup n →* QuaternionGroup (2 * n) where
  toFun q := match q with
    | .a j => .a (doublePhi n j)
    | .xa j => .xa (δ + doublePhi n j)
  map_one' := by
    show a (doublePhi n 0) = 1
    rw [map_zero, one_def]
  map_mul' := by
    rintro (i | i) (j | j)
    · show a (doublePhi n (i + j)) = a (doublePhi n i) * a (doublePhi n j)
      rw [map_add, a_mul_a]
    · show xa (δ + doublePhi n (j - i)) = a (doublePhi n i) * xa (δ + doublePhi n j)
      rw [map_sub, a_mul_xa]
      congr 1
      ring
    · show xa (δ + doublePhi n (i + j)) = xa (δ + doublePhi n i) * a (doublePhi n j)
      rw [map_add, xa_mul_a]
      congr 1
      ring
    · show a (doublePhi n (((n : ℕ) : ZMod (2 * n)) + j - i)) =
        xa (δ + doublePhi n i) * xa (δ + doublePhi n j)
      rw [map_sub, map_add, doublePhi_central, xa_mul_xa]
      congr 1
      ring

theorem doubleHom_a (n : ℕ) (δ : ZMod (2 * (2 * n))) (j : ZMod (2 * n)) :
    doubleHom n δ (a j) = a (doublePhi n j) := rfl

theorem doubleHom_xa (n : ℕ) (δ : ZMod (2 * (2 * n))) (j : ZMod (2 * n)) :
    doubleHom n δ (xa j) = xa (δ + doublePhi n j) := rfl

theorem doublePhi_ker (n : ℕ) [NeZero n] (x : ZMod (2 * n)) (hx : doublePhi n x = 0) : x = 0 := by
  haveI : NeZero (2 * n) := ⟨by have := NeZero.pos n; omega⟩
  have hx' : doublePhi n ((x.val : ℕ) : ZMod (2 * n)) = 0 := by
    rwa [ZMod.natCast_zmod_val x]
  rw [doublePhi_natCast] at hx'
  have h2 : ((2 * x.val : ℕ) : ZMod (2 * (2 * n))) = 0 := by
    push_cast
    exact hx'
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hlt : 2 * x.val < 2 * (2 * n) := by
    have := ZMod.val_lt x
    omega
  have hz : 2 * x.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 hlt
  have hxv : x.val = 0 := by omega
  rw [← ZMod.natCast_zmod_val x, hxv, Nat.cast_zero]

theorem exists_double_hom {n n' : ℕ} [NeZero n] (hn : n' = 2 * n) (δ : ZMod (2 * n')) :
    ∃ φ : QuaternionGroup n →* QuaternionGroup n', Function.Injective φ ∧
      (∀ j : ZMod (2 * n), ∃ k : ZMod (2 * n'), φ (a j) = a k * a k) ∧
      (∀ j : ZMod (2 * n), φ (xa j) = xa δ * φ (a j)) ∧
      φ (a ((n : ℕ) : ZMod (2 * n))) = a ((n' : ℕ) : ZMod (2 * n')) := by
  subst hn
  refine ⟨doubleHom n δ, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    rintro (i | i) hi
    · rw [doubleHom_a, one_def, a.injEq] at hi
      have hi0 : i = 0 := doublePhi_ker n i hi
      rw [hi0, one_def]
    · exfalso
      rw [doubleHom_xa, one_def] at hi
      cases hi
  · intro j
    refine ⟨(j.val : ZMod (2 * (2 * n))), ?_⟩
    rw [doubleHom_a, a_mul_a, doublePhi_val]
    congr 1
    ring
  · intro j
    rw [doubleHom_xa, doubleHom_a, xa_mul_a]
  · rw [doubleHom_a, doublePhi_central]

theorem exists_pow_eq_center {m : ℕ} (q : QuaternionGroup (2 ^ m)) (hq : q ≠ 1) :
    ∃ k : ℕ, q ^ k = a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  have hcard : Nat.card (QuaternionGroup (2 ^ m)) = 2 ^ (m + 2) := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  have hdvd : orderOf q ∣ 2 ^ (m + 2) := hcard ▸ orderOf_dvd_natCard q
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := by
    rcases s with _ | t
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hs, pow_zero])) hq
    · exact ⟨t, rfl⟩
  have hw1 : q ^ 2 ^ t * q ^ 2 ^ t = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hs, pow_orderOf_eq_one]
  have hw2 : q ^ 2 ^ t ≠ 1 := by
    intro h0
    have := orderOf_dvd_of_pow_eq_one h0
    rw [hs] at this
    have := Nat.le_of_dvd (by positivity) this
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) (Nat.lt_succ_self t)
    omega
  rcases (mul_self_eq_one_iff (q ^ 2 ^ t)).mp hw1 with h0 | h0
  · exact absurd (h0.trans (one_def).symm) hw2
  · exact ⟨2 ^ t, h0⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.QuatAutH
