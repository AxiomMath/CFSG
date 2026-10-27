module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMBasic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

theorem QuaternionGroup.mulAut_eq_one_of_odd {k : ℕ} (hk : 2 ≤ k)
    (φ : MulAut (QuaternionGroup (2 ^ k))) (hφ : Odd (orderOf φ)) : φ = 1 := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  haveI : NeZero (2 * 2 ^ k) := ⟨by positivity⟩
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hN : φ ^ orderOf φ = 1 := pow_orderOf_eq_one φ
  have hord1 : orderOf (φ (QuaternionGroup.a 1)) = 2 * 2 ^ k := by
    have h := orderOf_injective (φ : QuaternionGroup (2 ^ k) ≃* QuaternionGroup (2 ^ k)).toMonoidHom
      (EquivLike.injective φ) (QuaternionGroup.a 1)
    rw [MulEquiv.coe_toMonoidHom] at h
    rw [h, QuaternionGroup.orderOf_a_one]
  obtain ⟨m, hm⟩ : ∃ m : ZMod (2 * 2 ^ k), φ (QuaternionGroup.a 1) = QuaternionGroup.a m := by
    rcases hx : φ (QuaternionGroup.a 1) with m | j
    · exact ⟨m, rfl⟩
    · exfalso
      rw [hx, QuaternionGroup.orderOf_xa] at hord1
      omega
  have hφa : ∀ t : ZMod (2 * 2 ^ k), φ (QuaternionGroup.a t) = QuaternionGroup.a (m * t) := by
    have hap : ∀ j : ℕ, (QuaternionGroup.a m : QuaternionGroup (2 ^ k)) ^ j =
        QuaternionGroup.a ((j : ZMod (2 * 2 ^ k)) * m) := by
      intro j
      induction j with
      | zero =>
        rw [pow_zero, Nat.cast_zero, zero_mul]
        rfl
      | succ j ih =>
        rw [pow_succ, ih, QuaternionGroup.a_mul_a]
        congr 1
        push_cast
        ring
    intro t
    have ht : (QuaternionGroup.a t : QuaternionGroup (2 ^ k)) = QuaternionGroup.a 1 ^ t.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [ht, map_pow, hm, hap, ZMod.natCast_zmod_val, mul_comm t m]
  have hiter : ∀ (j : ℕ) (t : ZMod (2 * 2 ^ k)),
      (φ ^ j) (QuaternionGroup.a t) = QuaternionGroup.a (m ^ j * t) := by
    intro j
    induction j with
    | zero => intro t; simp
    | succ j ih =>
      intro t
      rw [pow_succ' φ j, MulAut.mul_apply, ih, hφa, pow_succ m j]
      congr 1
      ring
  have hmN : m ^ orderOf φ = 1 := by
    have h := hiter (orderOf φ) 1
    rw [hN, MulAut.one_apply, mul_one] at h
    exact (QuaternionGroup.a.inj h).symm
  have hmu : IsUnit m := IsUnit.of_pow_eq_one hmN hφ.pos.ne'
  have htotient : Nat.totient (2 * 2 ^ k) = 2 ^ k := by
    rw [← pow_succ', Nat.totient_prime_pow_succ Nat.prime_two]
    norm_num
  have htot : m ^ (2 ^ k) = 1 := by
    have hcard : Fintype.card (ZMod (2 * 2 ^ k))ˣ = 2 ^ k := by
      rw [ZMod.card_units_eq_totient, htotient]
    have hT : hmu.unit ^ Fintype.card (ZMod (2 * 2 ^ k))ˣ = 1 := pow_card_eq_one
    rw [hcard] at hT
    have hT' := congrArg Units.val hT
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at hT'
    exact hT'
  have hcop : Nat.Coprime (orderOf φ) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hφ)
  have hm1 : m = 1 := by
    have hg : m ^ Nat.gcd (orderOf φ) (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hmN, htot⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
    exact hg
  have hφa1 : ∀ t : ZMod (2 * 2 ^ k), φ (QuaternionGroup.a t) = QuaternionGroup.a t := by
    intro t
    rw [hφa, hm1, one_mul]
  obtain ⟨b, hb⟩ : ∃ b : ZMod (2 * 2 ^ k), φ (QuaternionGroup.xa 0) = QuaternionGroup.xa b := by
    rcases hx : φ (QuaternionGroup.xa 0) with c | b
    · exfalso
      have h1 : φ (QuaternionGroup.xa 0) = φ (QuaternionGroup.a c) := by
        rw [hx, hφa1]
      have h2 := EquivLike.injective φ h1
      cases h2
    · exact ⟨b, rfl⟩
  have hxa_eq : ∀ t : ZMod (2 * 2 ^ k),
      (QuaternionGroup.xa t : QuaternionGroup (2 ^ k)) =
        QuaternionGroup.xa 0 * QuaternionGroup.a t := by
    intro t
    rw [QuaternionGroup.xa_mul_a, zero_add]
  have hφx : ∀ t : ZMod (2 * 2 ^ k), φ (QuaternionGroup.xa t) = QuaternionGroup.xa (b + t) := by
    intro t
    rw [hxa_eq t, map_mul, hb, hφa1, QuaternionGroup.xa_mul_a]
  have hiterx : ∀ j : ℕ, (φ ^ j) (QuaternionGroup.xa 0) =
      QuaternionGroup.xa ((j : ZMod (2 * 2 ^ k)) * b) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ' φ j, MulAut.mul_apply, ih, hφx]
      congr 1
      push_cast
      ring
  have hNb : (orderOf φ : ZMod (2 * 2 ^ k)) * b = 0 := by
    have h := hiterx (orderOf φ)
    rw [hN, MulAut.one_apply] at h
    exact (QuaternionGroup.xa.inj h).symm
  have hb0 : b = 0 := by
    have hcop2 : Nat.Coprime (orderOf φ) (2 * 2 ^ k) :=
      Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hφ) hcop
    have hu := Units.inv_mul (ZMod.unitOfCoprime (orderOf φ) hcop2)
    rw [ZMod.coe_unitOfCoprime] at hu
    obtain ⟨w, hw⟩ : ∃ w : ZMod (2 * 2 ^ k), w * (orderOf φ : ZMod (2 * 2 ^ k)) = 1 := ⟨_, hu⟩
    linear_combination (-b) * hw + w * hNb
  apply MulEquiv.ext
  intro x
  cases x with
  | a t => rw [MulAut.one_apply]; exact hφa1 t
  | xa t => rw [MulAut.one_apply, hφx, hb0, zero_add]

end CFSG.CGT.PushingUpLit.SolKNA.R4
