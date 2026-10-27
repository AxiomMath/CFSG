module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {C : Type*} [Group C]

def powHom (p : ℕ) (hpow : ∀ x y : C, (x * y) ^ p = x ^ p * y ^ p) : C →* C where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' := hpow

@[simp] theorem powHom_apply (hpow : ∀ x y : C, (x * y) ^ p = x ^ p * y ^ p) (x : C) :
    powHom p hpow x = x ^ p := (rfl)

theorem coe_ker_powHom (hpow : ∀ x y : C, (x * y) ^ p = x ^ p * y ^ p) :
    ((powHom p hpow).ker : Set C) = {x : C | x ^ p = 1} := by
  ext x; simp [MonoidHom.mem_ker]

theorem apply_eq_self_of_pow_pow_eq_one
    (hpow : ∀ x y : C, (x * y) ^ p = x ^ p * y ^ p)
    {a : MulAut C} (ha : ∀ h : C, h ^ p = 1 → a h = h)
    {n : ℕ} (hn : Nat.Coprime n p) (han : a ^ n = 1) :
    ∀ (k : ℕ) (x : C), x ^ p ^ k = 1 → a x = x := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp only [pow_zero, pow_one] at hx
      subst hx
      simp
  | succ k ih =>
      intro x hx
      have hxp : a (x ^ p) = x ^ p := by
        refine ih (x ^ p) ?_
        rw [← pow_mul, ← pow_succ']
        exact hx
      set y : C := x⁻¹ * a x with hy
      have hyp : y ^ p = 1 := by
        rw [hy, hpow, ← map_pow, hxp, inv_pow, inv_mul_cancel]
      have hay : a y = y := ha y hyp
      have hax : a x = x * y := by rw [hy, mul_inv_cancel_left]
      have key : ∀ m : ℕ, (a ^ m) x = x * y ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ihm =>
            rw [pow_succ', MulAut.mul_apply, ihm, map_mul, map_pow, hay, hax, pow_succ]
            group
      have hxy : x * y ^ n = x := by rw [← key n, han]; simp
      have hyn : y ^ n = 1 := mul_eq_left.mp hxy
      have hdvd : orderOf y ∣ Nat.gcd n p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyn) (orderOf_dvd_of_pow_eq_one hyp)
      rw [hn] at hdvd
      have hy1 : y = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
      rw [hax, hy1, mul_one]

theorem eq_one_of_isPGroup_of_coprime_pow_eq_one (hC : IsPGroup p C)
    (hpow : ∀ x y : C, (x * y) ^ p = x ^ p * y ^ p)
    {a : MulAut C} (ha : ∀ h : C, h ^ p = 1 → a h = h)
    {n : ℕ} (hn : Nat.Coprime n p) (han : a ^ n = 1) : a = 1 := by
  ext x
  obtain ⟨k, hk⟩ := hC.exists_pow_pow_eq_one x
  exact apply_eq_self_of_pow_pow_eq_one hpow ha hn han k x hk

theorem isPGroup_fixingSubgroup_setOf_pow_eq_one [Finite C] (hp : p.Prime) (hC : IsPGroup p C)
    (hpow : ∀ x y : C, (x * y) ^ p = x ^ p * y ^ p) :
    IsPGroup p (fixingSubgroup (MulAut C) {x : C | x ^ p = 1}) := by
  rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, hp.primeFactors]
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hqp, hqdvd, -⟩ := hq
  simp only [Finset.mem_singleton]
  by_contra hne
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨a, hao⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  have haq : (a : MulAut C) ^ q = 1 := by
    rw [← Subgroup.coe_pow, ← hao, pow_orderOf_eq_one, Subgroup.coe_one]
  have hfix : ∀ h : C, h ^ p = 1 → (a : MulAut C) h = h := fun h hh =>
    (mem_fixingSubgroup_iff _).mp a.2 h hh
  have h1 : a = 1 :=
    Subtype.ext (eq_one_of_isPGroup_of_coprime_pow_eq_one hC hpow hfix
      ((Nat.coprime_primes hqp hp).mpr hne) haq)
  rw [h1, orderOf_one] at hao
  exact hqp.one_lt.ne hao

theorem exists_natCard_fixingSubgroup_eq_pow [Finite C] (hp : p.Prime) (hC : IsPGroup p C)
    (hpow : ∀ x y : C, (x * y) ^ p = x ^ p * y ^ p) :
    ∃ n : ℕ, Nat.card (fixingSubgroup (MulAut C) {x : C | x ^ p = 1}) = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.iff_card.mp (isPGroup_fixingSubgroup_setOf_pow_eq_one hp hC hpow)

end

end CFSG.FeitThompson
