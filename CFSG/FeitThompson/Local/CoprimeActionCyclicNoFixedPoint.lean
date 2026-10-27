module

public import Mathlib.NumberTheory.Basic
public import Mathlib.GroupTheory.PGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {A Q : Type*} [Group A] [Group Q] {p q : ℕ}

private lemma pow_apply_of_forall_apply_eq_zpow (σ : MulAut Q) (m : ℤ)
    (hσ : ∀ y : Q, σ y = y ^ m) (t : ℕ) : ∀ y : Q, (σ ^ t) y = y ^ m ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, hσ y, ih (y ^ m), ← zpow_mul, pow_succ']

theorem pow_natCard_eq_one_of_apply_eq_self [Fact q.Prime] [Finite Q] [IsCyclic Q]
    (hQ : IsPGroup q Q) {σ : MulAut Q} {x : Q} (hx : x ≠ 1) (hσx : σ x = x) :
    σ ^ Nat.card Q = 1 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (MulEquiv.toMonoidHom σ)
  have hm' : ∀ y : Q, σ y = y ^ m := hm
  have hqm : (q : ℤ) ∣ m - 1 := by
    obtain ⟨k, hk⟩ := hQ x
    obtain ⟨i, hi, hix⟩ :=
      (Nat.dvd_prime_pow (Fact.out : q.Prime)).mp (orderOf_dvd_of_pow_eq_one hk)
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hx (orderOf_eq_one_iff.mp (by simpa using hix))
    have hqx : (q : ℤ) ∣ (orderOf x : ℤ) := by
      rw [hix]; exact_mod_cast dvd_pow_self q hi0
    have hxm : x ^ m = x ^ (1 : ℤ) := by rw [zpow_one, ← hm' x, hσx]
    exact hqx.trans (Int.ModEq.dvd (zpow_eq_zpow_iff_modEq.mp hxm).symm)
  have key : ((Nat.card Q : ℤ)) ∣ m ^ Nat.card Q - 1 := by
    have h := dvd_sub_pow_of_dvd_sub (p := q) (a := m) (b := 1) hqm n
    simp only [one_pow] at h
    rw [hn]
    refine dvd_trans ?_ h
    push_cast
    exact pow_dvd_pow _ (Nat.le_succ n)
  refine MulEquiv.ext fun y => ?_
  rw [pow_apply_of_forall_apply_eq_zpow σ m hm']
  have hy : (orderOf y : ℤ) ∣ m ^ Nat.card Q - 1 :=
    dvd_trans (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard y)) key
  have hfin : y ^ (m ^ Nat.card Q) = y ^ (1 : ℤ) := by
    rw [zpow_eq_zpow_iff_modEq]
    exact Int.modEq_iff_dvd.mpr (by simpa using hy.neg_right)
  simpa using hfin

theorem eq_one_of_exists_ne_one_fixed [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    [Finite A] [Finite Q] [IsCyclic Q] (hA : IsPGroup p A) (hQ : IsPGroup q Q)
    (φ : A →* MulAut Q) (hfix : ∃ x : Q, x ≠ 1 ∧ ∀ a : A, φ a x = x) : φ = 1 := by
  obtain ⟨x, hx, hfix⟩ := hfix
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card A) := by
    rw [hn, hk]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hpq))
  refine MonoidHom.ext fun a => ?_
  have h1 : orderOf (φ a) ∣ Nat.card Q :=
    orderOf_dvd_of_pow_eq_one (pow_natCard_eq_one_of_apply_eq_self hQ hx (hfix a))
  have h2 : orderOf (φ a) ∣ Nat.card A := (orderOf_map_dvd φ a).trans (orderOf_dvd_natCard a)
  simpa using orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem range_eq_bot_of_exists_ne_one_fixed [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    [Finite A] [Finite Q] [IsCyclic Q] (hA : IsPGroup p A) (hQ : IsPGroup q Q)
    (φ : A →* MulAut Q) (hfix : ∃ x : Q, x ≠ 1 ∧ ∀ a : A, φ a x = x) : φ.range = ⊥ := by
  rw [eq_one_of_exists_ne_one_fixed hpq hA hQ φ hfix]
  exact MonoidHom.range_one

theorem smul_eq_self_of_fixedPoints_ne_bot [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    [Finite A] [Finite Q] [IsCyclic Q] [MulDistribMulAction A Q] (hA : IsPGroup p A)
    (hQ : IsPGroup q Q) (hfix : FixedPoints.subgroup A Q ≠ ⊥) (a : A) (y : Q) : a • y = y := by
  obtain ⟨⟨x, hxmem⟩, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfix
  have hx1 : x ≠ 1 := by simpa using hx
  have hφ := eq_one_of_exists_ne_one_fixed hpq hA hQ (MulDistribMulAction.toMulAut A Q)
    ⟨x, hx1, fun a => (FixedPoints.mem_subgroup A Q x).mp hxmem a⟩
  simpa using congrArg (fun f => (f a) y) hφ

theorem fixedPoints_subgroup_eq_top_of_ne_bot [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    [Finite A] [Finite Q] [IsCyclic Q] [MulDistribMulAction A Q] (hA : IsPGroup p A)
    (hQ : IsPGroup q Q) (hfix : FixedPoints.subgroup A Q ≠ ⊥) :
    FixedPoints.subgroup A Q = ⊤ := by
  rw [Subgroup.eq_top_iff']
  exact fun y => (FixedPoints.mem_subgroup A Q y).mpr fun a =>
    smul_eq_self_of_fixedPoints_ne_bot hpq hA hQ hfix a y

end

end CFSG.FeitThompson
