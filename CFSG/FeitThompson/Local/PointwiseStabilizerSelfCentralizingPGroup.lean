module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.PGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {P : Type*} [Group P]

theorem mem_fixingSubgroup_mulAut_iff {C : Subgroup P} {a : MulAut P} :
    a ∈ fixingSubgroup (MulAut P) (C : Set P) ↔ ∀ c ∈ C, a c = c := by
  simp [mem_fixingSubgroup_iff, MulAut.smul_def]

theorem mem_centralizer_inv_mul_apply {C : Subgroup P} [C.Normal]
    {a : MulAut P} (ha : a ∈ fixingSubgroup (MulAut P) (C : Set P)) (x : P) :
    x⁻¹ * a x ∈ Subgroup.centralizer (C : Set P) := by
  rw [mem_fixingSubgroup_mulAut_iff] at ha
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have h1 : a (x * c * x⁻¹) = x * c * x⁻¹ := ha _ (‹C.Normal›.conj_mem c hc x)
  rw [map_mul, map_mul, map_inv, ha c hc] at h1
  have h2 : x⁻¹ * a x * c * (x⁻¹ * a x)⁻¹ = c := by
    calc x⁻¹ * a x * c * (x⁻¹ * a x)⁻¹
        = x⁻¹ * (a x * c * (a x)⁻¹) * x := by group
      _ = x⁻¹ * (x * c * x⁻¹) * x := by rw [h1]
      _ = c := by group
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem apply_pow_eq_mul_pow {a : MulAut P} {x : P} (hy : a (x⁻¹ * a x) = x⁻¹ * a x) (j : ℕ) :
    (a ^ j) x = x * (x⁻¹ * a x) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h : (a ^ (j + 1)) x = a ((a ^ j) x) := by rw [pow_succ']; simp [MulAut.mul_apply]
      rw [h, ih, map_mul, map_pow, hy, pow_succ', ← mul_assoc, mul_inv_cancel_left]

theorem isPGroup_fixingSubgroup_mulAut {p : ℕ} [Finite P] (hp : p.Prime) (hP : IsPGroup p P)
    (C : Subgroup P) [C.Normal] (hC : Subgroup.centralizer (C : Set P) ≤ C) :
    IsPGroup p (fixingSubgroup (MulAut P) (C : Set P)) := by
  have : Fact p.Prime := ⟨hp⟩
  set B := fixingSubgroup (MulAut P) (C : Set P) with hBdef
  refine IsPGroup.of_card (n := (Nat.card B).primeFactorsList.length) ?_
  refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_
  intro q hq hqd
  by_contra hne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' q hqd
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr fun h => hne h.symm
  have haq : ((a : MulAut P) ^ q) = 1 := by
    rw [← ha, ← Subgroup.coe_pow, pow_orderOf_eq_one]
    rfl
  have key : ∀ x : P, (a : MulAut P) x = x := by
    intro x
    have hyC : x⁻¹ * (a : MulAut P) x ∈ C := hC (mem_centralizer_inv_mul_apply a.2 x)
    have hay : (a : MulAut P) (x⁻¹ * (a : MulAut P) x) = x⁻¹ * (a : MulAut P) x :=
      (mem_fixingSubgroup_mulAut_iff.mp a.2) _ hyC
    have hq1 : ((a : MulAut P) ^ q) x = x := by rw [haq]; rfl
    have hyq : (x⁻¹ * (a : MulAut P) x) ^ q = 1 := by
      have h := apply_pow_eq_mul_pow hay q
      rw [hq1] at h
      exact left_eq_mul.mp h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) (x⁻¹ * (a : MulAut P) x)
    have hdvd : p ^ k ∣ q := hk ▸ orderOf_dvd_of_pow_eq_one hyq
    have hpk : p ^ k = 1 := (hcop.pow_left k).eq_one_of_dvd hdvd
    have hy1 : x⁻¹ * (a : MulAut P) x = 1 := orderOf_eq_one_iff.mp (by rw [hk, hpk])
    exact (inv_mul_eq_one.mp hy1).symm
  have hone : a = 1 := by ext x; exact key x
  rw [hone, orderOf_one] at ha
  exact hq.one_lt.ne ha

theorem exists_card_fixingSubgroup_mulAut_eq_pow {p : ℕ} [Finite P] (hp : p.Prime)
    (hP : IsPGroup p P) (C : Subgroup P) [C.Normal]
    (hC : Subgroup.centralizer (C : Set P) ≤ C) :
    ∃ n : ℕ, Nat.card (fixingSubgroup (MulAut P) (C : Set P)) = p ^ n :=
  have : Fact p.Prime := ⟨hp⟩
  (isPGroup_fixingSubgroup_mulAut hp hP C hC).exists_card_eq

end

end CFSG.FeitThompson
