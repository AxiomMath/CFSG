module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

namespace CFSG.GroupTheory.PrimeField

theorem exists_prime_pow_eq_one_not_mem_zpowers {A : Type*} [CommGroup A] [Finite A]
    (hA : ¬ IsCyclic A) :
    ∃ r : ℕ, r.Prime ∧ ∃ x y : A, x ^ r = 1 ∧ y ^ r = 1 ∧ y ≠ 1 ∧ x ∉ Subgroup.zpowers y := by
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := A))
  set m := Monoid.exponent A with hm
  have hm0 : m ≠ 0 := Monoid.ExponentExists.of_finite.exponent_ne_zero
  have htop : Subgroup.zpowers g ≠ ⊤ := fun h =>
    hA (isCyclic_iff_exists_zpowers_eq_top.2 ⟨g, h⟩)
  have hidx : (Subgroup.zpowers g).index ≠ 1 := fun h => htop (Subgroup.index_eq_one.1 h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hidx
  have _ : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := A ⧸ Subgroup.zpowers g) r hrdvd
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  have hhg : h ∉ Subgroup.zpowers g := fun hh => by
    rw [(QuotientGroup.eq_one_iff h).2 hh, orderOf_one] at hz
    exact hr.one_lt.ne hz
  have hhr : h ^ r ∈ Subgroup.zpowers g := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hz, pow_orderOf_eq_one]
  have hrm : r ∣ m := by
    rw [← hz]
    exact (orderOf_map_dvd (QuotientGroup.mk' _) h).trans (Monoid.order_dvd_exponent h)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hhr
  obtain ⟨m', hm'⟩ := hrm
  have hm'0 : m' ≠ 0 := by rintro rfl; simp at hm'; exact hm0 hm'
  have hrk : (r : ℤ) ∣ k := by
    have h1 : g ^ (k * m') = 1 := by
      rw [zpow_mul, hk, zpow_natCast, ← pow_mul, ← hm', hm, Monoid.pow_exponent_eq_one]
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hg, hm', Nat.cast_mul] at h2
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hm'0)).1 h2
  obtain ⟨k', rfl⟩ := hrk
  refine ⟨r, hr, h * g ^ (-k'), g ^ m', ?_, ?_, ?_, ?_⟩
  · rw [mul_pow, ← zpow_natCast (g ^ (-k')), ← zpow_mul, ← hk, ← zpow_add,
      show (r : ℤ) * k' + -k' * r = 0 by ring, zpow_zero]
  · rw [← pow_mul, mul_comm, ← hm', hm, Monoid.pow_exponent_eq_one]
  · refine pow_ne_one_of_lt_orderOf hm'0 ?_
    rw [hg, hm']
    exact lt_mul_left (Nat.pos_of_ne_zero hm'0) hr.one_lt
  · intro hx
    apply hhg
    have hx' : h * g ^ (-k') ∈ Subgroup.zpowers g :=
      Subgroup.zpowers_le.2 (Subgroup.npow_mem_zpowers g m') hx
    have := Subgroup.mul_mem _ hx' (Subgroup.zpow_mem_zpowers g k')
    rwa [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one] at this

theorem exists_fixed_of_pow_eq_one {k V A : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Nontrivial V] [CommGroup A] (ρ : Representation k A V) {r : ℕ} (hr : r.Prime)
    (hrk : (r : k) ≠ 0) {x y : A} (hx : x ^ r = 1) (hy : y ^ r = 1) (hy1 : y ≠ 1)
    (hxy : x ∉ Subgroup.zpowers y) : ∃ a : A, a ≠ 1 ∧ ∃ v : V, v ≠ 0 ∧ ρ a v = v := by
  by_contra! H
  have _ : Fact r.Prime := ⟨hr⟩
  have key : ∀ g : A, g ^ r = 1 → g ≠ 1 → ∀ v, ∑ i ∈ Finset.range r, ρ (g ^ i) v = 0 := by
    intro g hg hg1 v
    by_contra hne
    apply H g hg1 _ hne
    rw [map_sum]
    have hf : ∀ i, ρ g (ρ (g ^ i) v) = ρ (g ^ (i + 1)) v := fun i => by
      rw [pow_succ', map_mul, Module.End.mul_apply]
    simp only [hf]
    have := Finset.sum_range_succ' (fun i => ρ (g ^ i) v) r
    rw [Finset.sum_range_succ, hg, pow_zero] at this
    exact (add_right_cancel this).symm
  have hyo : orderOf y = r := orderOf_eq_prime hy hy1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  have hsum : ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range r, ρ ((x * y ^ j) ^ i) v = 0 :=
    Finset.sum_eq_zero fun j _ => key _ (by rw [mul_pow, hx, one_mul, ← pow_mul, mul_comm,
      pow_mul, hy, one_pow]) (fun h => hxy (by
        rw [mul_eq_one_iff_eq_inv] at h
        rw [h]
        exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers y j))) v
  rw [Finset.sum_comm] at hsum
  have hterm : ∀ i ∈ Finset.range r, ∑ j ∈ Finset.range r, ρ ((x * y ^ j) ^ i) v =
      ρ (x ^ i) (∑ j ∈ Finset.range r, ρ ((y ^ i) ^ j) v) := fun i _ => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, mul_pow, ← pow_mul, ← pow_mul, mul_comm i j]
  rw [Finset.sum_congr rfl hterm] at hsum
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hr.pos; omega⟩
  rw [Finset.sum_range_succ'] at hsum
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [key (y ^ (i + 1)) (by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow])
      (pow_ne_one_of_lt_orderOf (Nat.succ_ne_zero i)
        (by rw [hyo]; exact Nat.succ_lt_succ (Finset.mem_range.1 hi))), map_zero]),
    zero_add] at hsum
  simp only [pow_zero, one_pow, map_one, Module.End.one_apply, Finset.sum_const,
    Finset.card_range] at hsum
  rw [← Nat.cast_smul_eq_nsmul k] at hsum
  exact (smul_eq_zero.1 hsum).resolve_left hrk

theorem noncyclic_abelian_actor_fixed_vector {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] [Nontrivial V] {A : Type*} [CommGroup A]
    [Finite A] (hA : ¬ IsCyclic A) (hcop : Nat.Coprime (Nat.card A) p)
    (ρ : Representation (ZMod p) A V) : ∃ a : A, a ≠ 1 ∧ ∃ v : V, v ≠ 0 ∧ ρ a v = v := by
  obtain ⟨r, hr, x, y, hx, hy, hy1, hxy⟩ := exists_prime_pow_eq_one_not_mem_zpowers hA
  have _ : Fact r.Prime := ⟨hr⟩
  refine exists_fixed_of_pow_eq_one ρ hr ?_ hx hy hy1 hxy
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hpr
  have hrA : r ∣ Nat.card A := orderOf_eq_prime hy hy1 ▸ orderOf_dvd_natCard y
  have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes hcop (hpr.trans hrA) dvd_rfl
  exact (Fact.out : p.Prime).one_lt.ne' hp1

end CFSG.GroupTheory.PrimeField
