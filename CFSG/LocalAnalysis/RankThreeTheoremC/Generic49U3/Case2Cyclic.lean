module

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

theorem cyclic_coprime_aut_trivial {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] {D : Subgroup Y}
    [IsCyclic D] {x : Y} (hDp : ∀ d ∈ D, ∃ k : ℕ, d ^ (p ^ k) = 1) (hx : x ∈ D) (hxo : orderOf x = p)
    {g : Y} (hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hgx : g * x * g⁻¹ = x) {s : ℕ} (hs : Nat.Coprime p s)
    (hgs : ∀ d ∈ D, (g ^ s) * d * (g ^ s)⁻¹ = d) : ∀ d ∈ D, g * d * g⁻¹ = d := by
  obtain ⟨e, he, hgen⟩ : ∃ e ∈ D, ∀ d ∈ D, ∃ n : ℤ, e ^ n = d := by
    obtain ⟨d₁, hd₁⟩ := IsCyclic.exists_generator (α := ↥D)
    refine ⟨d₁.1, d₁.2, fun d hd => ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hd₁ ⟨d, hd⟩)
    refine ⟨n, ?_⟩
    have h := congrArg Subtype.val hn
    rw [Subgroup.coe_zpow] at h
    exact h
  obtain ⟨m, hm⟩ : ∃ m : ℤ, g * e * g⁻¹ = e ^ m := by
    obtain ⟨m, hm⟩ := hgen _ (hgD e he)
    exact ⟨m, hm.symm⟩
  have hconj : ∀ n : ℤ, g * e ^ n * g⁻¹ = e ^ (m * n) := by
    intro n
    rw [← conj_zpow, hm, ← zpow_mul]
  obtain ⟨j, hj⟩ := hgen x hx
  have hxm : x ^ m = x := by
    have h1 : g * e ^ j * g⁻¹ = e ^ j := by rw [hj]; exact hgx
    have h2 : e ^ (m * j) = e ^ j := by rw [← hconj, h1]
    rw [← hj, ← zpow_mul, mul_comm j m, h2]
  have hxm1 : x ^ (m - 1) = 1 := by
    rw [zpow_sub_one, hxm, mul_inv_cancel]
  have hpm : (p : ℤ) ∣ m - 1 := by
    have h := orderOf_dvd_iff_zpow_eq_one.2 hxm1
    rwa [hxo] at h
  obtain ⟨k, hk⟩ := hDp e he
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk)
  have hiter : ∀ n : ℕ, g ^ n * e * (g ^ n)⁻¹ = e ^ (m ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc g ^ (n + 1) * e * (g ^ (n + 1))⁻¹
          = g * (g ^ n * e * (g ^ n)⁻¹) * g⁻¹ := by group
        _ = g * e ^ (m ^ n) * g⁻¹ := by rw [ih]
        _ = e ^ (m * m ^ n) := hconj _
        _ = e ^ (m ^ (n + 1)) := by rw [pow_succ']
  have hgse : e ^ (m ^ s) = e := by
    rw [← hiter s]
    exact hgs e he
  have h1 : e ^ (m ^ s - 1) = 1 := by
    rw [zpow_sub_one, hgse, mul_inv_cancel]
  have hdvd1 : (orderOf e : ℤ) ∣ m ^ s - 1 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [ha, Nat.cast_pow, ← geom_sum_mul m s] at hdvd1
  have hps : ¬ p ∣ s := (Nat.Prime.coprime_iff_not_dvd hp).1 hs
  have hpnd : ¬ (p : ℤ) ∣ ∑ i ∈ Finset.range s, m ^ i := by
    intro hdvd
    have h1' : ((m - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hpm
    have h2' : ((∑ i ∈ Finset.range s, m ^ i : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    push_cast at h1' h2'
    have hm1 : (m : ZMod p) = 1 := sub_eq_zero.1 h1'
    rw [hm1] at h2'
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h2'
    exact hps ((ZMod.natCast_eq_zero_iff s p).1 h2')
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hcop : IsCoprime ((p : ℤ) ^ a) (∑ i ∈ Finset.range s, m ^ i) :=
    IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpr).2 hpnd)
  have hdiv : (p : ℤ) ^ a ∣ m - 1 := hcop.dvd_of_dvd_mul_left hdvd1
  have hdone : e ^ (m - 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.1
    rw [ha, Nat.cast_pow]
    exact hdiv
  have hem : e ^ m = e := by
    have h := zpow_add_one e (m - 1)
    rw [hdone, one_mul, sub_add_cancel] at h
    exact h
  have hgee : g * e * g⁻¹ = e := by
    rw [hm]
    exact hem
  intro d hd
  obtain ⟨n, hn⟩ := hgen d hd
  rw [← hn, ← conj_zpow, hgee]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
