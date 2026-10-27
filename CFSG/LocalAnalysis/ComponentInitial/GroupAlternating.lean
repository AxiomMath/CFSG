module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Equiv Equiv.Perm Subgroup

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {p : ℕ}

theorem cycleType_eq_of_orderOf_eq [Fact p.Prime] (hΩ : Fintype.card Ω = p + 1)
    {σ : Perm Ω} (hσ : orderOf σ = p) : σ.cycleType = {p} := by
  have hprime : (orderOf σ).Prime := hσ ▸ Fact.out
  obtain ⟨n, hn⟩ := cycleType_prime_order hprime
  rw [hσ] at hn
  have hsum := sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hle : σ.support.card ≤ p + 1 := hΩ ▸ Finset.card_le_univ _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : 2 * p ≤ (n + 1) * p := Nat.mul_le_mul_right p (by omega)
    omega
  rw [hn, hn0]
  rfl

theorem centralizer_singleton_eq [Fact p.Prime] (hΩ : Fintype.card Ω = p + 1)
    {σ : Perm Ω} (hσ : orderOf σ = p) : centralizer {σ} = zpowers σ := by
  have hct := cycleType_eq_of_orderOf_eq hΩ hσ
  have hcard : Nat.card (centralizer {σ}) = p := by
    rw [nat_card_centralizer, hct, hΩ]
    simp
  have hle : zpowers σ ≤ centralizer {σ} := by
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, Nat.card_zpowers, hσ]

theorem sign_eq_neg_one_of_conj_eq_inv [Fact p.Prime] (hp4 : p % 4 = 3)
    (hΩ : Fintype.card Ω = p + 1) {σ h : Perm Ω} (hσ : orderOf σ = p)
    (hh : h * σ * h⁻¹ = σ⁻¹) : sign h = -1 := by
  have hp : p.Prime := Fact.out
  have hct := cycleType_eq_of_orderOf_eq hΩ hσ
  have hcyc : σ.IsCycle := card_cycleType_eq_one.mp (by rw [hct]; rfl)
  have hsupp : σ.support.card = p := by
    rw [← sum_cycleType, hct, Multiset.sum_singleton]
  have hsign : sign σ = 1 := by
    rw [hcyc.sign, hsupp, (hp.eq_two_or_odd'.resolve_left (by omega)).neg_one_pow, neg_neg]
  have hcompl : σ.supportᶜ.card = 1 := by
    rw [Finset.card_compl, hsupp, hΩ, Nat.add_sub_cancel_left]
  obtain ⟨ω, hω⟩ := Finset.card_eq_one.mp hcompl
  have hfixed : ∀ y, σ y = y → y = ω := fun y hy => by
    have : y ∈ σ.supportᶜ := Finset.mem_compl.mpr (notMem_support.mpr hy)
    rwa [hω, Finset.mem_singleton] at this
  obtain ⟨x, hx⟩ := hcyc.nonempty_support
  have hσx : σ x ≠ x := mem_support.mp hx
  have hrel : ∀ y, σ⁻¹ (h y) = h (σ y) := fun y => by
    rw [← hh]
    simp [Perm.mul_apply]
  have hhx : σ (h x) ≠ h x := by
    intro heq
    apply hσx
    apply h.injective
    rw [← hrel x, Perm.inv_eq_iff_eq, heq]
  obtain ⟨c, hc⟩ := hcyc.exists_pow_eq hσx hhx
  set k := (σ ^ c)⁻¹ * h with hk
  have hkx : k x = x := by
    rw [hk, Perm.mul_apply, ← hc]
    exact Perm.inv_eq_iff_eq.mpr rfl
  have hkσ : k * σ * k⁻¹ = σ⁻¹ := by
    rw [hk, mul_inv_rev, inv_inv]
    calc (σ ^ c)⁻¹ * h * σ * (h⁻¹ * σ ^ c) = (σ ^ c)⁻¹ * (h * σ * h⁻¹) * σ ^ c := by group
      _ = σ⁻¹ := by rw [hh]; group
  have hsignk : sign k = sign h := by
    rw [hk, map_mul, map_inv, map_pow, hsign, one_pow, inv_one, one_mul]
  have hkpow : ∀ j : ℤ, k ((σ ^ j) x) = (σ ^ (-j)) x := fun j => by
    have h1 : k * σ ^ j * k⁻¹ = σ ^ (-j) := by
      rw [← conj_zpow, hkσ, inv_zpow, zpow_neg]
    calc k ((σ ^ j) x) = (k * σ ^ j * k⁻¹) (k x) := by simp [Perm.mul_apply]
      _ = (σ ^ (-j)) x := by rw [h1, hkx]
  have hkfix : ∀ y, σ y = y → k y = y := fun y hy => by
    have h2 : σ⁻¹ (k y) = k y := by
      have h3 : σ⁻¹ (k y) = k (σ y) := by
        rw [← hkσ]
        simp [Perm.mul_apply]
      rw [h3, hy]
    have h1 : σ (k y) = k y := by
      conv_lhs => rw [← h2]
      exact (Equiv.eq_symm_apply σ).mp rfl
    rw [hfixed _ h1, hfixed _ hy]
  have hcover : ∀ y, σ y ≠ y → ∃ i : ℕ, (σ ^ i) x = y := fun y hy =>
    hcyc.exists_pow_eq hσx hy
  have hk2 : k ^ 2 = 1 := by
    ext y
    rw [Perm.one_apply, sq, Perm.mul_apply]
    by_cases hy : σ y = y
    · rw [hkfix y hy, hkfix y hy]
    · obtain ⟨i, rfl⟩ := hcover y hy
      rw [← zpow_natCast, hkpow, hkpow, neg_neg]
  have hsuppk : k.support = σ.support.erase x := by
    ext y
    rw [mem_support, Finset.mem_erase, mem_support]
    constructor
    · intro hky
      refine ⟨fun hyx => hky (hyx ▸ hkx), fun hy => hky (hkfix y hy)⟩
    · rintro ⟨hyx, hy⟩ hky
      obtain ⟨i, rfl⟩ := hcover y hy
      apply hyx
      rw [← zpow_natCast, hkpow] at hky
      have h2 : (σ ^ (2 * (i : ℤ))) x = x := by
        have h3 := congrArg (σ ^ (i : ℤ)) hky
        rw [← Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Perm.one_apply,
          ← Perm.mul_apply, ← zpow_add, ← two_mul] at h3
        exact h3.symm
      have h4 : σ ^ (2 * i) = 1 := by
        rw [hcyc.pow_eq_one_iff]
        exact ⟨x, hσx, by exact_mod_cast h2⟩
      have h5 : p ∣ 2 * i := hσ ▸ orderOf_dvd_of_pow_eq_one h4
      have h6 : p ∣ i := (Nat.Coprime.dvd_mul_left
        ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))).mp h5
      rw [← hσ] at h6
      rw [orderOf_dvd_iff_pow_eq_one.mp h6, Perm.one_apply]
  have hcardk : k.support.card = p - 1 := by
    rw [hsuppk, Finset.card_erase_of_mem hx, hsupp]
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, support_one, Finset.card_empty] at hcardk
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hok : orderOf k = 2 := orderOf_eq_prime hk2 hk1
  obtain ⟨m, hm⟩ := cycleType_prime_order (hok ▸ Nat.prime_two : (orderOf k).Prime)
  rw [hok] at hm
  have hsumk := sum_cycleType k
  rw [hm, Multiset.sum_replicate, smul_eq_mul, hcardk] at hsumk
  rw [← hsignk, sign_of_cycleType, hm, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul]
  apply Odd.neg_one_pow
  refine ⟨3 * ((p - 3) / 4) + 1, ?_⟩
  omega

theorem normalizer_inf_eq_and_centralizer_inf_eq (hp : p.Prime) (hp4 : p % 4 = 3)
    (hΩ : Fintype.card Ω = p + 1) {Y P : Subgroup (Perm Ω)} (hY : Y ≤ alternatingGroup Ω)
    (hPY : P ≤ Y) (hP : Nat.card P = p) (hgcd : Nat.gcd (Nat.card Y) (p - 1) ∣ 2) :
    Y ⊓ normalizer (P : Set (Perm Ω)) = P ∧ Y ⊓ centralizer (P : Set (Perm Ω)) = P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := P) p (hP ▸ dvd_rfl)
  set σ : Perm Ω := (s : Perm Ω) with hσdef
  have hσ : orderOf σ = p := by rw [hσdef, orderOf_coe, hs]
  have hσP : σ ∈ P := s.2
  have hPσ : zpowers σ = P := by
    refine eq_of_le_of_card_ge ((zpowers_le).mpr hσP) ?_
    rw [hP, Nat.card_zpowers, hσ]
  have hCσ : centralizer {σ} = P := (centralizer_singleton_eq hΩ hσ).trans hPσ
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    rw [← hPσ]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self σ i j).eq
  have hcent : Y ⊓ centralizer (P : Set (Perm Ω)) = P := by
    refine le_antisymm (fun h hh => ?_) (le_inf hPY fun x hx => mem_centralizer_iff.mpr
      fun y hy => hcomm y hy x hx)
    rw [← hCσ]
    exact centralizer_le (Set.singleton_subset_iff.mpr hσP) hh.2
  refine ⟨le_antisymm (fun h hh => ?_) (le_inf hPY (le_normalizer)), hcent⟩
  set N := Y ⊓ normalizer (P : Set (Perm Ω)) with hN
  let f : N →* MulAut P := P.normalizerMonoidHom.comp (inclusion inf_le_right)
  have hfker : ∀ n : N, f n = 1 → (n : Perm Ω) ∈ centralizer (P : Set (Perm Ω)) := by
    intro n hn
    have hmem : inclusion inf_le_right n ∈ P.normalizerMonoidHom.ker := hn
    rw [normalizerMonoidHom_ker, mem_subgroupOf] at hmem
    exact hmem
  have : IsCyclic P := isCyclic_of_prime_card hP
  have hrange : Nat.card f.range ∣ 2 := by
    refine (Nat.dvd_gcd ?_ ?_).trans hgcd
    · rw [← index_ker]
      exact (index_dvd_card _).trans (card_dvd_of_le inf_le_left)
    · have h1 := card_subgroup_dvd_card f.range
      rwa [IsCyclic.card_mulAut, hP, Nat.totient_prime hp] at h1
  have hsq : f ⟨h, hh⟩ ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard f.range ⟨⟨h, hh⟩, rfl⟩).trans hrange)
  have hh2 : h ^ 2 ∈ centralizer (P : Set (Perm Ω)) := by
    rw [← map_pow] at hsq
    exact hfker _ hsq
  have hconj : h * σ * h⁻¹ ∈ zpowers σ := hPσ ▸ (mem_normalizer_iff.mp hh.2 σ).mp hσP
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hconj
  have hkk : σ ^ (k * k) = σ := by
    have h2 : h * h * σ * (h * h)⁻¹ = σ := by
      rw [← sq, ← mem_centralizer_iff.mp hh2 σ hσP, mul_inv_cancel_right]
    calc σ ^ (k * k) = (h * σ * h⁻¹) ^ k := by rw [zpow_mul, hk]
      _ = h * (h * σ * h⁻¹) * h⁻¹ := by rw [conj_zpow, hk]
      _ = h * h * σ * (h * h)⁻¹ := by group
      _ = σ := h2
  have hkmod : (k : ZMod p) * k = 1 := by
    have h1 : σ ^ (k * k - 1) = 1 := by rw [zpow_sub, hkk, zpow_one, mul_inv_cancel]
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * k - 1) p).mpr
      (hσ ▸ orderOf_dvd_iff_zpow_eq_one.mpr h1)
    push_cast at h2
    exact sub_eq_zero.mp h2
  rcases mul_self_eq_one_iff.mp hkmod with hk1 | hk1
  ·
    have hσk : σ ^ k = σ ^ (1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hσ, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      exact hk1
    rw [zpow_one] at hσk
    rw [← hCσ, mem_centralizer_singleton_iff]
    rw [hσk] at hk
    calc h * σ = h * σ * h⁻¹ * h := by group
      _ = σ * h := by rw [← hk]
  ·
    have hσk : σ ^ k = σ ^ (-1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hσ, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      exact hk1
    rw [zpow_neg_one] at hσk
    rw [hσk] at hk
    have hsign := sign_eq_neg_one_of_conj_eq_inv hp4 hΩ hσ hk.symm
    have halt := mem_alternatingGroup.mp (hY hh.1)
    rw [hsign] at halt
    exact absurd halt (by decide)

end CFSG.LocalAnalysis.ComponentInitial
