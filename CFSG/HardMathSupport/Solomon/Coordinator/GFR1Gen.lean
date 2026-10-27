module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem gfr1_mem_sup {Y : Type*} [Group Y] {g : Y} {K : Subgroup Y}
    (hg : ∀ k ∈ K, g * k = k * g) {x : Y} (hx : x ∈ Subgroup.zpowers g ⊔ K) :
    ∃ (i : ℤ) (k : Y), k ∈ K ∧ x = g ^ i * k := by
  have hc : ∀ k ∈ K, ∀ i : ℤ, g ^ i * k = k * g ^ i := fun k hk i =>
    (Commute.zpow_left (show Commute g k from hg k hk) i).eq
  let S : Subgroup Y :=
    { carrier := {x | ∃ (i : ℤ) (k : Y), k ∈ K ∧ x = g ^ i * k}
      one_mem' := ⟨0, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨i, k, hk, rfl⟩ ⟨j, k', hk', rfl⟩
        refine ⟨i + j, k * k', K.mul_mem hk hk', ?_⟩
        rw [zpow_add, mul_assoc, ← mul_assoc k, ← hc k hk j, mul_assoc, mul_assoc]
      inv_mem' := by
        rintro _ ⟨i, k, hk, rfl⟩
        refine ⟨-i, k⁻¹, K.inv_mem hk, ?_⟩
        have := hc k⁻¹ (K.inv_mem hk) (-i)
        rw [mul_inv_rev, this, zpow_neg] }
  have hle : Subgroup.zpowers g ⊔ K ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact ⟨i, 1, K.one_mem, by simp⟩
    · intro k hk
      exact ⟨0, k, hk, by simp⟩
  exact hle hx

theorem gfr1_commutator_le {Y : Type*} [Group Y] {g : Y} {K : Subgroup Y}
    (hg : ∀ k ∈ K, g * k = k * g) :
    ⁅Subgroup.zpowers g ⊔ K, Subgroup.zpowers g ⊔ K⁆ ≤ K := by
  have hc : ∀ k ∈ K, ∀ i : ℤ, g ^ i * k = k * g ^ i := fun k hk i =>
    (Commute.zpow_left (show Commute g k from hg k hk) i).eq
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨i, k, hk, rfl⟩ := gfr1_mem_sup hg hx
  obtain ⟨j, k', hk', rfl⟩ := gfr1_mem_sup hg hy
  have hm : k * k' * k⁻¹ * k'⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
  have key : ⁅g ^ i * k, g ^ j * k'⁆ = k * k' * k⁻¹ * k'⁻¹ := by
    rw [commutatorElement_def]
    have e1 : g ^ i * k * (g ^ j * k') * (g ^ i * k)⁻¹ * (g ^ j * k')⁻¹ =
        g ^ i * g ^ j * (k * k' * k⁻¹) * g ^ (-i) * k'⁻¹ * g ^ (-j) := by
      rw [mul_inv_rev, mul_inv_rev, zpow_neg, zpow_neg, mul_assoc (g ^ i), ← mul_assoc k,
        ← hc k hk j]
      simp only [mul_assoc]
    rw [e1]
    have hm1 : k * k' * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)
    rw [mul_assoc (g ^ i * g ^ j), mul_assoc (g ^ i * g ^ j), ← hc _ hm1 (-i)]
    calc g ^ i * g ^ j * (g ^ (-i) * (k * k' * k⁻¹) * k'⁻¹) * g ^ (-j)
        = g ^ i * g ^ j * (g ^ (-i) * (k * k' * k⁻¹ * k'⁻¹)) * g ^ (-j) := by
          simp only [mul_assoc]
      _ = g ^ i * g ^ j * ((k * k' * k⁻¹ * k'⁻¹) * g ^ (-i)) * g ^ (-j) := by
          rw [hc _ hm (-i)]
      _ = (g ^ (i + j) * (k * k' * k⁻¹ * k'⁻¹)) * g ^ (-i) * g ^ (-j) := by
          rw [zpow_add]; simp only [mul_assoc]
      _ = ((k * k' * k⁻¹ * k'⁻¹) * g ^ (i + j)) * g ^ (-i) * g ^ (-j) := by
          rw [hc _ hm (i + j)]
      _ = (k * k' * k⁻¹ * k'⁻¹) * g ^ (i + j + -i + -j) := by
          simp only [mul_assoc, zpow_add]
      _ = k * k' * k⁻¹ * k'⁻¹ := by
          rw [show i + j + -i + -j = 0 by ring, zpow_zero, mul_one]
  rw [key]
  exact hm

theorem gfr1_components {Y : Type} [Group Y] [Finite Y] {g : Y} {K : Subgroup Y}
    (hC : Subgroup.centralizer ({g} : Set Y) = Subgroup.zpowers g ⊔ K)
    (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 3 (Subgroup.center ↥K))
    (h3 : 3 ∣ Nat.card K) :
    GLAPComponent 3 (Subgroup.centralizer ({g} : Set Y)) K ∧
      ∀ J : Subgroup Y, GLAPComponent 3 (Subgroup.centralizer ({g} : Set Y)) J → J = K := by
  have hKC : K ≤ Subgroup.centralizer ({g} : Set Y) := by rw [hC]; exact le_sup_right
  have hg : ∀ k ∈ K, g * k = k * g := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hgn : g ∈ Subgroup.normalizer (K : Set Y) := by
    refine Subgroup.centralizer_le_normalizer (K : Set Y) ?_
    exact Subgroup.mem_centralizer_iff.2 fun h hh => (hg h hh).symm
  have hn : (K.subgroupOf (Subgroup.centralizer ({g} : Set Y))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKC, hC]
    exact sup_le (Subgroup.zpowers_le.2 hgn) Subgroup.le_normalizer
  refine ⟨Proving.glaPComponent_of_normal_overgroup Nat.prime_three hKC hn
    (on25_glaPComponent_self hq hZ h3), fun J hJ => ?_⟩
  have hperf := glaPComponent_perfect hJ
  have hne := gfr1_component_ne_bot hJ
  obtain ⟨hJC, hsn, -⟩ := hJ
  have hJK : J ≤ K := by
    calc J = ⁅J, J⁆ := hperf.symm
      _ ≤ ⁅Subgroup.centralizer ({g} : Set Y), Subgroup.centralizer ({g} : Set Y)⁆ :=
          Subgroup.commutator_mono hJC hJC
      _ ≤ K := by rw [hC]; exact gfr1_commutator_le hg
  exact gfr1_eq_of_subnormal hq hJK (isSubnormal_of_le_of_le hsn hJK hKC) hperf
    hne

noncomputable def gfr1_barOf_equiv {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 3 (Subgroup.center ↥K))
    (h3 : 3 ∣ Nat.card K) : barOf 3 K ≃* ↥K :=
  (QuotientGroup.quotientMulEquivOfEq (on25_primeCore_eq_bot hq hZ h3)).trans
    QuotientGroup.quotientBot

end CFSG.HardMathSupport.Solomon.Coordinator
