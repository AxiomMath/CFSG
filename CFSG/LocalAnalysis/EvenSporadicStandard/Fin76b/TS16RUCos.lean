module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUD8

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open Subgroup CFSG.Monster.B.Co2 CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def InCos (k : ℕ) (x : Equiv.Perm (Fin 820)) : Prop := x * (tP k)⁻¹ ∈ P

theorem inCos_iff {k : ℕ} {x : Equiv.Perm (Fin 820)} : InCos k x ↔ ∃ g ∈ P, x = g * tP k := by
  constructor
  · intro h
    exact ⟨x * (tP k)⁻¹, h, by group⟩
  · rintro ⟨g, hg, rfl⟩
    unfold InCos
    simpa using hg

theorem inCos_mul_tP {k : ℕ} {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) : InCos k (g * tP k) :=
  inCos_iff.2 ⟨g, hg, rfl⟩

theorem inCos_zero_iff {x : Equiv.Perm (Fin 820)} : InCos 0 x ↔ x ∈ P := by
  unfold InCos
  rw [tP_zero, inv_one, mul_one]

section Cosets


theorem inCos_mul {j k : ℕ} (hj : j < 8) (hk : k < 8) {x y : Equiv.Perm (Fin 820)}
    (hx : InCos j x) (hy : InCos k y) : InCos (mulTab j k) (x * y) := by
  obtain ⟨g, hg, rfl⟩ := inCos_iff.1 hx
  obtain ⟨g', hg', rfl⟩ := inCos_iff.1 hy
  refine inCos_iff.2 ⟨g * (tP j * g' * (tP j)⁻¹), P.mul_mem hg (tP_normalizes hg'), ?_⟩
  rw [← d8_mul hj hk]
  group

theorem inCos_inv {k : ℕ} (hk : k < 8) {x : Equiv.Perm (Fin 820)} (hx : InCos k x) :
    InCos (invIx k) x⁻¹ := by
  obtain ⟨g, hg, rfl⟩ := inCos_iff.1 hx
  refine inCos_iff.2 ⟨(tP k)⁻¹ * g⁻¹ * tP k, ?_, ?_⟩
  · have := tP_normalizes (k := invIx k) (P.inv_mem hg)
    rwa [← tP_inv_eq hk] at this
  · rw [← tP_inv_eq hk]
    group

theorem inCos_unique {k k' : ℕ} (hk : k < 8) (hk' : k' < 8) {x : Equiv.Perm (Fin 820)}
    (hx : InCos k x) (hx' : InCos k' x) : k = k' := by
  by_contra hne
  apply tP_mul_inv_not_mem hk hk' hne
  have : tP k * (tP k')⁻¹ = (x * (tP k)⁻¹)⁻¹ * (x * (tP k')⁻¹) := by group
  rw [this]
  exact P.mul_mem (P.inv_mem hx) hx'

theorem mem_Ks_iff {x : Equiv.Perm (Fin 820)} :
    x ∈ U43ExtStar ↔ ∃ k, k < 8 ∧ InV k ∧ InCos k x := by
  constructor
  · rintro ⟨g, hg, k, hk, hV, rfl⟩
    exact ⟨k, hk, hV, inCos_mul_tP hg⟩
  · rintro ⟨k, hk, hV, hx⟩
    obtain ⟨g, hg, rfl⟩ := inCos_iff.1 hx
    exact ⟨g, hg, k, hk, hV, rfl⟩

theorem mulTab_V_zero : ∀ k < 8, InV k → mulTab k k = 0 := by decide +kernel

theorem mulTab_conj_V : ∀ j < 8, ∀ k < 8, InV j → InV k → mulTab (mulTab j k) (invIx j) = k := by
  decide +kernel

theorem sq_mem_P {x : Equiv.Perm (Fin 820)} (hx : x ∈ U43ExtStar) : x * x ∈ P := by
  obtain ⟨k, hk, hV, hxk⟩ := mem_Ks_iff.1 hx
  have := inCos_mul hk hk hxk hxk
  rw [mulTab_V_zero k hk hV] at this
  exact inCos_zero_iff.1 this

theorem pow_four_mem_P {x : Equiv.Perm (Fin 820)} (hx : x ∈ U43ExtStar) : x ^ 4 ∈ P := by
  have : x ^ 4 = (x * x) ^ 2 := by rw [← sq, ← pow_mul]
  rw [this]
  exact P.pow_mem (sq_mem_P hx) 2

theorem pow_eight_mem_P {x : Equiv.Perm (Fin 820)} (hx : x ∈ U43ExtStar) : x ^ 8 ∈ P := by
  have : x ^ 8 = (x * x) ^ 4 := by rw [← sq, ← pow_mul]
  rw [this]
  exact P.pow_mem (sq_mem_P hx) 4

theorem inCos_conj {k : ℕ} (hk : k < 8) (hV : InV k) {x y : Equiv.Perm (Fin 820)}
    (hx : x ∈ U43ExtStar) (hy : InCos k y) : InCos k (x * y * x⁻¹) := by
  obtain ⟨j, hj, hjV, hxj⟩ := mem_Ks_iff.1 hx
  have h1 := inCos_mul hj hk hxj hy
  have h2 := inCos_inv hj hxj
  have h3 := inCos_mul (mulTab_lt j k) (invIx_spec j hj).1 h1 h2
  rwa [mulTab_conj_V j hj k hk hjV hV] at h3

end Cosets

end CFSG.EvenSporadicStandard.Fin76b.U16
