module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

@[expose] def InvolutionFixesElem (K : Type*) [Group K] (n : ℕ) : Prop :=
  ∀ α : MulAut K, α ≠ 1 → α * α = 1 → ∃ E : Subgroup K, (∀ x ∈ E, α x = x) ∧
    (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ n ≤ Nat.card E

theorem false_of_second_copy {L K N : Subgroup G} {t : G} {b n : ℕ} (hbn : b < n)
    (ht2 : t * t = 1)
    (hCt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKq : CFSG.IsQuasisimple ↥K)
    (hΛs : Group.IsSolvable ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G)))
    (hΛr : ∀ E : Subgroup G, E ≤ normalizer (L : Set G) ⊓ centralizer (K : Set G) →
      (∀ x ∈ E, x * x = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ b)
    (hrank : InvolutionFixesElem ↥K n) (hN : N ≤ centralizer (K : Set G)) (e : N ≃* K)
    (htN : t ∈ normalizer (N : Set G)) : False := by
  have hΛ : ∀ n ∈ N, t * n * t⁻¹ = n →
      n ∈ normalizer (L : Set G) ⊓ centralizer (K : Set G) := by
    intro n hn hnt
    refine ⟨hCt (mem_centralizer_singleton_iff.2 ?_), hN hn⟩
    calc n * t = (t * n * t⁻¹) * t := by rw [hnt]
      _ = t * n := by group
  have hNq : CFSG.IsQuasisimple ↥N := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq
  by_cases hall : ∀ n ∈ N, t * n * t⁻¹ = n
  · have hNΛ : N ≤ normalizer (L : Set G) ⊓ centralizer (K : Set G) := fun n hn =>
      hΛ n hn (hall n hn)
    have hsolv : Group.IsSolvable ↥N :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNΛ)
        (Subgroup.inclusion_injective hNΛ)
    have := CFSG.LocalCores.isQuasisimple_nontrivial hNq
    have : Group.IsPerfect ↥N := hNq.1
    exact Group.IsPerfect.not_isSolvable ↥N hsolv
  · push Not at hall
    obtain ⟨n₀, hn₀, hn₀t⟩ := hall
    set α : MulAut ↥N := Subgroup.normalizerMonoidHom N ⟨t, htN⟩ with hα
    have hαapp : ∀ n : ↥N, ((α n : ↥N) : G) = t * n * t⁻¹ := fun n =>
      Subgroup.normalizerMonoidHom_apply_apply_coe N ⟨t, htN⟩ n
    set α' : MulAut ↥K := MulAut.congr e α with hα'
    have hα1 : α ≠ 1 := by
      intro h1
      apply hn₀t
      have := hαapp ⟨n₀, hn₀⟩
      rw [h1] at this
      exact this.symm
    have hα'1 : α' ≠ 1 := by
      intro h1
      apply hα1
      apply (MulAut.congr e).injective
      rw [← hα', h1, map_one]
    have hαα : α * α = 1 := by
      have : (⟨t, htN⟩ : ↥(normalizer (N : Set G))) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
      rw [hα, ← map_mul, this, map_one]
    have hα'α' : α' * α' = 1 := by
      rw [hα', ← map_mul, hαα, map_one]
    obtain ⟨E, hEfix, hE2, hEc, hEn⟩ := hrank α' hα'1 hα'α'
    let E' : Subgroup G := (E.map e.symm.toMonoidHom).map N.subtype
    have hE'mem : ∀ x ∈ E', ∃ k ∈ E, x = ((e.symm k : ↥N) : G) := by
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    have hE'fix : ∀ k ∈ E, t * ((e.symm k : ↥N) : G) * t⁻¹ = ((e.symm k : ↥N) : G) := by
      intro k hk
      have h1 : α (e.symm k) = e.symm k := by
        have h2 : α' k = e (α (e.symm k)) := by
          rw [hα', MulAut.congr_apply]
          rfl
        have h3 := hEfix k hk
        rw [h2] at h3
        exact e.injective (by simpa using h3)
      rw [← hαapp, h1]
    have hE'Λ : E' ≤ normalizer (L : Set G) ⊓ centralizer (K : Set G) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := hE'mem x hx
      exact hΛ _ (e.symm k).2 (hE'fix k hk)
    have hcard : Nat.card E' = Nat.card E := by
      rw [Subgroup.card_map_of_injective N.subtype_injective,
        Subgroup.card_map_of_injective e.symm.injective]
    have h8 := hΛr E' hE'Λ
      (by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := hE'mem x hx
        have := hE2 k hk
        have h4 : (e.symm k) * (e.symm k) = 1 := by
          rw [← map_mul, this, map_one]
        exact congrArg Subtype.val h4)
      (by
        intro x hx y hy
        obtain ⟨k, hk, rfl⟩ := hE'mem x hx
        obtain ⟨l, hl, rfl⟩ := hE'mem y hy
        have h4 : (e.symm k) * (e.symm l) = (e.symm l) * (e.symm k) := by
          rw [← map_mul, ← map_mul, hEc k hk l hl]
        exact congrArg Subtype.val h4)
    omega

end CFSG.EvenSporadicStandard.Solomon78
