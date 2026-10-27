module

public import Mathlib.Dynamics.PeriodicPts.Defs

public section

namespace CFSG.HardMathSupport.C14Idx

open scoped Function

theorem mem_range_image_iterate {X : Type*} [DecidableEq X] {θ : X → X} {α : X} {n i : ℕ}
    (hi : i < n) : (θ)^[i] α ∈ (Finset.range n).image fun j => (θ)^[j] α :=
  Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩

theorem range_image_iterate_subset {X : Type*} [DecidableEq X] {θ : X → X} {D : Finset X}
    (h : Set.MapsTo θ (D : Set X) (D : Set X)) {α : X} (hα : α ∈ D) (n : ℕ) :
    (Finset.range n).image (fun i => (θ)^[i] α) ⊆ D := by
  intro β hβ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hβ
  exact h.iterate i hα

theorem range_image_iterate_card {X : Type*} [DecidableEq X] {θ : X → X} {α : X} {n : ℕ}
    (hnα : (θ)^[n] α = α) (hmin : ∀ m, 0 < m → m < n → (θ)^[m] α ≠ α) :
    ((Finset.range n).image fun i => (θ)^[i] α).card = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hper : Function.IsPeriodicPt θ n α := hnα
  have hminper : n = Function.minimalPeriod θ α := by
    apply le_antisymm
    · by_contra h
      have hpos : 0 < Function.minimalPeriod θ α := hper.minimalPeriod_pos hn
      exact hmin _ hpos (by omega) (Function.isPeriodicPt_minimalPeriod θ α)
    · exact hper.minimalPeriod_le hn
  rw [hminper, Finset.card_image_of_injOn]
  · simp
  · simpa [Finset.coe_range] using Function.iterate_injOn_Iio_minimalPeriod

theorem range_image_iterate_stable {X : Type*} [DecidableEq X] {θ : X → X} {α : X} {n : ℕ}
    (hn : 0 < n) (hnα : (θ)^[n] α = α) :
    ∀ β ∈ (Finset.range n).image (fun i => (θ)^[i] α), θ β ∈
      (Finset.range n).image fun i => (θ)^[i] α := by
  intro β hβ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hβ
  have hi' : i < n := Finset.mem_range.1 hi
  by_cases hlt : i + 1 < n
  · simpa [Function.iterate_succ_apply'] using mem_range_image_iterate (θ := θ) (α := α) hlt
  · have hile : i.succ = n := by omega
    have heq : θ ((θ)^[i] α) = (θ)^[n] α := by
      rw [← Function.iterate_succ_apply' (θ) i α, hile]
    rw [heq, hnα]
    exact mem_range_image_iterate (θ := θ) (α := α) hn

theorem mem_range_image_iterate_of_theta_mem {X : Type*} [DecidableEq X] {θ : X → X}
    {D : Finset X} (hD : Set.MapsTo θ (D : Set X) (D : Set X))
    (hθinj : Set.InjOn θ (D : Set X))
    {α : X} {n : ℕ} (hn : 0 < n) (hnα : (θ)^[n] α = α)
    (hαD : α ∈ D) {β : X} (hβD : β ∈ D)
    (hβ : θ β ∈ (Finset.range n).image fun i => (θ)^[i] α) :
    β ∈ (Finset.range n).image fun i => (θ)^[i] α := by
  obtain ⟨i, hi, hieq⟩ := Finset.mem_image.1 hβ
  have hi' : i < n := Finset.mem_range.1 hi
  rcases i with _ | j
  · have hβeq : β = (θ)^[n - 1] α := by
      apply hθinj hβD (hD.iterate (n - 1) hαD)
      have hn1 : (n - 1).succ = n := Nat.sub_one_add_one hn.ne'
      rw [← Function.iterate_succ_apply' (θ) (n - 1) α, hn1, hnα]
      exact hieq.symm
    rw [hβeq]
    exact mem_range_image_iterate (by omega)
  · have hβeq : β = (θ)^[j] α := by
      apply hθinj hβD (hD.iterate j hαD)
      simpa [Function.iterate_succ_apply'] using hieq.symm
    rw [hβeq]
    exact mem_range_image_iterate (by omega)

end CFSG.HardMathSupport.C14Idx
