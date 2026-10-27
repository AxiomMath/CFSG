module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup
open scoped commutatorElement

structure ThLocalWitness {F : Type*} [Group F] (S A B : Subgroup F) (z : F) : Prop where
  pgroup : IsPGroup 2 S
  index_odd : ¬ 2 ∣ S.index
  z_sq : z ^ 2 = 1
  z_ne_one : z ≠ 1
  z_mem : z ∈ S
  center_le : ∀ x ∈ S, (∀ y ∈ S, x * y = y * x) → x ∈ zpowers z
  mem_A_iff : ∀ x, x ∈ A ↔ x ∈ S ∧ ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S, ∀ s₄ ∈ S,
    ⁅⁅⁅⁅x, s₁⁆, s₂⁆, s₃⁆, s₄⁆ = 1
  A_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  A_sq : ∀ x ∈ A, x ^ 2 = 1
  A_card : Nat.card A = 16
  z_mem_A : z ∈ A
  mem_B_iff : ∀ x, x ∈ B ↔ ∀ a ∈ A, x * a = a * x
  B_card : Nat.card B = 2 ^ 9
  trans : ∀ a ∈ A, a ≠ 1 → ∃ n : F, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ n * z * n⁻¹ = a
  surj : ∀ f : F → F, (∀ a ∈ A, f a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
    (∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) → ∃ n : F, ∀ a ∈ A, n * a * n⁻¹ = f a

variable {F F' : Type*} [Group F] [Group F']

theorem ThLocalWitness.map_equiv (e : F ≃* F') {S A B : Subgroup F'} {z : F'}
    (W : ThLocalWitness S A B z) :
    ThLocalWitness (S.map (e.symm : F' →* F)) (A.map (e.symm : F' →* F))
      (B.map (e.symm : F' →* F)) (e.symm z) := by
  have hmem : ∀ K : Subgroup F', ∀ x : F, x ∈ K.map (e.symm : F' →* F) ↔ e x ∈ K := fun K x => by
    simpa using Subgroup.mem_map_equiv (f := e.symm) (K := K) (x := x)
  have hcomm : ∀ x y : F, e ⁅x, y⁆ = ⁅e x, e y⁆ := fun x y => map_commutatorElement e x y
  refine ⟨W.pgroup.map _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.index_map_equiv]
    exact W.index_odd
  · rw [← map_pow, W.z_sq, map_one]
  · intro h1
    apply W.z_ne_one
    simpa using congrArg e h1
  · exact (hmem S _).2 (by simpa using W.z_mem)
  · intro x hx hc
    rw [hmem] at hx
    have : e x ∈ zpowers z := by
      apply W.center_le _ hx
      intro y' hy'
      have h1 := hc (e.symm y') ((hmem S _).2 (by simpa using hy'))
      have h2 := congrArg e h1
      simpa using h2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
    refine Subgroup.mem_zpowers_iff.2 ⟨k, e.injective ?_⟩
    simpa using hk
  · intro x
    rw [hmem, W.mem_A_iff, hmem]
    refine and_congr_right fun _ => ⟨fun h s₁ hs₁ s₂ hs₂ s₃ hs₃ s₄ hs₄ => ?_, fun h s₁ hs₁ s₂ hs₂
      s₃ hs₃ s₄ hs₄ => ?_⟩
    · rw [hmem] at hs₁ hs₂ hs₃ hs₄
      apply e.injective
      rw [hcomm, hcomm, hcomm, hcomm, map_one]
      exact h _ hs₁ _ hs₂ _ hs₃ _ hs₄
    · have := h (e.symm s₁) ((hmem S _).2 (by simpa using hs₁)) (e.symm s₂)
        ((hmem S _).2 (by simpa using hs₂)) (e.symm s₃) ((hmem S _).2 (by simpa using hs₃))
        (e.symm s₄) ((hmem S _).2 (by simpa using hs₄))
      have h2 := congrArg e this
      rw [hcomm, hcomm, hcomm, hcomm, map_one] at h2
      simpa using h2
  · intro x hx y hy
    rw [hmem] at hx hy
    exact e.injective (by simpa using W.A_comm _ hx _ hy)
  · intro x hx
    rw [hmem] at hx
    exact e.injective (by simpa using W.A_sq _ hx)
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact W.A_card
  · exact (hmem A _).2 (by simpa using W.z_mem_A)
  · intro x
    rw [hmem, W.mem_B_iff]
    refine ⟨fun h a ha => ?_, fun h a ha => ?_⟩
    · rw [hmem] at ha
      exact e.injective (by simpa using h _ ha)
    · have := h (e.symm a) ((hmem A _).2 (by simpa using ha))
      simpa using congrArg e this
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact W.B_card
  · intro a ha ha1
    rw [hmem] at ha
    obtain ⟨n, hn1, hn2⟩ := W.trans (e a) ha (fun h => ha1 (e.injective (by simpa using h)))
    refine ⟨e.symm n, fun x hx => ?_, e.injective (by simpa using hn2)⟩
    rw [hmem] at hx ⊢
    simpa using hn1 _ hx
  · intro f hf1 hf2 hf3
    obtain ⟨n, hn⟩ := W.surj (fun y => e (f (e.symm y)))
      (fun a ha => by
        have := hf1 (e.symm a) ((hmem A _).2 (by simpa using ha))
        rw [hmem] at this
        exact this)
      (fun a ha b hb => by
        have := hf2 (e.symm a) ((hmem A _).2 (by simpa using ha)) (e.symm b)
          ((hmem A _).2 (by simpa using hb))
        simp only [map_mul] at this ⊢
        rw [this, map_mul])
      (fun a ha b hb hab => by
        have := hf3 (e.symm a) ((hmem A _).2 (by simpa using ha)) (e.symm b)
          ((hmem A _).2 (by simpa using hb)) (e.injective hab)
        simpa using congrArg e this)
    refine ⟨e.symm n, fun a ha => ?_⟩
    rw [hmem] at ha
    have := hn (e a) ha
    apply e.injective
    simpa using this

end CFSG.EvenSporadicStandard.ThStd
