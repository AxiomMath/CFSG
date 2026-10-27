module

public import CFSG.GH74.Uniqueness.Section5Basic
public import CFSG.GH74.Uniqueness.Prop38

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type*} [Group X]

theorem omega_conjugate (M : Subgroup X) (g : X) : omega (conjugate M g) = omega M := by
  ext β
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨g * k, by rw [conjugate_conjugate]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨g⁻¹ * k, by rw [conjugate_conjugate, ← mul_assoc, mul_inv_cancel, one_mul]⟩

section Prop38Omega

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.prop38b_omega (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {u : X} (hu : u ∈ Z) {δ β : Subgroup X} (hδ : δ ∈ omega M)
    (huδ : conjugate δ u = δ) (hβ : β ∈ omega M) (hβδ : β ≠ δ) {P : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hPD : P ≤ δ ⊓ β) (hPp : IsPGroup p P)
    (huP : u ∈ normalizer (P : Set X)) :
    Nat.card (CFSG.OddInversion.invertedSet P u) ≤ zNumShare Z M p ∧
      (ABGLocalTools.IsSylowOf p P (δ ⊓ β) →
        Nat.card (CFSG.OddInversion.invertedSet P u) = zNumShare Z M p) := by
  obtain ⟨g, rfl⟩ := hδ
  have h' := h.conjugate_point hZ g
  have huM : u ∈ conjugate M g := (h.conjugate_eq_iff_mem ⟨g, rfl⟩).mp huδ
  have hβ' : β ∈ omega (conjugate M g) := by rw [omega_conjugate]; exact hβ
  have := h'.prop38b hZ hu huM hβ' hβδ hp hp2 hPD hPp huP
  rwa [zNum_conjugate hZ M g] at this

theorem IsProductDisconnected.prop38c_omega (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {u : X} (hu : u ∈ Z) {δ β : Subgroup X} (hδ : δ ∈ omega M)
    (huδ : conjugate δ u = δ) (hβ : β ∈ omega M) (hβδ : β ≠ δ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Subgroup X} (hPD : P ≤ δ ⊓ β) (hPp : IsPGroup p P)
    (huP : u ∈ normalizer (P : Set X))
    (hcard : Nat.card (CFSG.OddInversion.invertedSet P u) = zNumShare Z M p) :
    ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q (δ ⊓ β) ∧ Q ≤ δ ⊓ β ⊓ conjugate β u ∧
      u ∈ normalizer (Q : Set X) := by
  obtain ⟨g, rfl⟩ := hδ
  have h' := h.conjugate_point hZ g
  have huM : u ∈ conjugate M g := (h.conjugate_eq_iff_mem ⟨g, rfl⟩).mp huδ
  have hβ' : β ∈ omega (conjugate M g) := by rw [omega_conjugate]; exact hβ
  have hcard' : Nat.card (CFSG.OddInversion.invertedSet P u) =
      p ^ (zNum Z (conjugate M g)).factorization p := by
    rw [zNum_conjugate hZ M g]
    exact hcard
  exact h'.exists_invariant_sylow_of_card_eq hZ hu huM hβ' hβδ hp hp2 hPD hPp huP hcard'

end Prop38Omega

end CFSG.GH74.Uniqueness
