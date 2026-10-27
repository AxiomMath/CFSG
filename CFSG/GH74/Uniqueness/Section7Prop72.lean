module

public import CFSG.GH74.Uniqueness.Section7Prop74
public import CFSG.GH74.Uniqueness.Section7Lemma75
public import CFSG.GH74.Uniqueness.Section7Lemma76

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open Section7Theta

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.lemma77 (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {p : ℕ}
    {Γ : Set (Subgroup X)} {β : Subgroup X} (hβ : β ∈ omega M) (hβM : β ≠ M) {g : X}
    (hg : conjugate (conjugate β z) g = M) (hβ₁ : conjugate β g ∈ Γ)
    (hmin : ∀ γ ∈ Γ, γ ≠ M →
      Nat.card (oPrimePrime p (M ⊓ β)) ≤ Nat.card (oPrimePrime p (M ⊓ γ))) :
    Nat.card (oPrimePrime p (M ⊓ β)) ≤ Nat.card (oPrimePrime p (β ⊓ conjugate β z)) := by
  have hβ₁M : conjugate β g ≠ M := by
    intro heq
    exact h.conjugate_ne_of_ne_self hZ hz hzM hβ hβM
      (conjugate_injective g (heq.trans hg.symm)).symm
  have h1 := hmin _ hβ₁ hβ₁M
  have h2 : conjugate (β ⊓ conjugate β z) g = M ⊓ conjugate β g := by
    rw [conjugate_inf, hg, inf_comm]
  rw [← card_oPrimePrime_conjugate p (β ⊓ conjugate β z) g, h2]
  exact h1

theorem prop72_of_prop74 (hZ : IsInvariantInvolutionSet Z) (h : IsProductDisconnected Z M)
    (h74 : ∀ (z : X) (p : ℕ) (W : Subgroup X), T4Max Z M z p W →
      ∃ Γ : Set (Subgroup X), Prop74Spec Z M z W Γ)
    (hC64 : Cor64Stmt Z M) : Prop72Stmt Z M := by
  intro z p W hW
  obtain ⟨Γ, hΓ⟩ := h74 z p W hW
  have hcand := hW.cand
  have hz := hcand.mem_Z
  have hzM := hcand.mem_M
  have hne : (Γ \ {M}).Nonempty := by
    by_contra hempty
    have hsub : Γ ⊆ {M} := fun x hx => by
      by_contra hxM
      exact hempty ⟨x, hx, hxM⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    have := hΓ.one_lt_ncard
    omega
  obtain ⟨β, ⟨hβΓ, hβM'⟩, hmin⟩ := Set.exists_min_image (Γ \ {M})
    (fun β => Nat.card (oPrimePrime p (M ⊓ β))) (Set.toFinite _) hne
  have hβM : β ≠ M := hβM'
  have hβW : β ∈ omegaFix M (W : Set X) := hΓ.subset hβΓ
  obtain ⟨t, -, -, hK1E, hcent, g, hg, hβg⟩ := hΓ.exists_involution β hβΓ hβM
  have hβz : conjugate β z ∈ Γ := hΓ.conjugate_mem β hβΓ
  have hne' : β ≠ conjugate β z :=
    (h.conjugate_ne_of_ne_self hZ hz hzM hβW.1 hβM).symm
  have hCF := hΓ.centralizer_le β hβΓ (conjugate β z) hβz hne'
  have h75 := h.lemma75 hZ hcand hβW hCF
  have h76 := h.lemma76 hZ hcand hβW hβM (z⁻¹ * t * z) hK1E hcent
  have h77 := h.lemma77 hZ hz hzM hβW.1 hβM hg hβg
    (fun γ hγ hγM => hmin γ ⟨hγ, hγM⟩)
  have heq : oPrimePrime p (β ⊓ conjugate β z) = oPrimePrime p (M ⊓ β) :=
    Subgroup.eq_of_le_of_card_ge (h75.trans h76) h77
  have hzN : z ∈ normalizer (oPrimePrime p (M ⊓ β) : Set X) := by
    rw [← heq]
    exact mem_normalizer_oPrimePrime p (mem_normalizer_inf_conjugate (hZ.mul_self_eq_one hz))
  exact ⟨β, hβW, hβM, (hC64 z p W hcand β hβW hβM hzN).1⟩

theorem ZDSetup.prop72
    (S : ZDSetup X Z M) (hL73 : Lemma73Stmt Z M) (hC64 : Cor64Stmt Z M) :
    Prop72Stmt Z M :=
  prop72_of_prop74 S.invariant S.prodDisc (fun _ _ _ hW => S.prop74 hL73 hW) hC64

end CFSG.GH74.Uniqueness
