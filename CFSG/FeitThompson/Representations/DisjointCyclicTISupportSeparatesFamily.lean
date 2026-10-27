module

public import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.SmallCharactersPerpendicularCyclicTIArray
public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace DisjointCoherentFamilies

open CrossFamilyProjection (coherentImage coherentImage_apply)
open scoped ComplexConjugate

namespace IsFullCoherentFamily

variable {G : Type*} [Group G] [Fintype G] {L : Type*} [Group L] [Fintype L]
  {ι : Type*} {ξ : ι → (L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {D : Set G}
  {W W1 W2 : Subgroup G} [Fintype ↥W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem star_coherentVal (h : IsFullCoherentFamily ξ τ ν D) (χ : Set.range ξ) :
    coherentVal ν (starElem h.star_mem χ) = star (coherentVal ν χ) := by
  obtain ⟨k, -⟩ := χ.2
  exact coherentVal_starElem h.subset_Irr (h.two_le_ncard k) h.star_mem h.star_ne
    h.apply_one_eq_zero h.star_tau' h.isCoherentWith χ

theorem star_coherentVal_ne (h : IsFullCoherentFamily ξ τ ν D) (χ : Set.range ξ) :
    star (coherentVal ν χ) ≠ coherentVal ν χ := by
  rw [← h.star_coherentVal χ]
  intro hc
  have h2 := congrArg Subtype.val (coherentVal_injective h.isCoherentWith hc)
  rw [coe_starElem] at h2
  exact h.star_ne _ χ.2 h2

theorem isOrthogonal_coherentVal_apply (h : IsFullCoherentFamily ξ τ ν D)
    (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (hτV : ∀ f : charSpanZero (Set.range ξ), ∀ v ∈ cyclicTIDiff W W1 W2, (τ f : G → ℂ) v = 0)
    (χ : Set.range ξ) {ψ : classFun ↥W} (hψ : (ψ : ↥W → ℂ) ∈ Irr ↥W) :
    IsOrthogonal (coherentVal ν χ) (σ ψ : G → ℂ) := by
  have hρ : coherentVal ν χ ∈ signedIrr G :=
    coherentVal_mem_signedIrr h.subset_Irr h.isCoherentWith χ
  have hconj : (fun x => conj (coherentVal ν χ x)) = star (coherentVal ν χ) := by
    funext x
    simp [Pi.star_apply]
  have hnr : coherentVal ν χ ≠ fun x => conj (coherentVal ν χ x) := by
    rw [hconj]
    exact fun hc => h.star_coherentVal_ne χ hc.symm
  have hsub : coherentVal ν χ - star (coherentVal ν χ)
      = (τ ⟨(χ : L → ℂ) - star (χ : L → ℂ),
          sub_star_mem_charSpanZero h.subset_Irr h.star_mem χ.2⟩ : G → ℂ) := by
    rw [← h.star_coherentVal χ]
    exact coherentVal_sub_coherentVal_starElem h.subset_Irr h.star_mem h.isCoherentWith χ
  have hρ0 : ∀ x ∈ cyclicTIDiff W W1 W2,
      (coherentVal ν χ - fun y => conj (coherentVal ν χ y)) x = 0 := by
    intro x hx
    have he : (coherentVal ν χ - fun y => conj (coherentVal ν χ y))
        = coherentVal ν χ - star (coherentVal ν χ) := by rw [hconj]
    rw [he, hsub]
    exact hτV _ x hx
  exact hW.isOrthogonal_apply_of_ne_conj hσ hρ hnr hρ0 hψ

theorem isOrthogonal_coherentImage_apply (h : IsFullCoherentFamily ξ τ ν D)
    (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (hτV : ∀ f : charSpanZero (Set.range ξ), ∀ v ∈ cyclicTIDiff W W1 W2, (τ f : G → ℂ) v = 0)
    (k : ι) {ψ : classFun ↥W} (hψ : (ψ : ↥W → ℂ) ∈ Irr ↥W) :
    IsOrthogonal (coherentImage ξ ν k) (σ ψ : G → ℂ) := by
  have hk := h.isOrthogonal_coherentVal_apply hW hσ hτV ⟨ξ k, ⟨k, rfl⟩⟩ hψ
  rwa [coherentVal_apply, ← coherentImage_apply] at hk

end IsFullCoherentFamily

section Bridge

variable {G : Type*} [Group G] [Fintype G] {Lsub : Subgroup G} [Fintype ↥Lsub] {A : Set G}
  {J : G → Subgroup G} {H : Subgroup ↥Lsub} {κ : Type*} {ζ : κ → (↥Lsub → ℂ)}
  {t : charSpanZero (Set.range ζ) →+ virtualChars G}
  {μ : Submodule.span ℤ (Set.range ζ) →+ virtualChars G}
  {W W1 W2 : Subgroup G} [Fintype ↥W] {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem isOrthogonal_coherentVal_apply_of_isDadeData [H.Normal] (hodd : Odd (Nat.card G))
    (hD : IsDadeData Lsub A J)
    (hA : A = (fun x : ↥Lsub => (x : G)) '' ((H : Set ↥Lsub) \ {1}))
    (hS : Set.range ζ = indFam H (Irr ↥H \ {1})) (hIrr : Set.range ζ ⊆ Irr ↥Lsub)
    (ht : ∀ (f : charSpanZero (Set.range ζ)) (hf : (f : ↥Lsub → ℂ) ∈ dadeDomain Lsub A),
      (t f : G → ℂ) = ((dadeMap hD ⟨(f : ↥Lsub → ℂ), hf⟩ : classFun G) : G → ℂ))
    (hμ : IsCoherentWith (Set.range ζ) t μ)
    (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (hV : ∀ F : dadeDomain Lsub A, ∀ v ∈ cyclicTIDiff W W1 W2,
      ((dadeMap hD F : classFun G) : G → ℂ) v = 0)
    (χ : Set.range ζ) {ψ : classFun ↥W} (hψ : (ψ : ↥W → ℂ) ∈ Irr ↥W) :
    IsOrthogonal (coherentVal μ χ) (σ ψ : G → ℂ) := by
  refine (isFullCoherentFamily_of_isDadeData hodd hD hA hS hIrr ht
    hμ).isOrthogonal_coherentVal_apply hW hσ (fun f v hv => ?_) χ hψ
  rw [ht f (mem_dadeDomain_of_charSpanZero hA hS f)]
  exact hV _ v hv

end Bridge

end DisjointCoherentFamilies

end CFSG.FeitThompson
