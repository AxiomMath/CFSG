module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem fzr_isSylowOf_S {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : Ctx0 t L S x₁ x₂ lam rho) : IsSylowOf 2 S (invCent t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_iff.mpr ⟨h.le_invCent, h.isPGroup, h.relIndex_odd⟩

theorem fzr_T2_inf_cent {t : G} {S T₂ : Subgroup G} (hS : IsSylowOf 2 S (invCent t))
    (hT₂ : IsPGroup 2 T₂) (hST : S ≤ T₂) : T₂ ⊓ invCent t = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hS.eq_of_le (le_inf hST hS.le) inf_le_right (hT₂.to_le inf_le_left)

theorem fzr_transport {t u : G} {S T₂ : Subgroup G} (hS : IsSylowOf 2 S (invCent t))
    (hT₂ : IsPGroup 2 T₂) (hST : S ≤ T₂) (hu : ∃ h : G, h⁻¹ * t * h = u) :
    ∃ g : G, g⁻¹ * u * g = t ∧ ∀ c ∈ T₂ ⊓ invCent u, g⁻¹ * c * g ∈ S := by
  obtain ⟨h, hh⟩ := hu
  have heq : T₂ ⊓ invCent t = S := fzr_T2_inf_cent hS hT₂ hST
  have hv : IsSylowOf 2 (T₂ ⊓ centralizer ({t} : Set G)) (centralizer ({t} : Set G)) := by
    have h1 : T₂ ⊓ centralizer ({t} : Set G) = S := heq
    rw [h1]
    exact hS
  obtain ⟨g, hg1, hg2⟩ := CFSG.ComponentClassification.GHarris.exists_conj_extremal hT₂ hv hh
  refine ⟨g, hg1, fun c hc => ?_⟩
  have h3 : g⁻¹ * c * g ∈ T₂ ⊓ invCent t := hg2 c hc
  rwa [heq] at h3

theorem fzr_card_cent_le {t u : G} {S T₂ : Subgroup G} (hS : IsSylowOf 2 S (invCent t))
    (hT₂ : IsPGroup 2 T₂) (hST : S ≤ T₂) (hu : ∃ h : G, h⁻¹ * t * h = u) :
    Nat.card ↥(T₂ ⊓ invCent u) ≤ Nat.card ↥S := by
  obtain ⟨g, -, hg⟩ := fzr_transport hS hT₂ hST hu
  have hinj : Function.Injective
      (fun c : ↥(T₂ ⊓ invCent u) => (⟨g⁻¹ * (c : G) * g, hg c c.2⟩ : ↥S)) := by
    intro a b hab
    have h1 : g⁻¹ * (a : G) * g = g⁻¹ * (b : G) * g := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  exact Nat.card_le_card_of_injective _ hinj

end CFSG.OddStandard.SmallF3.FritzII
