module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallPull

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

variable (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) (hk : 4 ∣ orderOf c)
include hD hk

theorem le_normalizer_zpowers_c (hcD : c ∈ D) :
    normalizer (D : Set G) ≤ normalizer (zpowers c : Set G) := fun t ht =>
  mem_normalizer_zpowers (conj_c_mem hD hk ht hcD) (by
    have h1 := conj_c_mem hD hk (inv_mem ht) hcD
    rwa [inv_inv] at h1)

end CFSG.ComponentClassification.Foote5.HallGen
