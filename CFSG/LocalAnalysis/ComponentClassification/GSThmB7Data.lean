module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Seven

variable {X : Type} [Group X] [Finite X]

abbrev B0 (h : Hyp52 X) (y : X) : Subgroup X := h.B ⊓ conjugate h.B y

abbrev Lay (h : Hyp52 X) (y : X) : Subgroup X := layerIn (centralizer (B0 h y : Set X))

structure Data (X : Type) [Group X] [Finite X] where
  h : Hyp52 X
  y : X
  z : X
  hT : h.T = h.B ⊔ zpowers h.a
  hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a
  hJn : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X)
  hSa : IsSylowIn h.S (centralizer ({h.a} : Set X))
  hDP : h.D ⊓ h.P = ⊥
  hyP : y ∈ h.P
  hyT : y ∉ h.T
  hy2 : y ^ 2 ∈ h.T
  hyQ : y ∈ normalizer (h.Q : Set X)
  hQ : h.Q ≤ normalizer (B0 h y : Set X)
  h61 : h.Lemma61Shape y
  hS0E : h.S ⊓ normalizer (B0 h y : Set X) ≤
    centralizer ((zpowers h.a ⊔ ⁅h.B, zpowers y⁆ : Subgroup X) : Set X)
  hBL : ∃ β ∈ h.B, β ∈ Lay h y ∧ β ∉ B0 h y
  hB0L : B0 h y ⊓ Lay h y = ⊥
  hzD : z ∈ h.D
  hzS : ∀ t ∈ h.S, t * z = z * t
  hz2 : orderOf z = 2
  hconj : ∀ c ∈ B0 h y, c * c = 1 → h.a * c ∈ Lay h y →
    ∃ r ∈ Lay h y, r * r = 1 ∧ r⁻¹ * (h.a * c) * r = z
  hout : ∀ c ∈ B0 h y, c * c = 1 → h.a * c ∈ Lay h y → ∃ s ∈ h.S, s ∈ Lay h y ∧
    ∀ w ∈ h.S, (∀ d ∈ h.D, w * d = d * w) → w * s = s * w → w ∈ h.P ∨ z * w ∈ h.P

end Seven

end CFSG.ComponentClassification.GSThmB
