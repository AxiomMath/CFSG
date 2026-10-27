module

public import CFSG.LocalAnalysis.OddStandard.Seitz77V1ActCertified

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

structure PlaneData {G : Type} [Group G] {A : Subgroup G} (d : Datum A) (W : Subgroup G) where
  norm_le : normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (W : Set G)
  X : Subgroup G
  Q : Subgroup G
  O : Subgroup G
  reg : IsRegularNormal (W ⊔ zpowers d.t : Subgroup G) d.t X
  X_cent : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ = w
  Q_syl : IsSylowOf 2 Q X
  E_lt : (W ⊔ zpowers d.t : Subgroup G) < Q
  O_odd : Odd (Nat.card O)
  O_norm : ∀ n ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G), ∀ o ∈ O, n * o * n⁻¹ ∈ O
  O_sup : O ⊔ (W ⊔ zpowers d.t : Subgroup G) = centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G)
  QO_sup : Q ⊔ O = X
  QO_inf : Q ⊓ O = ⊥

section Plane

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ W : Subgroup G}

theorem Hyp.exists_PlaneData
    (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) : Nonempty (PlaneData d W) := by
  obtain ⟨X, Q, O, hX, hQ, hEQ, hO, hOn, hOs, hQO, hQOi⟩ :=
    h.exists_regularNormal_sylow_oddComplement_of_certificate d hR hW
  have hcent : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ = w :=
    h.facts.regularNormal_le_centralizer d hR (alpha_of_certificates h d) hW (h.aSide d hR hW) hX
  exact ⟨⟨h.normalizer_adj_le d hR hW, X, Q, O, hX, hcent, hQ, hEQ, hO, hOn, hOs, hQO, hQOi⟩⟩

end Plane

end CFSG.OddStandard.Seitz77
