module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CenterData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def CF23L34Socle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → IsSimpleGroup ↥N →
    centralizer (N : Set G) = ⊥ → GSRestricted ↥N →
    ∀ (α : G) (J : Subgroup G), orderOf α = 2 → J ≤ N →
      J ≤ centralizer ({α} : Set G) → IsComponent (J.subgroupOf (centralizer ({α} : Set G))) →
      Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 3 2 2 →
      (Nonempty (↥N ≃* Blueprint.NativeSporadic.He) ∨
        α ∈ N ∧ (Nonempty (↥N ≃* Blueprint.NativeSporadic.Suz) ∨
          Nonempty (↥N ≃* Blueprint.NativeSporadic.ON))) ∨
        (Blueprint.LieModel ↥N .PSL 3 2 4 ∧
          ∀ n ∈ N, orderOf (α * n) = 2 → ∃ γ ∈ N, γ⁻¹ * α * γ = α * n)

@[expose] def CF23L34HeStep : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), ¬ h.Table54 →
    Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2 → conjugate h.K h.a = h.K →
    Nonempty (OddBar h.K ≃* Blueprint.NativeSporadic.He) → h.Fus23ConclW

namespace CF23L34

open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.OutInv

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

include hKa in
theorem isSimpleGroup_NL : IsSimpleGroup ↥(NL hKa) := by
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  have : IsSimpleGroup (LK h) := h.isQuasisimple_K.2.1
  exact eN.isSimpleGroup

include hKa in
theorem gsRestricted_NL : GSRestricted ↥(NL hKa) := by
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  rcases h.type_K with hr | ⟨hne, -⟩
  · exact OddQuot.gsRestricted_of_mulEquiv (eZ.symm.trans eN.symm) hr
  · exact absurd hKa hne

include hKa in
theorem lieModel_Jhat (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) :
    Blueprint.LieModel (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) .PSL 3 2 2 := by
  obtain ⟨eJ⟩ := nonempty_Jhat_equiv' hKa
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.J
  exact OddQuot.lieModel_of_equiv (eZ.symm.trans eJ.symm) hL

include hKa in
theorem socle_cases (hS : CF23L34Socle) (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) :
    (Nonempty (↥(NL hKa) ≃* Blueprint.NativeSporadic.He) ∨
      phi hKa (abar h) ∈ NL hKa ∧ (Nonempty (↥(NL hKa) ≃* Blueprint.NativeSporadic.Suz) ∨
        Nonempty (↥(NL hKa) ≃* Blueprint.NativeSporadic.ON))) ∨
      (Blueprint.LieModel ↥(NL hKa) .PSL 3 2 4 ∧
        ∀ n ∈ NL hKa, orderOf (phi hKa (abar h) * n) = 2 →
          ∃ γ ∈ NL hKa, γ⁻¹ * phi hKa (abar h) * γ = phi hKa (abar h) * n) :=
  hS _ (NL hKa) (NL_normal hKa) (isSimpleGroup_NL hKa) (centralizer_NL hKa)
    (gsRestricted_NL hKa) _ _ (orderOf_phi_abar' hKa) (Jhat_le_NL hKa) (Jhat_component hKa).1
    (Jhat_component hKa).2 (lieModel_Jhat hKa hL)

end CF23L34

end CFSG.ComponentClassification.GSThmB
