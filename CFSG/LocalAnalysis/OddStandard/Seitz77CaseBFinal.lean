module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Model
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Certified
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Comm
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44G0
public import CFSG.LocalAnalysis.OddStandard.Seitz77MainDefs

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

theorem caseBCross :
    ∀ (G : Type) [Group G] [Finite G] (A V₁ V₂ : Subgroup G) (_ : Hyp G A) (d : Datum A)
      (_ : Radicals d.V V₁ V₂) (c₁ : CaseB A V₁ d.t) (c₂ : CaseB A V₂ d.t)
      (M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G) (k : Type) [Field k] (e : ↥A₁ ≃* ↥(unipAll k)),
      CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e → CrossData M₁ M₂ N₁ N₂ := by
  intro G _ _ A V₁ V₂ h d hR c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ k _ e CS
  have hZ₁ : c₁.OddCoreCentral := CaseB.oddCoreCentral h d hR (Or.inl rfl) c₁
  have hZ₂ : c₂.OddCoreCentral := CaseB.oddCoreCentral h d hR (Or.inr rfl) c₂
  obtain ⟨σa, σb, Up, Uq, W⟩ := exists_weylInput h d hR
  have hcomm := CS.commutator_G₁_G₂ hR hZ₁ hZ₂ W
  exact ⟨hcomm, CS.model_of_comm h hZ₁ hZ₂ W hcomm⟩

theorem caseBG0_exists
    {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (c₁ : CaseB A V₁ d.t) (c₂ : CaseB A V₂ d.t) :
    ∃ G₁ G₂ S₀ : Subgroup G, CaseBG0 d G₁ G₂ S₀ c₁.W c₂.W := by
  obtain ⟨M₁, M₂, N₁, N₂, S, A₁, B₁, k, _, e, CS⟩ := caseB_common_sylow h d hR c₁ c₂
  have hZ₁ : c₁.OddCoreCentral := CaseB.oddCoreCentral h d hR (Or.inl rfl) c₁
  have hZ₂ : c₂.OddCoreCentral := CaseB.oddCoreCentral h d hR (Or.inr rfl) c₂
  exact ⟨M₁ ⊔ N₁, M₂ ⊔ N₂, S, caseBG0_of_cross CS hR hZ₁ hZ₂
    (caseBCross G A V₁ V₂ h d hR c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ k e CS)⟩

theorem seitz77CaseBFalse :
    Seitz77CaseBFalse := by
  intro G _ _ A V₁ V₂ h d hR hyp
  obtain ⟨⟨c₁⟩, ⟨c₂⟩⟩ := caseB_of_forall hyp
  obtain ⟨G₁, G₂, S₀, hG0⟩ := caseBG0_exists h d hR c₁ c₂
  exact caseBG0_false_of_certificate h d hG0

end CFSG.OddStandard.Seitz77
