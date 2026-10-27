module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Hyp52.Fus23ConclW {H : Type} [Group H] [Finite H] (h : Hyp52 H) : Prop :=
  ∃ g ∈ h.W, g⁻¹ * h.a * g ∈ h.S ∧ g⁻¹ * h.a * g ∉ h.P ∧
    g⁻¹ * h.a * g ∈ closure ((h.D : Set H) ∪ {h.a}) ⊓ centralizer ({h.x} : Set H)

@[expose] def CFProp23Fusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), ¬ h.Table54 → h.Fus23ConclW

@[expose] def CFProp23Center : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Table54 →
    h.T ⊓ centralizer (h.Q : Set H) ≤ zpowers h.a ⊔ h.B

@[expose] def CFProp24c : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H),
    Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2 → conjugate h.K h.a = h.K →
    center (OddBar h.K) ≠ ⊥ → Nonempty (ZStarBar h.K ≃* Blueprint.NativeSporadic.Suz) →
    Even (Nat.card (Open.fusionZStar ↥(GSLit.fixedLayer h.J h.B))) ∧
      (Open.fusionZStar ↥(GSLit.fixedLayer h.J h.B)).map (GSLit.fixedLayer h.J h.B).subtype ≤
        (Open.fusionZStar ↥h.K).map h.K.subtype

@[expose] def CFProp23IndexReduced : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.Table517 → h.T ≤ zpowers h.a ⊔ h.B

end CFSG.ComponentClassification.GSThmB
