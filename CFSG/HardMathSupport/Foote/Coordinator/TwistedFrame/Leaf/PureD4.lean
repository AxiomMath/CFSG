module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Basic
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Coords
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PureD4AuxPure

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem twPure_D4 (K : Type) [Field K] [Finite K] (hK : TwClass.e8Twelve.minQ ≤ Nat.card K)
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    TwPure (TwClass.e8Twelve.X₁ D) (TwClass.e8Twelve.X₂ D) := by
  intro g hg hC
  have hcomm := TwBasicAux.frame_commute TwClass.e8Twelve D
  have hU₁ : Uθ TwClass.e8Twelve.tag K ≤ TwClass.e8Twelve.X₁ D :=
    TwBasicAux.rootSubgroup_le_frame D (TwBasicAux.highRoot_mem_S₁ _)
      (Pθ_le_normalizer_Uθ _ D.L (parabolicLevi_le_parabolicSubgroup _ D.g_mem))
  have hV₁ : Heis.Uneg TwClass.e8Twelve.tag K ≤ TwClass.e8Twelve.X₁ D :=
    TwBasicAux.rootSubgroup_le_frame D (TwBasicAux.neg_highRoot_mem_S₁ _)
      (Lθ_le_normalizer_Uneg _ D.L D.g_mem)
  have hco := twCoords TwClass.e8Twelve K hK D
  have hZ : ∀ d ∈ (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) ⊓ Qθ Tag.E8 K,
      (∀ r ∈ (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) ⊓ Qθ Tag.E8 K, r * d = d * r) →
      d ∈ Uθ Tag.E8 K := by
    intro d hd hcen
    have hs := heisCoord_spec Tag.E8 K
    have h1 : heisCoord Tag.E8 K d ∈ VS (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) :=
      Submodule.subset_span ⟨d, hd, rfl⟩
    have h2 : heisCoord Tag.E8 K d ∈ VM (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) :=
      Submodule.subset_span ⟨d, ⟨hd.2, Subgroup.mem_centralizer_iff.2 hcen⟩, rfl⟩
    have h0 : heisCoord Tag.E8 K d ∈
        VS (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) ⊓
          VM (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) := ⟨h1, h2⟩
    rw [hco.inf_eq_bot] at h0
    exact (hs.eq_zero_iff d hd.2).1 ((Submodule.mem_bot K).1 h0)
  exact PureD4Aux.pure_of_center_sup K hcomm hU₁ hV₁ hZ hg hC

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
