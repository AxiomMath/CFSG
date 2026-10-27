module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def CoverStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K E : Subgroup G), GLAPComponent 3 X K → IsPGroup 3 ↥E →
    E ≤ dQ K → ∃ J : Subgroup G,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer (E : Set G)) J ∧ K ≤ J ⊔ GLAPPrimeCoreOf 3 K ∧
        (∀ J' : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer (E : Set G)) J' → J' = J) ∧
        GLAPPrimeCoreOf 3 J = J ⊓ GLAPPrimeCoreOf 3 K

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
