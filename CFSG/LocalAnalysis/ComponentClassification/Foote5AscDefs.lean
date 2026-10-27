module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Abstract

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def AschbacherCentralCoreInput : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (S : Sylow 2 B),
    Open.properTwoGenCoreGamma (S : Subgroup B) 2 ≠ ⊤ → ∀ t : B, orderOf t = 2 →
    t ∈ center B → 3 ≤ CFSG.pRank 2 B →
    (∀ X : Subgroup B, IsPComponent 2 X → t ∈ X → CFSG.pRank 2 ↥X ≤ 1 → False) →
    (∀ X : Subgroup B, IsPComponent 2 X → t ∈ X →
      IsCoverOverTwo (X ⧸ pPrimeCore 2 X) (alternatingGroup (Fin 9)) → False) →
    FooteAschbacherDichotomy (B ⧸ pPrimeCore 2 B)

end CFSG.ComponentClassification.Foote5
