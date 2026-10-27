module

import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSym
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

open CFSG.Open Subgroup

@[expose] def NoTwoSymThree {A : Type} [Group A] (P : Subgroup A) : Prop :=
  ∀ X X' : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), Sym.IsSymThree X → Sym.IsSymThree X' →
    IsSubnormal X ⊤ → IsSubnormal X' ⊤ → X = X'

theorem pCore_two_hat_eq_bot {A : Type} [Group A] (P : Subgroup A) :
    CFSG.pCore 2 (↥P ⧸ CFSG.pCore 2 ↥P) = ⊥ :=
  CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
