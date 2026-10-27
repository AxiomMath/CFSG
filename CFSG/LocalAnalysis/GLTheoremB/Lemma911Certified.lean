module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem outer_solvable_of_component_certified {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsKGroup Q) {K : Subgroup Q} (hK : IsComponentOf K ⊤) :
    Group.IsSolvable (Outer ↥K) :=
  outer_solvable_of_component CFSG.AGLEmbedding.kFactCatalogSchreier hQ hK

theorem prop98_of_inputs_S_certified (hS : Lemma911S) (i20 : Input20_1) (i11 : Input11_6)
    (l23 : Lemma23) (i19 : Input19Delta) (i19' : Input19_1_6) (h95 : Prop95Core)
    (h99 : Lemma99) (i22 : Input22_5) (iPi : InputPiGen) : Prop98 :=
  prop98_of_inputs_S CFSG.AGLEmbedding.kFactCatalogSchreier hS i20 i11 l23 i19 i19' h95 h99 i22 iPi

end CFSG.LocalAnalysis.GLTheoremB
