module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203PSp4
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Prop27

public section

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Main

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

theorem lemma20_3_thm
    (h34 : Leaf_Prop34)
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) : Lemma20_3 :=
  L203.lemma20_3_of_prop27 h34 (L203.l203Prop27_thm hfld hSch)

end CFSG.GH74.GLS.Stage2.Final.Thm6
