module

public import CFSG.GH74.GLS.C3.Prop121.Card7Main
public import CFSG.GH74.GLS.C3.Prop121.Card7F
public import CFSG.GH74.GLS.C3.Prop121.Card7H
public import CFSG.GH74.GLS.C3.Prop121.Card7Syl

public section

namespace CFSG.GH74.GLS.C3.Prop121

theorem s_card7 :
    S_card7 :=
  Card7.s_card7_of_facts Card7.card7FFacts Card7.card7HFacts Card7.Syl.card7SylFacts

theorem s_prop121_cfg_final
    : S_prop121_cfg := s_prop121_cfg_of_card7 s_card7

end CFSG.GH74.GLS.C3.Prop121
