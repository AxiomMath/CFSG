module

public import CFSG.GH74.Generic.Front.Transport
public import CFSG.GH74.Generic.Front.DataUni
public import CFSG.GH74.Generic.Front.DataSp
public import CFSG.GH74.Generic.Front.NoCentralStatement

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank

theorem frontData0Statement : FrontData0Statement := by
  intro K _ hK
  rcases hK with (⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩) | ⟨F, _, _, hodd, ⟨e⟩⟩
  · obtain ⟨D⟩ := frontData0_statedSL4 hF
    exact FrontData0.ofMulEquiv e.symm D
  · obtain ⟨D⟩ := frontData0_statedSU4 hF hq
    exact FrontData0.ofMulEquiv e.symm D
  · obtain ⟨D⟩ := frontData0_statedSp2 hodd
    exact FrontData0.ofMulEquiv e.symm D

theorem frontDataStatement : FrontDataStatement :=
  frontDataStatement_of frontData0Statement noCentralStatement

end CFSG.GH74.Generic
