module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.HData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem exists_hSideData_base (h : F5Base a z) : HSideData a z :=
  exists_hSideData h.iface h.typ h.loc.fusion1.self h.loc.fusion2.self h.loc.a8pictures.self

end CFSG.EvenSporadicStandard.HNRecog.Section4
