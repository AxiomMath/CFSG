module

public import CFSG.Assembly.InCatalog
public import CFSG.Open.Defs

public section

namespace CFSG.Assembly

theorem kProper_inCatalog_iff_isKProper (G : Type) [Group G] :
    KProper InCatalog G ↔ CFSG.Open.IsKProper G :=
  Iff.rfl

theorem isCharTwoType_iff_open (G : Type*) [Group G] :
    IsCharTwoType G ↔ CFSG.Open.IsCharTwoType G :=
  Iff.rfl

theorem evenRank_eq_open (G : Type*) [Group G] [Finite G] :
    evenRank G = CFSG.Open.evenRank G :=
  rfl

end CFSG.Assembly
