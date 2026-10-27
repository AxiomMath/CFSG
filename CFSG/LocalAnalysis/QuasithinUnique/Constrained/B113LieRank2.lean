module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieExc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverRank2

public section

namespace CFSG.QuasithinUnique.Bridge

theorem asLieRank2Families
    : Over.AsLieRank2Families where
  l3 := Over.l3_overgroups
  sp4 := Over.sp4_overgroups
  g2 := Over.g2_overgroups
  d4 := Over.d4_overgroups
  f4 := Over.f4_overgroups
  tits := Over.tits_overgroups
  l5 := Over.l5_overgroups

theorem asLieRank2FStar
    : Over.AsLieRank2FStar :=
  asLieRank2Families.asLieRank2FStar

theorem asLieRank2SylowAutFamilies
    : AsLieRank2SylowAutFamilies where
  l3 := l3_sylowAutTrivial
  sp4 := sp4_sylowAutTrivial
  g2 := g2_sylowAutTrivial
  d4 := d4_sylowAutTrivial
  f4 := f4_sylowAutTrivial
  tits := tits_sylowAutTrivial
  l5 := l5_sylowAutTrivial

theorem asLieRank2SylowAut
    : AsLieRank2SylowAut :=
  asLieRank2SylowAutFamilies.asLieRank2SylowAut

end CFSG.QuasithinUnique.Bridge
