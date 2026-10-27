module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallL27
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallU3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallTits
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallG2Char2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallG2Odd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section A5

theorem i141RankA5_holds : I141RankA5 :=
  i141RankFamily_of_autRank _ fun _ hp hp2 _ _ _ h _ hE h3 => i141f_autRank_alt5 hp hp2 h hE h3

end A5

section A6

theorem i141RankA6_holds : I141RankA6 :=
  i141RankFamily_of_autRank _ fun _ hp hp2 _ _ _ h _ hE h3 => i141f_autRank_alt6 hp hp2 h hE h3

end A6

section A8

theorem i141RankA8_holds : I141RankA8 :=
  i141RankFamily_of_autRank _ fun _ hp hp2 _ _ _ h _ hE h3 => i141f_autRank_alt8 hp hp2 h hE h3

end A8

section L27

theorem i141RankL27_holds : I141RankL27 :=
  i141RankFamily_of_autRank _ fun _ hp hp2 _ _ _ h _ hE h3 => i141f_autRank_l27 hp hp2 h hE h3

end L27

section U3


theorem i141RankU3_holds : I141RankU3 :=
  i141RankFamily_of_autRank _ fun _ hp hp2 _ _ _ h _ hE h3 => i141f_autRank_u3 hp hp2 h hE h3

end U3

section Tits


theorem i141RankTits_holds : I141RankTits :=
  i141RankFamily_of_autRank _ fun _ hp hp2 _ _ _ h _ hE h3 => i141f_autRank_tits hp hp2 h hE h3

end Tits

section Small


theorem i141RankSmall_holds
    : I141RankSmall :=
  i141RankSmall_of_families i141RankG2Char2_holds i141RankG2Odd_holds i141RankU3_holds
    i141RankA5_holds i141RankA6_holds i141RankA8_holds i141RankL27_holds i141RankTits_holds

end Small

end CFSG.LocalAnalysis.GLTheoremA.I141F
