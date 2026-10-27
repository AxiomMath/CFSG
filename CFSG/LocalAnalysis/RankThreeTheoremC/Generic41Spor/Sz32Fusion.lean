module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Pgroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedLemma33
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32LinesMain
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32ZData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 U3Lemma33)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_lines_fusion (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSz : Sz32Facts) (hSz' : Sz32OpenFacts) (hdata : Sz32DataFacts)
    (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G} (hA : Sz32QDecomp P x J a c y)
    (hL33 : U3Lemma33 5 x) : Sz32Lines P x (a ^ 5) :=
  sz32_lines_fusion_core hS hD1 hU0 hSz hSz' hdata hc hA hL33

theorem sz32_struct_of {a c y : G} (hA : Sz32QDecomp P x J a c y) (hL : Sz32Lines P x (a ^ 5)) :
    Sz32Struct P x J a c y := by
  obtain ⟨g, hg, hswap⟩ := hL.swap
  have hpres : Sz32QPres (P : Subgroup G) a c y x := by
    have := hA.pres
    rwa [u3S_eq_of_le_cent hL.le_cent] at this
  exact ⟨hA, hL.le_cent, sz32_pgroup_struct hpres hg hswap⟩

theorem sz32_Z_facts (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSz : Sz32Facts) (hSz' : Sz32OpenFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) (hL : Sz32Lines P x (a ^ 5)) : Sz32ZFacts P M x (a ^ 5) :=
  sz32_Z_facts' hS hD1 hU0 hSz hSz' hc hP hL

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
