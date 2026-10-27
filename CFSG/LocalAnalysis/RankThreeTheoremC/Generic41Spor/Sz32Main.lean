module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedProp31
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedLemma33
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedFocal
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Qdecomp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Pgroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Lemma32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Fusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Lemma42
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Lemma43
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Lemma44
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Lemma45
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2G
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NormalCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Fcases
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32EndgameHyp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame41MaxPair
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (GenericComponentClass)

variable {G : Type} [Group G] [Finite G]

theorem sz32_false (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hK : TypeIIKFacts)
    (hClass : GenericComponentClass G) (hTits : TitsFacts) (hA10 : A10Facts)
    (hMcL : ExtraFacts IsMcLType 5 McLShape) (hJ4 : ExtraFacts IsJ4Type 11 J4Shape)
    (hSz : Sz32Facts) (hSz' : Sz32OpenFacts) (hdata : Sz32DataFacts) (hI6103 : KFactI6103Five)
    (hI122 : KFactI122Five) (hI713 : KFactI713Out) (hNonab : KFactNonabF5) {P : Sylow 5 G}
    {M : Subgroup G} {x : G} {J : Subgroup G} (hc : PointConfig IsSz32Type G 5 P M x J) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, c, y, hA⟩ := sz32_Q_decomp hS hD1 hU0 hSz hdata hc
  have hL33 := lemma33_of_lemma32 hS hc (sz32_lemma32 hS hD1 hU0 hK.sig hSz hdata hc hA)
  have hL := sz32_lines_fusion hS hD1 hU0 hSz hSz' hdata hc hA hL33
  have hP := sz32_struct_of hA hL
  have hZ := sz32_Z_facts hS hD1 hU0 hSz hSz' hc hP hL
  obtain ⟨U, hU⟩ := sz32_plane hP hL
  have hL42 := sz32_lemma42 hS hD1 hU0 hClass hTits hA10 hMcL hJ4 hSz hc hP hL hZ hU
  have hnorm := sz32_normal_core hS hD1 hU0 hSz hSz' hI6103 hI122 hI713 hc hP hL hZ
  have hL43 := sz32_lemma43 hS hD1 hU0 hc hP hL hZ hnorm hU
  have hL44 := sz32_lemma44 hS hD1 hU0 hSz hSz' hc
  have hL45 := sz32_lemma45_G hS hD1 hU0 hSz hSz' hc hP hU
  have hFd := sz32_hFd hS hD1 hU0 hNonab hc hP hL hZ hU hL42
  exact eg41_false_of_plane_maxpair hS hU0 hD1 hK.inner hK.weak hc.sigma (by have := hc.five; omega)
    hc.core hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 hU.abs.elem hU.abs.card hU.le_P hU.abs.mem hFd
    hL42 hL43 hL45 hL44

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
