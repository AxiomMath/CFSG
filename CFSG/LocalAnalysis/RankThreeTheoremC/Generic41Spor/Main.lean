module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (GenericComponentClass)

variable {G : Type} [Group G] [Finite G]

theorem noExoticPoint_of_types (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hK : TypeIIKFacts) (hClass : GenericComponentClass G)
    (hTits : TitsFacts) (hA10 : A10Facts) (hMcL : ExtraFacts IsMcLType 5 McLShape)
    (hJ4 : ExtraFacts IsJ4Type 11 J4Shape) (hSz : Sz32Facts) (hSz' : Sz32OpenFacts)
    (hdata : Sz32DataFacts) (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hI : KFactI1434) (hU : KFactU44Data) (hXe : A10Ext) (hI6103 : KFactI6103Five)
    (hI122 : KFactI122Five) (hI713 : KFactI713Out) (hNonab : KFactNonabF5) :
    NoExoticPoint G := by
  intro p hp P M hM hfail hIH x hgen h5 J hE
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hE.iso
  rcases isExoticType_iff.1 hQ with hA | hT | hMc | hJ | hS32
  ·
    have hp0 := hA.1
    subst hp0
    exact a10_false hS hD1 hU0 hK hClass hTits hMcL hJ4 hSz hSz' hdata hSch hI hU hA10 hXe (pointConfig_of_exotic hp hM hfail hIH hgen h5 hE
      ⟨Q, hQg, ψ, hψ, hker, hA⟩)
  · have hp0 := hT.1
    subst hp0
    exact tits_false hS hD1 hU0 hK hClass hA10 hMcL hJ4 hSz hSz' hdata hTits (pointConfig_of_exotic hp hM hfail hIH hgen h5 hE
      ⟨Q, hQg, ψ, hψ, hker, hT⟩)
  · have hp0 := hMc.1
    subst hp0
    exact mcl_false hS hD1 hU0 hK hClass hTits hA10 hJ4 hSz hSz' hdata hMcL (pointConfig_of_exotic hp hM hfail hIH hgen h5 hE
      ⟨Q, hQg, ψ, hψ, hker, hMc⟩)
  · have hp0 := hJ.1
    subst hp0
    exact j4_false hS hD1 hU0 hK hClass hTits hA10 hMcL hJ4 (pointConfig_of_exotic hp hM hfail hIH hgen h5 hE
      ⟨Q, hQg, ψ, hψ, hker, hJ⟩)
  · have hp0 := hS32.1
    subst hp0
    exact sz32_false hS hD1 hU0 hK hClass hTits hA10 hMcL hJ4 hSz hSz' hdata hI6103 hI122 hI713 hNonab
      (pointConfig_of_exotic hp hM hfail hIH hgen h5 hE ⟨Q, hQg, ψ, hψ, hker, hS32⟩)

theorem genericListSpor_of_types (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hK : TypeIIKFacts) (hClass : GenericComponentClass G)
    (hTits : TitsFacts) (hA10 : A10Facts) (hMcL : ExtraFacts IsMcLType 5 McLShape)
    (hJ4 : ExtraFacts IsJ4Type 11 J4Shape) (hSz : Sz32Facts) (hSz' : Sz32OpenFacts)
    (hdata : Sz32DataFacts) (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hI : KFactI1434) (hU : KFactU44Data) (hXe : A10Ext) (hI6103 : KFactI6103Five)
    (hI122 : KFactI122Five) (hI713 : KFactI713Out) (hNonab : KFactNonabF5) :
    GL83GenericListExclusionRedSpor G :=
  genericListSpor_of_noExoticPoint
    (noExoticPoint_of_types hS hD1 hU0 hK hClass hTits hA10 hMcL hJ4 hSz hSz' hdata hSch hI hU hXe
      hI6103 hI122 hI713 hNonab)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
