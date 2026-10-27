module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Tits
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTGeneric
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


theorem noSmall_lie_tits (hv : TauCeti.LieTypeIndex.tits.Valid) :
    HStdExcl.NoSmall (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := by
  intro α hα3 hα1 I hI hsmall
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv
    (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)
      ⟨hv, ⟨MulEquiv.refl _⟩⟩)
  have hγ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hγ1 : MulAut.congr e α ≠ 1 := by
    intro h1
    exact hα1 ((MulAut.congr e).injective (h1.trans (map_one (MulAut.congr e)).symm))
  haveI hsolv : Group.IsSolvable ↥(fixSubgroup α) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRT.isSolvable_fixSubgroup_of_congr e α
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_titsD
        CFSG.Sporadic.Schreier.Tits.titsD_center hγ3 hγ1)
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.not_isComponentOf_of_isSolvable hsolv hI

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
