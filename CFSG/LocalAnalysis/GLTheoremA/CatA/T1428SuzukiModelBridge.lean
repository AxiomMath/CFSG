module

public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Generated

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open TauCeti

theorem suzukiW_eq_weylMatrix (m : ℕ) :
    (CFSG.Blueprint.suzukiW (GaloisField 2 (2 * m + 1)) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) =
      TauCeti.Suzuki.weylMatrix m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Blueprint.suzukiW, TauCeti.Suzuki.weylMatrix_apply]

end CFSG.LocalAnalysis.GLTheoremA
