module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Components
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Indecomposable

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.SectionRank

variable {K : Type} [Group K] [Finite K]

theorem isSimpleGroup_of_hyp (hSch : SchreierFor Catalog) (hP : P12Facts) (hKg : IsKGroupCat K)
    (hK : SolomonA12HypK K) : IsSimpleGroup K := by
  obtain ⟨L, C, hL, hLs, hLnc, hC, hLC, hsup, hcomm⟩ := exists_split hSch hP hKg hK
  have hCbot : C = ⊥ := eq_bot_of_split hP hK hL hC hLC hsup hcomm hLnc
  have hLtop : L = ⊤ := by
    rw [hCbot, sup_bot_eq] at hsup
    exact hsup
  haveI := hLs
  let e : K ≃* ↥L := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)
  exact e.isSimpleGroup

end CFSG.EvenSporadicStandard.M12Std.SolomonK
