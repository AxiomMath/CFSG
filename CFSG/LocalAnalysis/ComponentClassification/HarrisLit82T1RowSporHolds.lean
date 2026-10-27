module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spor
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltReduce

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowSpor

open CFSG Subgroup


theorem rowCore_spor :
    RowAlt.RowCore (fun _ S => Blueprint.NativeSporadic.SporadicRep S ∧
      ¬ Nonempty (S ≃* ↥Blueprint.NativeSporadic.M11)) := by
  intro S _ _ _ hna p hp hp2 hC t ht J hJC hJs htJ hJq L _ _ hM hI he
  exact SporRow.rowCore_spor_perfect S hna p hp hp2 hC t ht J hJC hJs htJ
    ⟨hJq, L, inferInstance, inferInstance, hM, hI, he⟩

theorem rowSpor_holds : RowSpor :=
  RowAlt.rowSpor_of_core rowCore_spor

end CFSG.ComponentClassification.HarrisLit.T1.RowSpor
