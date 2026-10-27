module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltDefs

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open CFSG.ComponentClassification.HarrisLit.T1

@[expose] def Case3RowCores : Prop :=
  RowAlt.RowCore (fun p S => (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∧
      ¬ LieChar p S) ∧
    RowAlt.RowCore (fun p S => (∃ r : ℕ, r ≠ p ∧ LieChar r S) ∧ ¬ LieChar p S) ∧
    RowAlt.RowCore (fun _ S => CFSG.Blueprint.NativeSporadic.SporadicRep S ∧
      ¬ Nonempty (S ≃* ↥CFSG.Blueprint.NativeSporadic.M11))

end CFSG.OddStandard.HigherRank.G2Three
