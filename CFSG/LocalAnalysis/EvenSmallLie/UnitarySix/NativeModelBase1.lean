
module


public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

@[expose] public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Fischer CFSG.ComponentClassification.M12Cover
open scoped Pointwise

theorem rep_letter
    (k : ℕ) (hk : k < 46) : Rep 693 (letterT k) (letter k hk) := by
  intro i hi
  rw [idx_of_lt _ hi, Equiv.Perm.smul_def, letter, tab_eq]
  change ap (letterT k) i = ap (letterT k) i % 693
  rw [Nat.mod_eq_of_lt (involOK_spec (letterT_ok k hk) hi).1]

end CFSG.EvenSmallLie.UnitarySix
