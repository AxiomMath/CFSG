module

public import Certificates.Data.Kernel.PermCent.KGrpC2
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.GH74.KGroups.NativeChecks
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Prop27.OddCoreCheck
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp

open CFSG.GH74.KGroups CFSG.GH74.GLS.Prop27

variable {n : Nat} [Small n]

theorem centIn_C (LA LS : List (CV n)) :
    NativeChecks.centInCheck (LA.map ev) (LS.map ev) = centInC LA LS := by
  unfold NativeChecks.centInCheck centInC
  simp only [List.all_map, Function.comp_def, ev_mul', decide_ev_eq, comm_fast, decide_mem_map_ev]

theorem oddCoreAt_C (m : Nat) (CA CP : List (CV n)) :
    oddCoreAt m (CA.map ev) (CP.map ev) = oddCoreAtC m CA CP := by
  unfold oddCoreAt oddCoreAtC
  simp only [List.all_map, List.any_map, Function.comp_def, ne_eq, decide_not, ev_mul', ev_inv',
    ev_pow', one_eq_ev, decide_ev_eq]

theorem oddCoreCheck_C (m : Nat) (LA LP : List (CV n)) :
    oddCoreCheck m (LA.map ev) (LP.map ev) = oddCoreCheckC m LA LP := by
  unfold oddCoreCheck oddCoreCheckC
  simp only [List.filter_map, List.all_map, Function.comp_def, oddCoreAt_C, ne_eq, decide_not,
    ev_mul', ev_pow', one_eq_ev, decide_ev_eq, pow_fast, comm_fast]

end CFSG.Certificates.Kernel.PkCV.KGrp

end
