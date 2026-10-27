module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitMinusW
public import CFSG.Certificates.Kernel.O8MaskProved

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.N3Split

theorem fixBoth_eqM {SW : List ℕ} (hSW : SW = swarK) (s c : ℕ) :
    ((fixVecs s).filter fun v => mulVecK c v == v).length =
      popcM SW (fixMaskW SW s &&& fixMaskW SW c) := by
  apply fixBoth_eqM_proved <;> assumption

theorem burnCountL_eqM {SW : List ℕ} (hSW : SW = swarK) (E : Enum) (s : ℕ) :
    burnCountL E s = ((List.range E.keys.size).map fun i =>
      if mulK (E.keys.getD i 0) s = mulK s (E.keys.getD i 0) then
        popcM SW (fixMaskW SW s &&& fixMaskW SW (E.keys.getD i 0)) else 0).sum := by
  simp only [burnCountL, fixBoth_eqM hSW]

end CFSG.KC.O8
