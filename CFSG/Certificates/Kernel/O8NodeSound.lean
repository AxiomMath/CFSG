module

public import CFSG.Certificates.Kernel.O8MaskProved
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2

theorem fixMaskW_lt (y : ℕ) : fixMaskW swarK y < 2 ^ 4096 := by
  apply fixMaskW_lt_proved

theorem testBit_fixMaskW (y : ℕ) {v : ℕ} (hv : v < 4096) :
    (fixMaskW swarK y).testBit v = (mulVec12K y v == v) := by
  apply testBit_fixMaskW_proved <;> assumption

theorem allRoots_eqM {B : ℕ} {SW I : List ℕ} {b : ℕ → Bool} {Xb : ℕ} (hSW : SW = swarK)
    (hXb : Xb < 2 ^ 4096) (hb : ∀ v < 4096, Xb.testBit v = b v) :
    allRoots B I ((List.range 4096).filter b) =
      I.all fun r => nodeM B SW 8 [ID12, r] (Nat.land Xb (fixMaskW SW r)) (commOfK I r) := by
  apply allRoots_eqM_proved <;> assumption

end CFSG.KC.O8

end
