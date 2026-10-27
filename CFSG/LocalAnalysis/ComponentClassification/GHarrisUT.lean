module

public import Certificates.Certificate22605
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GHarris.SCert.SE

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem mem_centralizer_l_iff : ∀ s : SE, s * gen 1 = gen 1 * s ↔ s.d.val < 4 := by
  decide +kernel

theorem toUT_mul (s t : SE) (hs : s.d.val < 4)
    (ht : t.d.val < 4) : toUT (s * t) = toUT s * toUT t :=
  Certificates.certificate22605.1 s t hs ht

theorem toUT_ker (s : SE) (hs : s.d.val < 4) (h : toUT s = 1) :
    s = 1 ∨ s = gen 1 ∨ s = gen 0 ∨ s = gen 1 * gen 0 :=
  Certificates.certificate22605.2.1 s hs h

theorem toUT_surj (u : UT3 F4c) :
    ∃ s : SE, s.d.val < 4 ∧ toUT s = u :=
  Certificates.certificate22605.2.2 u

theorem toUT_lpow : toUT 1 = 1 ∧ toUT (gen 1) = 1 ∧ toUT (gen 0) = 1 ∧
    toUT (gen 1 * gen 0) = 1 := by decide

theorem predE_iff_toUT : ∀ s : SE, s.d.val < 4 → (predE s ↔ (toUT s).b = 0) := by
  decide +kernel

theorem predF_iff_toUT : ∀ s : SE, s.d.val < 4 → (predF s ↔ (toUT s).a = 0) := by
  decide +kernel

end CFSG.ComponentClassification.GHarris.SCert.SE
