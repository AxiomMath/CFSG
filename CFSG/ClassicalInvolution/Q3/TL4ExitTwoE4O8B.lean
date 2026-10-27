module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8W11
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Certificate127
public import Certificates.Data.E4QuatArr
public import Certificates.Data.E4QuatCheck
public import Certificates.Data.E4QuatO8
public import Certificates.Data.O8p2NoDatum

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.O8Data CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem outer_root_spec {i : ℕ} (hi : i < 3)
    {j : Equiv.Perm (Fin 360)} (hjA : j ∈ autT) (hjO : j ∉ omegaT) (hjj : j * j = mainPerm i) :
    (∃ c ∈ omegaT, c * mainPerm i = mainPerm i * c ∧ ∃ k : ℕ,
      (j⁻¹ * c * j * c⁻¹) ^ k ≠ 1 ∧ ((j⁻¹ * c * j * c⁻¹) ^ k) ^ 3 = 1) ∨
      ∀ u ∈ omegaT, u * u = mainPerm i → j * u * j⁻¹ ≠ u⁻¹ :=
  Certificates.certificate127.2.2 hi hjA hjO hjj

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
