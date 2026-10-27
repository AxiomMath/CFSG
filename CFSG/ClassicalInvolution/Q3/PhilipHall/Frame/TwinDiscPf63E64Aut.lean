
module


public import Certificates.Certificate393003
public import Certificates.Data.E64Aut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open Certificates.AE117 Certificates.E64Aut CFSG.ClassicalInvolution.Q3.E64Data

namespace TwinDisc

namespace E64Aut

theorem center_e64Sub_eq_bot : Subgroup.center ↥e64Sub = ⊥ :=
  Certificates.certificate393003.1

theorem e64_aut_eq_conj (θ : MulAut ↥e64Sub)
    {α : Finset (Fin 7)} (hα : α ∈ e64Sets) (h : α.card = 4)
    (hT : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α h true → θ x = x)
    (hF : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α h false → θ x = x) :
    ∃ c : ↥e64Sub, c * c = 1 ∧ ∀ y : ↥e64Sub,
      (∃ α' ∈ e64Sets, ∃ (h' : α'.card = 4) (b : Bool), (y : AEQ 7) ∈ memBar α' h' b) →
        θ y = c * y * c⁻¹ :=
  Certificates.certificate393003.2 θ hα h hT hF

end E64Aut

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
