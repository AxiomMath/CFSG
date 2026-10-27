module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2S
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2O

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

namespace E3S3O


theorem e4SigmaFix_of_exLie (M : Type) [Group M] [Finite M]
    (hM : PhilipHall.QuaternionBridge.ExLie M) : E4SigmaFix M := by
  rcases hM with h | h
  · exact e4SigmaFix_PSp h
  · exact e4SigmaFix_POmegaPlus h

theorem model1524Twin3E4_proved : Model1524Twin3E4 :=
  model1524Twin3E4_of e4SigmaFix_of_exLie

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
