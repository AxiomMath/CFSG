module

public import CFSG.GF2Type.Smith1979W3.SuzL34Input
public import CFSG.GF2Type.Smith1979W3.T1216NoPGL27
public import CFSG.Sporadic.SuzRecog.SuzL34Cert.Checks
public import CFSG.Sporadic.SuzRecog.SuzL34Cert.ChecksBase

public section

namespace CFSG.GF2Type.Smith1979W3

open CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.GF2Type.Smith1979W3.Cert690

theorem suzL34DataInput_holds :
    SuzL34DataInput :=
  suzL34DataInput_of f1_sound f1m_sound f2_sound f3_sound f4_sound f5_sound f6_sound f6b_sound
    f7_sound f8_sound f9_sound f11_sound

section Certs


theorem smith1979WidthThreeCharTwoKP_of_cert690 (hP : CensusPlusProp) (hM : CensusMinusProp)
    (hF : PGLFactsProp) (hPS : PGLSquareProp) (hA8 : A8SquareProp) :
    Smith1979WidthThreeCharTwoKP :=
  smith1979WidthThreeCharTwoKP_of_t1216 (t1216WidthThree_of_cert690 hP hM hF hPS hA8)
    suzL34DataInput_holds

end Certs

end CFSG.GF2Type.Smith1979W3
