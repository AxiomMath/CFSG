module

public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFE
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFAll
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundP
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundA
public import Certificates.Certificate690001

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

theorem enumCert_pgl_of_pglFactsCheck (h : pglFactsCheck () = true) :
    EnumCert kPGLGens (pglData ()).elems.toList ∧
      EnumCert kPGL0Gens (pglData ()).elems0.toList := by
  simp only [pglFactsCheck, pglF1Of, Bool.and_eq_true] at h
  exact ⟨enumOK_sound h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
    enumOK_sound h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩

theorem enumCert_a8_of_a8SquareCheck (h : a8SquareCheck () = true) :
    EnumCert a8Gens (a8Data ()).elems.toList := by
  simp only [a8SquareCheck, a8S1Of, Bool.and_eq_true] at h
  exact enumOK_sound h.1.1.1.1.1.1.1.1

theorem pglFactsProp_holds : PGLFactsProp :=
  have h := Certificates.certificate690001
  pglFacts_sound_of (enumCert_pgl_of_pglFactsCheck h).1 (enumCert_pgl_of_pglFactsCheck h).2 h

theorem pglSquareProp_holds :
    PGLSquareProp :=
  have h := enumCert_pgl_of_pglFactsCheck Certificates.certificate690001
  pglSquare_sound_of_cert h.1 h.2

theorem a8SquareProp_holds : A8SquareProp :=
  a8Square_sound_of_cert (enumCert_a8_of_a8SquareCheck Certificates.certificate690003)

end CFSG.GF2Type.Smith1979W3.Cert690

end
