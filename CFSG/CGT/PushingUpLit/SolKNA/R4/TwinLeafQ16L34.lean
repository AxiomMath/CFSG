module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16Sound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafModels
public import Certificates.Certificate320301

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG.ComponentClassification.PSL3Four

theorem noQ16Q16_psl3four_R :
    NoQ16Q16 ↥R := by
  obtain ⟨Q, hQR, hQ, hno⟩ := Certificates.certificate320301
  exact noQ16Q16_of_sylow_card hQR (k := 8) (m := 945) hQ (by decide)
    (by rw [card_R]; norm_num) hno

theorem autL34NoQ16Q16_of_cert :
    AutL34NoQ16Q16 :=
  autL34NoQ16Q16_of_model noQ16Q16_psl3four_R

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
