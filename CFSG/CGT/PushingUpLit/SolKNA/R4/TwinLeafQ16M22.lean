module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16Sound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafModels
public import Certificates.Certificate320302

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG.ComponentClassification.RankTwoSporadic.M22

theorem noQ16Q16_ppair_of_cert :
    NoQ16Q16 ↥CFSG.Monster.B.TwoA.Ppair := by
  have hcard : 2 ^ 8 * 3465 = Nat.card ↥(iota.range) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective iota_injective).toEquiv,
      CFSG.Monster.B.TwoA.natCard_Ppair]
    norm_num
  obtain ⟨Q, hQR, hQc, hno⟩ := Certificates.certificate320302
  have hQ := noQ16Q16_of_sylow_card hQR (k := 8) (m := 3465) hQc (by decide) hcard hno
  exact NoQ16Q16.of_injective (MonoidHom.ofInjective iota_injective).toMonoidHom
    (MulEquiv.injective _) hQ

theorem autM22NoQ16Q16_holds :
    AutM22NoQ16Q16 :=
  autM22NoQ16Q16_of_model noQ16Q16_ppair_of_cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
