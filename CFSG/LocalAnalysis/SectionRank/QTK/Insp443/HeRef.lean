module

public import Certificates.Certificate725002
public import CFSG.Quasithin.Vol2.KGFactC31HeRefBase

public section

namespace CFSG.SectionRank.QTK.Insp443.He

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.He _root_.Certificates

theorem k_he1 :
    ([x7W, c7W].all (lettersOK 2) && fixB bs [wA x7W] 7 && !(fixB bs [wA x7W] 1) &&
      normsW bs qA (wA x7W) (wAi x7W) && normsW bs qA (wA c7W) (wAi c7W)) = true :=
  Certificates.certificate725002.1

theorem k_he2 :
    (rawChainOK 8330 (arrO l7S l7GenW.length) l7S (arrBase l7B) l7Wd 4 &&
      ((rawOrbitSizes 8330 l7S (arrBase l7B)).prod == 21504)) = true :=
  Certificates.certificate725002.2

theorem k_he_letters : [x7W, c7W].all (lettersOK 2) = true :=
  band_l (band_l (band_l (band_l k_he1)))

theorem k_he_x7a : fixB bs [wA x7W] 7 = true :=
  band_r (band_l (band_l (band_l k_he1)))

theorem k_he_x7b : fixB bs [wA x7W] 1 = false := by
  have h := band_r (band_l (band_l k_he1))
  simpa using h

theorem k_he_normX : normsW bs qA (wA x7W) (wAi x7W) = true :=
  band_r (band_l k_he1)

theorem k_he_normC : normsW bs qA (wA c7W) (wAi c7W) = true :=
  band_r k_he1

theorem k_he_chain :
    rawChainOK 8330 (arrO l7S l7GenW.length) l7S (arrBase l7B) l7Wd 4 = true :=
  band_l k_he2

theorem k_he_ord : (rawOrbitSizes 8330 l7S (arrBase l7B)).prod = 21504 :=
  beq_nat (band_r k_he2)

end CFSG.SectionRank.QTK.Insp443.He

end
