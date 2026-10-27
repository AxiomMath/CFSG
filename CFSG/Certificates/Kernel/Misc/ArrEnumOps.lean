module

public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack

public section

namespace CFSG.KC.Misc.ArrEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem permB_pcomp {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    permB n w (pcomp n w (mask w) p q) = true :=
  permB_of_pp ((pp_of_permB hw hp).mul (pp_of_permB hw hq))

theorem permB_pinvS {p : ℕ} (hp : permB n w p = true) :
    permB n w (pinvS n w (mask w) p) = true :=
  permB_of_pp (pp_of_permB hw hp).inv

theorem permB_ppow {p : ℕ} (hp : permB n w p = true) (e : ℕ) :
    permB n w (ppow n w (mask w) (pidn n w) p e) = true :=
  permB_of_pp (pp_ppow hw (pp_of_permB hw hp) e)

theorem wordA_unpack {S Sinv : Array (Array ℕ)} {SC SIC : ℕ → ℕ} {j : ℕ}
    (hS : ∀ h < j, S[h]! = unpack n w (SC h)) (hSI : ∀ h < j, Sinv[h]! = unpack n w (SIC h))
    (hSp : ∀ h < j, permB n w (SC h) = true) (hSIp : ∀ h < j, permB n w (SIC h) = true)
    {wd : List ℤ} (hl : CFSG.Monster.B.Co2.Native.lettersOK j wd = true) :
    CFSG.Monster.B.Co2.Native.wordA n S Sinv wd =
      unpack n w (CFSG.KS.Raw.wordK n w (mask w) (pidn n w) SC SIC wd) :=
  wordA_eq hw hS hSI hSp hSIp wd hl

theorem permB_wordK {SC SIC : ℕ → ℕ} {j : ℕ} (hSp : ∀ h < j, permB n w (SC h) = true)
    (hSIp : ∀ h < j, permB n w (SIC h) = true) {wd : List ℤ}
    (hl : CFSG.Monster.B.Co2.Native.lettersOK j wd = true) :
    permB n w (CFSG.KS.Raw.wordK n w (mask w) (pidn n w) SC SIC wd) = true :=
  permB_of_pp (pp_wordK hw hSp hSIp wd hl)

end CFSG.KC.Misc.ArrEnum

end
