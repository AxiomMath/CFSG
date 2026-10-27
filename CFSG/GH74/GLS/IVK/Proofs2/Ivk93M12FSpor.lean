module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Leaves
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12FAlt
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.J2
import CFSG.Sporadic.J3
import CFSG.Sporadic.McL.Simple
import CFSG.Sporadic.Ly
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

namespace Ivk93M12FSpor

theorem empty_of_card {s : TauCeti.SporadicName} {n a m : ℕ}
    (hs : Nat.card (NativeSporadic.Carrier s) = n) (hm : Odd m) (hn : n = 2 ^ a * m)
    (h3 : a ≠ 3) (h5 : a ≠ 5) (h6 : a ≠ 6) :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X s) := by
  intro J _ _ hJ y hD
  obtain ⟨e⟩ := hJ
  exact Ivk93M12FAlt.false_of_card hD hm ((Nat.card_congr e.toEquiv).trans (hs.trans hn)) h3 h5 h6

end Ivk93M12FSpor

theorem ivk93m12_m11 :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .M11) :=
  Ivk93M12FSpor.empty_of_card (a := 4) (m := 495) CFSG.Sporadic.Mathieu.card_M11 (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem ivk93m12_m22 :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .M22) :=
  Ivk93M12FSpor.empty_of_card (a := 7) (m := 3465) CFSG.Sporadic.Mathieu.card_M22 (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem ivk93m12_m23 :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .M23) :=
  Ivk93M12FSpor.empty_of_card (a := 7) (m := 79695) CFSG.Sporadic.Schreier.m23_card (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem ivk93m12_j2 :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .J2) :=
  Ivk93M12FSpor.empty_of_card (a := 7) (m := 4725) CFSG.Sporadic.J2.card_J2 (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem ivk93m12_j3 :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .J3) :=
  Ivk93M12FSpor.empty_of_card (a := 7) (m := 392445) CFSG.Sporadic.J3.card_J3 (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem ivk93m12_mcl :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .McL) :=
  Ivk93M12FSpor.empty_of_card (a := 7) (m := 7016625) CFSG.Sporadic.McL.card_McL (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem ivk93m12_ly :
    Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .Ly) :=
  Ivk93M12FSpor.empty_of_card (a := 8) (m := 202207730484375) CFSG.Sporadic.Ly.card_Ly
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CFSG.GH74.GLS.IVK.Proofs2
