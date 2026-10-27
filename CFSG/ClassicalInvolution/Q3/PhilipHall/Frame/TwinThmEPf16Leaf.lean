module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf16E29
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

section Leaf

theorem e189ConclF_of_e64 {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
    (F : TwinDisc.ExitO2.Q8Fam Y Λ) (I : AEIdentOn Λ 7 AE.e64Sets AE.e64Sub)
    {K J : Subgroup Y} (hK : K ∈ Λ) (hJ : J ∈ Λ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    TwinThmEW.E189ConclF Λ K z t :=
  Or.inr (e189_e64_alt2 F I hK hJ hz ht hzt hne)

theorem e189ConclF_of_e29 {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
    (F : TwinDisc.ExitO2.Q8Fam Y Λ) (I : AEIdentOn Λ 8 AE.e29Sets AE.e29Sub)
    {K J : Subgroup Y} (hK : K ∈ Λ) (hJ : J ∈ Λ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    TwinThmEW.E189ConclF Λ K z t :=
  Or.inr (e189_e29_alt2 F I hK hJ hz ht hzt hne)

end Leaf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
