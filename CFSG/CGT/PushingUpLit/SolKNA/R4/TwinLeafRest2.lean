module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16L34
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16M22
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16J2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16J3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafU34
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafJ1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLy
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafMcL
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafSz
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallList

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

@[expose] def LocalG23 : Prop := LocalNoQ16Q16' fun F _ => LieModel F .G2 0 3 1

@[expose] def LocalD43 : Prop := LocalNoQ16Q16' fun F _ => LieModel F .trialityD4 0 3 1

@[expose] def LocalM23 : Prop := LocalNoQ16Q16' fun F _ => NativeSporadic.IsSporadic F .M23

structure TwinLeafRest2 : Prop where
  g23 : LocalG23
  d43 : LocalD43
  l43 : LocalL43
  u43 : LocalU43
  l53 : LocalL53
  m23 : LocalM23

theorem twinLeafR_excludedRest_of_rest2 {r n : ℕ} (hr : 4 ≤ r) (hm23 : LocalM23) :
    TwinLeafR r n ExcludedRest :=
  twinLeafR_or (twinLeafR_of_noQ16Q16Aut hr autU34NoQ16Q16_holds)
    (twinLeafR_or (twinLeafR_of_noQ16Q16Aut hr autL34NoQ16Q16_of_cert)
      (twinLeafR_or (twinLeafR_sz8 hr)
        (twinLeafR_or (twinLeafR_of_noQ16Q16Aut hr autM22NoQ16Q16_holds)
          (twinLeafR_or (twinLeafR_of_local' hr hm23)
            (twinLeafR_or (twinLeafR_j1 hr)
              (twinLeafR_or (twinLeafR_of_noQ16Q16Aut hr autJ2NoQ16Q16_holds)
                (twinLeafR_or (twinLeafR_of_noQ16Q16Aut hr autJ3NoQ16Q16_holds)
                  (twinLeafR_or (twinLeafR_mcl hr) (twinLeafR_ly hr)))))))))

theorem twinLeavesR_of_rest2 {r : ℕ} (hr : 4 ≤ r) (n : ℕ) (I : TwinLeafRest2) :
    TwinLeavesR r n where
  g23 := twinLeafR_of_local' hr I.g23
  d43 := twinLeafR_of_local' hr I.d43
  l43 := twinLeafR_of_local hr I.l43
  u43 := twinLeafR_of_local hr I.u43
  l53 := twinLeafR_of_local hr I.l53
  excluded := twinLeafR_excludedRest_of_rest2 hr I.m23

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
