module

public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.Gen.Wrap
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.Th.Gen

structure FwdData where
  ThO_wA : Nat
  ThO_wB : Nat
  ThO_xw : Nat
  ThO_yw : Nat
  ThS_Bi : Nat
  ThS_GRf : Nat
  ThS_IRf : Nat
  ThS_ONE : Nat
  ThS_RBf : Nat → Nat
  ThS_c : Nat
  ThS_dg : Nat
  ThS_rm : Nat
  ThS_tm0 : Nat
  ThS_tm1 : Nat
  ThS_tm2 : Nat
  ThS_tm3 : Nat
  ThS_tm4 : Nat
  ThS_tm5 : Nat
  ThS_tm6 : Nat
  ThS_tm7 : Nat
  ThS_up : Nat
  ThS_w1 : Nat
  ThS_w2 : Nat
  ThSeed_LA : List Char
  ThSeed_LB : List Char
  ThSeed_SA : Nat
  ThSeed_SB : Nat
  ThSeed_SF : Nat
  cs0 : List Nat
  sf0 : Nat
  l0 : List Nat

@[expose] noncomputable def fwdChkGen (D : FwdData) : Bool :=
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.cs0 3) D.sf0)
  (CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA)
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.packOK D.ThSeed_SF CFSG.KC.Th.SeedS.fcRowsList)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SA) D.ThSeed_SF) D.ThSeed_SA) D.ThSeed_SF))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SB) D.ThSeed_SF) D.ThSeed_SB) D.ThSeed_SF)
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 1) D.ThSeed_SA))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 2) D.ThSeed_SB)
  (CFSG.KC.Th.Gen.eqN D.ThS_w1 327208660843949311569856638931134950366718123578765707520623978699011294545)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThS_w2 53118203310247861616881865655955129280624587562044029180903589568007838922)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 0))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 1)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 2)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 3)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 4))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 5)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 6)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 7)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 8))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 9)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 10))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 11)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 12))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 13)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 14)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 15)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 16))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 17)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 18)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 19)))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 20)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 21))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 22)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 23)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 24)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 25))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 26)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 27))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 28)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 29))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 30)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 31)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 32)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 33))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 34)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 35)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 36))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 37)
  (CFSG.KC.Th.BigS.relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf 38))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.invOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf)
  (CFSG.KC.Th.BigS.fixWOK D.ThS_RBf D.ThS_rm D.ThS_GRf D.ThS_w1 D.ThS_w2 7)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.regsIn D.ThS_GRf 8 D.sf0)
  (CFSG.KC.Th.BigS.regsIn D.ThS_IRf 8 D.sf0))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prodWord D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf D.ThO_wA 42) (D.ThS_RBf 1))
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prodWord D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf D.ThO_wB 44) (D.ThS_RBf 2)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 15) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi D.ThO_xw 33))
  (CFSG.KC.Th.chkInW D.ThS_rm D.ThS_w1 (D.ThS_RBf 15) D.ThS_w1 D.ThS_w2))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.chkInW D.ThS_rm D.ThS_w2 (D.ThS_RBf 15) D.ThS_w1 D.ThS_w2)
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 11) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi D.ThO_yw 115))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.chkInW D.ThS_rm D.ThS_w1 (D.ThS_RBf 11) D.ThS_w1 D.ThS_w2)
  (CFSG.KC.Th.chkInW D.ThS_rm D.ThS_w2 (D.ThS_RBf 11) D.ThS_w1 D.ThS_w2))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.notB (CFSG.KC.Th.andB (CFSG.KC.Th.chkInW D.ThS_rm D.ThS_w1 (D.ThS_RBf 2) D.ThS_w1 D.ThS_w2) (CFSG.KC.Th.chkInW D.ThS_rm D.ThS_w2 (D.ThS_RBf 2) D.ThS_w1 D.ThS_w2)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.runMarked D.l0 71303171) 131666978918167624115545384052890930534613496023380409048310005843204256303926497945151936657308930416465903099869240036831681489530891173033482234894671088796679326635859876046309954276853581002416070839727947005913431825845865304194434330924703944067877198237477948573099897714253895630370569423121548268)
  (CFSG.KC.Th.BigS.allMarked D.ThS_GRf 7 64290517049886535212668644557075649675104246105166215355620120040627078273401610324781219070951626179914991747983027361734219477310005455582754997507163617576503577458915955100737282361744912598835972089710911623981167883713801418063688638146828097689393163201893529576708934430788034975766879601133568))))))))

@[expose] noncomputable def fwdPins (D : FwdData) : Bool :=
  CFSG.KC.Th.andB (decide (D.l0 = D.cs0))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN D.sf0 2048)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThO_xw 19676527007948218914)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThO_yw
    546472502307675765001542338109559680589977148440078108285031978964036)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThS_RBf 2) D.ThS_Bi) D.ThS_ONE))))

@[expose] noncomputable def fwdChk (D : FwdData) : Bool :=
  CFSG.KC.Th.andB (fwdChkGen D) (fwdPins D)

end CFSG.KC.Th.Gen

end
