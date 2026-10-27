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

structure GenData where
  ThO_Gc0 : Nat
  ThO_Gc1 : Nat
  ThO_Gci0 : Nat
  ThO_Gci1 : Nat
  ThO_Ge01 : Nat
  ThO_Ge01i : Nat
  ThO_Ge02 : Nat
  ThO_Ge02i : Nat
  ThO_Ge11 : Nat
  ThO_Ge11i : Nat
  ThO_Ge12 : Nat
  ThO_Ge12i : Nat
  ThO_Gf0 : Nat
  ThO_Gf0a : Nat
  ThO_Gf1 : Nat
  ThO_Gf1a : Nat
  ThO_Gg0 : Nat
  ThO_Gg1 : Nat
  ThO_Ggi0 : Nat
  ThO_Ggi1 : Nat
  ThO_Gh01a : Nat
  ThO_Gh01b : Nat
  ThO_Gh02a : Nat
  ThO_Gh02b : Nat
  ThO_Gh11a : Nat
  ThO_Gh11b : Nat
  ThO_Gh12a : Nat
  ThO_Gh12b : Nat
  ThO_Gm0a : Nat
  ThO_Gm0b : Nat
  ThO_Gm0c : Nat
  ThO_Gm0d : Nat
  ThO_Gm1a : Nat
  ThO_Gm1b : Nat
  ThO_Gm1c : Nat
  ThO_Gm1d : Nat
  ThO_Gq0 : Nat
  ThO_Gs10 : Nat
  ThO_Gs7 : Nat
  ThO_Gs8 : Nat
  ThO_Gs8p : Nat
  ThO_Gs8pi : Nat
  ThO_Gs9 : Nat
  ThO_Gt3 : Nat
  ThO_Gt4 : Nat
  ThO_Gt5 : Nat
  ThO_Gt6 : Nat
  ThO_Gt7 : Nat
  ThO_Gt8 : Nat
  ThO_Gt8i : Nat
  ThO_Gu : Nat
  ThO_Gu9 : Nat
  ThO_Gv : Nat
  ThO_Gw0A_0 : Nat
  ThO_Gw0A_120 : Nat
  ThO_Gw0B_0 : Nat
  ThO_Gw0B_120 : Nat
  ThO_Gw1A_0 : Nat
  ThO_Gw1A_120 : Nat
  ThO_Gw1A_240 : Nat
  ThO_Gw1A_360 : Nat
  ThO_Gw1B_0 : Nat
  ThO_Gw1B_120 : Nat
  ThO_Gw1B_240 : Nat
  ThO_Gx : Nat
  ThO_Gxy : Nat
  ThO_Gy : Nat
  ThS_Bi : Nat
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

@[expose] noncomputable def genChk (D : GenData) : Bool :=
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
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB)
  (CFSG.KC.Th.SeedS.packOK D.ThSeed_SF CFSG.KC.Th.SeedS.fcRowsList))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SA) D.ThSeed_SF) D.ThSeed_SA) D.ThSeed_SF)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SB) D.ThSeed_SF) D.ThSeed_SB) D.ThSeed_SF)
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 1) D.ThSeed_SA)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 2) D.ThSeed_SB)
  (CFSG.KC.Th.Gen.eqN D.ThS_w1 327208660843949311569856638931134950366718123578765707520623978699011294545))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThS_w2 53118203310247861616881865655955129280624587562044029180903589568007838922)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThS_RBf 1) (D.ThS_RBf 2)) D.ThO_Gt3)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt3 (D.ThS_RBf 2)) D.ThO_Gt4))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt3 D.ThO_Gt4) D.ThO_Gt5)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt3 D.ThO_Gt5) D.ThO_Gt6)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThS_RBf 1) D.ThO_Gt6) D.ThO_Gt7)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt6 (D.ThS_RBf 1)) D.ThO_Gt8)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt8 D.ThO_Gt8i) D.ThS_ONE)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt8i D.ThO_Gt7) D.ThO_Gu))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt6 D.ThO_Gt5) D.ThO_Gs8)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt3 D.ThO_Gs8) D.ThO_Gs9))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gs9 D.ThO_Gt4) D.ThO_Gs10)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThS_RBf 1) D.ThO_Gs10) D.ThO_Gs7)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gs10 (D.ThS_RBf 1)) D.ThO_Gs8p))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gs8p D.ThO_Gs8pi) D.ThS_ONE)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gs8pi D.ThO_Gs7) D.ThO_Gv)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE D.ThO_Gv 14 4) D.ThO_Gx)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE D.ThO_Gu 9 4) D.ThO_Gu9)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gt7 D.ThO_Gu9) D.ThO_Gy)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gx D.ThO_Gy) D.ThO_Gxy)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE D.ThO_Gxy 6 3) D.ThO_Gq0)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi 276 5) D.ThO_Gg0))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gg0 D.ThO_Ggi0) D.ThS_ONE)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Ggi0 D.ThO_Gq0) D.ThO_Gm0a)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gm0a D.ThO_Gg0) D.ThO_Gm0b))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gm0b (D.ThS_RBf 1)) D.ThO_Gm0c)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE D.ThO_Gm0c 9 4) D.ThO_Gm0d)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gm0d D.ThO_Ggi0) D.ThO_Gc0)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gc0 D.ThO_Gci0) D.ThS_ONE)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gc0 D.ThO_Gq0) D.ThO_Gf0a)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gf0a D.ThO_Gci0) D.ThO_Gf0)))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThO_Gf0 (D.ThS_RBf 1))
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gx D.ThO_Gc0) D.ThO_Gh01a))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gci0 D.ThO_Gh01a) D.ThO_Gh01b)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gx D.ThO_Gh01b) D.ThO_Ge01)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Ge01 D.ThO_Ge01i) D.ThS_ONE))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gy D.ThO_Gc0) D.ThO_Gh02a)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gci0 D.ThO_Gh02a) D.ThO_Gh02b))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gy D.ThO_Gh02b) D.ThO_Ge02)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Ge02 D.ThO_Ge02i) D.ThS_ONE)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge01 D.ThO_Ge01i D.ThO_Ge02 D.ThO_Ge02i D.ThS_ONE 1027278180859423808880271384740128649384967473669434554152249017708992294 120) D.ThO_Gw0A_0)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge01 D.ThO_Ge01i D.ThO_Ge02 D.ThO_Ge02i D.ThO_Gw0A_0 263614083059063266606756910057115466782497025583418065728627199254028938 120) D.ThO_Gw0A_120)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge01 D.ThO_Ge01i D.ThO_Ge02 D.ThO_Ge02i D.ThO_Gw0A_120 6761439539694400935 32) (D.ThS_RBf 1)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge01 D.ThO_Ge01i D.ThO_Ge02 D.ThO_Ge02i D.ThS_ONE 676627602343317791726693622325835146997568335648219736413889782853105257 120) D.ThO_Gw0B_0)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge01 D.ThO_Ge01i D.ThO_Ge02 D.ThO_Ge02i D.ThO_Gw0B_0 943907118023717604658010226988766869776161375868683070462345935263520810 120) D.ThO_Gw0B_120)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge01 D.ThO_Ge01i D.ThO_Ge02 D.ThO_Ge02i D.ThO_Gw0B_120 496139095252823262175194688731370449733694409 75) (D.ThS_RBf 2)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi 17896517 13) D.ThO_Gg1)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gg1 D.ThO_Ggi1) D.ThS_ONE)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Ggi1 D.ThO_Gx) D.ThO_Gm1a)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gm1a D.ThO_Gg1) D.ThO_Gm1b)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gm1b (D.ThS_RBf 1)) D.ThO_Gm1c)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE D.ThO_Gm1c 9 4) D.ThO_Gm1d))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gm1d D.ThO_Ggi1) D.ThO_Gc1)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gc1 D.ThO_Gci1) D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gc1 D.ThO_Gx) D.ThO_Gf1a)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gf1a D.ThO_Gci1) D.ThO_Gf1)
  (CFSG.KC.Th.Gen.eqN D.ThO_Gf1 (D.ThS_RBf 1)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gx D.ThO_Gc1) D.ThO_Gh11a)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gci1 D.ThO_Gh11a) D.ThO_Gh11b)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gx D.ThO_Gh11b) D.ThO_Ge11)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i) D.ThS_ONE)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gy D.ThO_Gc1) D.ThO_Gh12a)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gci1 D.ThO_Gh12a) D.ThO_Gh12b)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Gy D.ThO_Gh12b) D.ThO_Ge12)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThO_Ge12 D.ThO_Ge12i) D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThS_ONE 1501988406389071177926184719493793470441306379507096141444258143427307775 120) D.ThO_Gw1A_0)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThO_Gw1A_0 1384208587369100569909010070574220977120798792021944172929749850523944951 120) D.ThO_Gw1A_120)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThO_Gw1A_120 281589046463145842781826300958726660131189133470885078451875770513399592 120) D.ThO_Gw1A_240))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThO_Gw1A_240 358543490039988152155403411809600425066585788531562028423206003789177807 120) D.ThO_Gw1A_360)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThO_Gw1A_360 4545000243104208823911 36) (D.ThS_RBf 1))
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThS_ONE 869566114126224557533052589676490613009370227541411561826569612677647500 120) D.ThO_Gw1B_0)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThO_Gw1B_0 1067008638450121353426132251298660843299559955987136692638446761720037238 120) D.ThO_Gw1B_120)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThO_Gw1B_120 1700597186383402818463584067717850942523653868672034968118830497347402953 120) D.ThO_Gw1B_240)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.prod4 D.ThS_c D.ThS_rm D.ThO_Ge11 D.ThO_Ge11i D.ThO_Ge12 D.ThO_Ge12i D.ThO_Gw1B_240 65116341059457502304052444286142540462783411091179250303 93) (D.ThS_RBf 2)))))))))

end CFSG.KC.Th.Gen

end
