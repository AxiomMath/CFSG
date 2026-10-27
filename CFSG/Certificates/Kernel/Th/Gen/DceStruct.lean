module

public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.TcS
public import CFSG.Certificates.Kernel.Common.RelNorm
public import Certificates.Data.Kernel.LceSTab
public import CFSG.Certificates.Kernel.Th.Gen.Wrap
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.Th.Gen

structure DceStructData where
  ThA_AL : Nat
  ThA_CB : Nat → Nat
  ThA_E1 : Nat → Nat
  ThA_E2 : Nat → Nat
  ThA_FB : Nat → Nat
  ThA_GB : Nat → Nat
  ThA_HB : Nat → Nat
  ThA_I0 : Nat
  ThA_LC : Nat
  ThA_LI : Nat
  ThA_LT : Nat
  ThA_MD : Nat
  ThA_NB : Nat
  ThA_NCL : Nat
  ThA_ND : Nat
  ThA_NF : Nat
  ThA_NL : Nat
  ThA_NO : Nat
  ThA_NORD : Nat
  ThA_NR : Nat
  ThA_OB : Nat → Nat
  ThA_RH : Nat
  ThA_RR : Nat → Nat
  ThA_SG1 : Nat
  ThA_SG2 : Nat
  ThA_SUM : Nat
  ThA_TB : Nat → Nat
  ThA_TL : Nat
  ThA_UH : Nat
  ThA_USQ : Nat
  ThA_VL : Nat
  ThA_W : Nat
  ThA_WD : Nat → Nat
  ThA_WH : Nat
  ThA_Wi : Nat
  ThA_nH : Nat
  ThA_nT : Nat
  ThA_nW : Nat
  ThA_om : Nat
  ThA_osh : Nat
  ThA_owd : Nat
  ThA_sel : Nat
  ThB_AL : Nat
  ThB_E1 : Nat → Nat
  ThB_E10 : Nat → Nat
  ThB_E2 : Nat → Nat
  ThB_E3 : Nat → Nat
  ThB_E4 : Nat → Nat
  ThB_E5 : Nat → Nat
  ThB_E6 : Nat → Nat
  ThB_E7 : Nat → Nat
  ThB_E8 : Nat → Nat
  ThB_E9 : Nat → Nat
  ThB_FB : Nat → Nat
  ThB_GB : Nat → Nat
  ThB_HB : Nat → Nat
  ThB_I0 : Nat
  ThB_LC : Nat
  ThB_LI : Nat
  ThB_LT : Nat
  ThB_MD : Nat
  ThB_NB : Nat
  ThB_ND : Nat
  ThB_NF : Nat
  ThB_NL : Nat
  ThB_NO : Nat
  ThB_NR : Nat
  ThB_OB : Nat → Nat
  ThB_RH : Nat
  ThB_RR : Nat → Nat
  ThB_SG1 : Nat
  ThB_SG10 : Nat
  ThB_SG2 : Nat
  ThB_SG3 : Nat
  ThB_SG4 : Nat
  ThB_SG5 : Nat
  ThB_SG6 : Nat
  ThB_SG7 : Nat
  ThB_SG8 : Nat
  ThB_SG9 : Nat
  ThB_SUM : Nat
  ThB_TB : Nat → Nat
  ThB_TL : Nat
  ThB_UH : Nat
  ThB_USQ : Nat
  ThB_VL : Nat
  ThB_W : Nat
  ThB_WD : Nat → Nat
  ThB_WH : Nat
  ThB_Wi : Nat
  ThB_nH : Nat
  ThB_nT : Nat
  ThB_nW : Nat
  ThB_om : Nat
  ThB_osh : Nat
  ThB_owd : Nat
  ThB_sel : Nat
  ThK1_HS : Nat
  ThK1_INV : Nat
  ThK1_INV8 : Nat
  ThK1_LVs : Nat → Nat
  ThK1_blk : Nat → Nat
  ThK1_litRT : Nat → Nat
  ThK1_nC : Nat
  ThK1_nLive : Nat
  ThK1_selRT : Nat → Nat
  ThK1_selST : Nat → Nat
  ThK1_selWT : Nat → Nat
  ThK2_HS : Nat
  ThK2_INV : Nat
  ThK2_INV8 : Nat
  ThK2_LVs : Nat → Nat
  ThK2_blk : Nat → Nat
  ThK2_litRT : Nat → Nat
  ThK2_nC : Nat
  ThK2_nLive : Nat
  ThK2_selRT : Nat → Nat
  ThK2_selST : Nat → Nat
  ThK2_selWT : Nat → Nat
  ThK3_HS : Nat
  ThK3_INV : Nat
  ThK3_INV8 : Nat
  ThK3_LVs : Nat → Nat
  ThK3_blk : Nat → Nat
  ThK3_litRT : Nat → Nat
  ThK3_nC : Nat
  ThK3_nLive : Nat
  ThK3_selRT : Nat → Nat
  ThK3_selST : Nat → Nat
  ThK3_selWT : Nat → Nat
  ThO_CB2 : Nat → Nat
  cs0 : List Nat
  cs1 : List Nat
  sf1 : Nat
  cs2 : List Nat
  sf2 : Nat
  cs3 : List Nat
  cs4 : List Nat
  cs5 : List Nat
  sf5 : Nat
  cs6 : List Nat
  cs7 : List Nat
  sf7 : Nat
  cs8 : List Nat
  cs9 : List Nat
  cs10 : List Nat
  sf10 : Nat
  cs11 : List Nat
  cs12 : List Nat
  cs13 : List Nat
  cs14 : List Nat
  sf14 : Nat
  cs15 : List Nat
  sf15 : Nat
  cs16 : List Nat
  sf16 : Nat
  cs17 : List Nat
  sf17 : Nat
  cs18 : List Nat
  sf18 : Nat
  cs19 : List Nat
  sf19 : Nat
  cs20 : List Nat
  sf20 : Nat
  cs21 : List Nat
  sf21 : Nat
  cs22 : List Nat
  sf22 : Nat
  cs23 : List Nat
  sf23 : Nat
  cs24 : List Nat
  cs25 : List Nat
  cs26 : List Nat
  sf26 : Nat
  cs27 : List Nat
  cs28 : List Nat
  cs29 : List Nat
  cs30 : List Nat
  cs31 : List Nat
  cs32 : List Nat
  cs33 : List Nat
  cs34 : List Nat
  cs35 : List Nat
  cs36 : List Nat
  cs37 : List Nat
  sf37 : Nat
  cs38 : List Nat
  cs39 : List Nat
  sf39 : Nat
  cs40 : List Nat
  cs41 : List Nat
  sf41 : Nat
  cs42 : List Nat
  sf42 : Nat
  cs43 : List Nat
  sf43 : Nat
  cs44 : List Nat
  sf44 : Nat
  cs45 : List Nat
  sf45 : Nat
  cs46 : List Nat
  sf46 : Nat
  cs47 : List Nat
  sf47 : Nat
  cs48 : List Nat
  sf48 : Nat
  cs49 : List Nat
  sf49 : Nat

@[expose] noncomputable def dceStructChkGen (D : DceStructData) : Bool :=
  CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runCover D.ThA_FB D.ThA_OB 4 2336 D.ThA_osh D.ThA_owd D.ThA_om D.ThA_NB D.ThA_sel D.ThA_NF D.ThA_NO D.ThA_AL D.cs0 1) (Nat.add 1 (Nat.shiftLeft D.ThA_ND 20)))
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThA_E1) 17 (CFSG.KC.Th.DceS.bits D.ThA_MD 20 20) D.cs1 1) D.sf1))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThA_E2) 17 (CFSG.KC.Th.DceS.bits D.ThA_MD 40 20) D.cs2 1) D.sf2)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runGom D.ThA_HB D.ThA_GB D.ThA_OB D.ThA_osh D.ThA_owd D.ThA_om D.ThA_NB D.ThA_sel D.ThA_I0 D.ThA_nH D.cs3 1) (Nat.succ D.ThA_NO))
  (eqN (CFSG.KC.Th.DceS.runHdr D.ThA_HB D.ThA_FB D.ThA_LT D.ThA_TL D.ThA_VL D.ThA_NL 4 2336 0 D.cs4 1) (Nat.succ D.ThA_nH)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThA_CB) 10 D.ThA_NCL D.cs5 1) D.sf5)
  (eqN (CFSG.KC.Th.DceS.runClass D.ThA_CB D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL D.cs6 2) (Nat.succ D.ThA_NCL)))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.pt D.ThA_OB D.ThA_osh D.ThA_owd D.ThA_om) 15 D.ThA_NO D.cs7 1) D.sf7)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runStab D.ThA_FB D.ThA_E1 4 2336 D.ThA_NF 1 D.ThA_SG1 D.cs8 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThA_MD 20 20)))
  (eqN (CFSG.KC.Th.DceS.runStab D.ThA_FB D.ThA_E2 4 2336 D.ThA_NF 2 D.ThA_SG2 D.cs9 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThA_MD 40 20)))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.tSig D.ThA_HB D.ThA_TB) 17 D.ThA_nT D.cs10 1) D.sf10)
  (eqN (CFSG.KC.Th.DceS.runT D.ThA_HB D.ThA_TB D.ThA_OB D.ThA_RR D.ThA_FB D.ThA_LT D.ThA_TL D.ThA_VL D.ThA_NL D.ThA_NR D.ThA_nH D.ThA_nT D.ThA_osh D.ThA_owd D.ThA_om D.ThA_NB D.ThA_sel D.ThA_I0 4 2336 0 D.cs11 1) (Nat.succ D.ThA_nT)))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runFacts D.ThA_FB D.ThA_HB D.ThA_GB D.ThA_TB D.ThA_WD 4 2336 D.ThA_LT D.ThA_TL D.ThA_VL D.ThA_NL D.ThA_ND D.ThA_NO D.ThA_nH D.ThA_nT D.ThA_nW D.ThA_W D.ThA_Wi true D.cs12 4294967296) (CFSG.KC.Th.DceS.mkS D.ThA_NF D.ThA_ND))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runCover D.ThB_FB D.ThB_OB 5 1184 D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NB D.ThB_sel D.ThB_NF D.ThB_NO D.ThB_AL D.cs13 1) (Nat.add 1 (Nat.shiftLeft D.ThB_ND 20)))
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E10) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 200 20) D.cs14 1) D.sf14))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E1) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 20 20) D.cs15 1) D.sf15)
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E2) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 40 20) D.cs16 1) D.sf16))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E3) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 60 20) D.cs17 1) D.sf17)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E4) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 80 20) D.cs18 1) D.sf18)
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E5) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 100 20) D.cs19 1) D.sf19))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E6) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 120 20) D.cs20 1) D.sf20)
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E7) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 140 20) D.cs21 1) D.sf21))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E8) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 160 20) D.cs22 1) D.sf22)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E9) 17 (CFSG.KC.Th.DceS.bits D.ThB_MD 180 20) D.cs23 1) D.sf23)
  (eqN (CFSG.KC.Th.DceS.runGom D.ThB_HB D.ThB_GB D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NB D.ThB_sel D.ThB_I0 D.ThB_nH D.cs24 1) (Nat.succ D.ThB_NO)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runHdr D.ThB_HB D.ThA_FB D.ThB_LT D.ThB_TL D.ThB_VL D.ThB_NL 4 2336 D.ThA_NF D.cs25 1) (Nat.succ D.ThB_nH))
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om) 15 D.ThB_NO D.cs26 1) D.sf26))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E10 5 1184 D.ThB_NF 10 D.ThB_SG10 D.cs27 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 200 20)))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E1 5 1184 D.ThB_NF 1 D.ThB_SG1 D.cs28 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 20 20)))
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E2 5 1184 D.ThB_NF 2 D.ThB_SG2 D.cs29 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 40 20)))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E3 5 1184 D.ThB_NF 3 D.ThB_SG3 D.cs30 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 60 20)))
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E4 5 1184 D.ThB_NF 4 D.ThB_SG4 D.cs31 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 80 20))))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E5 5 1184 D.ThB_NF 5 D.ThB_SG5 D.cs32 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 100 20)))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E6 5 1184 D.ThB_NF 6 D.ThB_SG6 D.cs33 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 120 20)))
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E7 5 1184 D.ThB_NF 7 D.ThB_SG7 D.cs34 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 140 20))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E8 5 1184 D.ThB_NF 8 D.ThB_SG8 D.cs35 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 160 20)))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E9 5 1184 D.ThB_NF 9 D.ThB_SG9 D.cs36 2) (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 180 20)))
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.tSig D.ThB_HB D.ThB_TB) 17 D.ThB_nT D.cs37 1) D.sf37)))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runT D.ThB_HB D.ThB_TB D.ThB_OB D.ThB_RR D.ThA_FB D.ThB_LT D.ThB_TL D.ThB_VL D.ThB_NL D.ThB_NR D.ThB_nH D.ThB_nT D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NB D.ThB_sel D.ThB_I0 4 2336 D.ThA_NF D.cs38 1) (Nat.succ D.ThB_nT))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runFacts D.ThB_FB D.ThB_HB D.ThB_GB D.ThB_TB D.ThB_WD 5 1184 D.ThB_LT D.ThB_TL D.ThB_VL D.ThB_NL D.ThB_ND D.ThB_NO D.ThB_nH D.ThB_nT D.ThB_nW D.ThB_W D.ThB_Wi false D.cs39 4294967296) D.sf39)
  (eqN (CFSG.KC.Th.DceS.runFacts D.ThB_FB D.ThB_HB D.ThB_GB D.ThB_TB D.ThB_WD 5 1184 D.ThB_LT D.ThB_TL D.ThB_VL D.ThB_NL D.ThB_ND D.ThB_NO D.ThB_nH D.ThB_nT D.ThB_nW D.ThB_W D.ThB_Wi false D.cs40 34359948128) (CFSG.KC.Th.DceS.mkS D.ThB_NF D.ThB_ND))))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runFacts D.ThB_FB D.ThB_HB D.ThB_GB D.ThB_TB D.ThB_WD 5 1184 D.ThB_LT D.ThB_TL D.ThB_VL D.ThB_NL D.ThB_ND D.ThB_NO D.ThB_nH D.ThB_nT D.ThB_nW D.ThB_W D.ThB_Wi false D.cs41 8589985856) D.sf41)
  (eqN (CFSG.KC.LceS.runCover D.ThK1_blk D.ThK1_LVs 77723 10 D.cs42 1) D.sf42))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.LceS.runFacts D.ThK1_blk D.ThK1_selWT D.ThK1_INV D.ThK1_nC 10 D.cs43 4294967296) D.sf43)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.LceS.runCover D.ThK2_blk D.ThK2_LVs 173901 12 D.cs44 1) D.sf44)
  (eqN (CFSG.KC.LceS.runFacts D.ThK2_blk D.ThK2_selWT D.ThK2_INV D.ThK2_nC 12 D.cs45 4294967296) D.sf45))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.LceS.runCover D.ThK3_blk D.ThK3_LVs 551839 14 D.cs46 1) D.sf46)
  (eqN (CFSG.KC.LceS.runFacts D.ThK3_blk D.ThK3_selWT D.ThK3_INV D.ThK3_nC 14 D.cs47 4294967296) D.sf47))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.OutS.runClass2 D.ThO_CB2 D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL D.cs48 2) D.sf48)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThO_CB2) 17 68796 D.cs49 1) D.sf49)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf1) (CFSG.KC.Th.DceS.bits D.ThA_MD 20 20))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf2) (CFSG.KC.Th.DceS.bits D.ThA_MD 40 20))
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf5) D.ThA_NCL))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf7) D.ThA_NO)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf10) D.ThA_nT)
  (CFSG.KC.Th.DceS.lettersOK D.ThA_LT D.ThA_LC D.ThA_LI D.ThA_TL D.ThA_VL D.ThA_NL))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.relsOK D.ThA_RR D.ThA_LT D.ThA_LC D.ThA_TL D.ThA_VL D.ThA_NL D.ThA_RH D.ThA_NR)
  (CFSG.KC.Th.DceS.wordsOK D.ThA_WD D.ThA_RR D.ThA_LI D.ThA_NL D.ThA_NR D.ThA_WH D.ThA_nW))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.usqOK D.ThA_RR D.ThA_LT D.ThA_LI D.ThA_TL D.ThA_VL D.ThA_NL D.ThA_NR D.ThA_USQ D.ThA_W D.ThA_Wi D.ThA_UH)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.selOK D.ThA_NB D.ThA_sel)
  (CFSG.KC.Th.Gen.eqN D.ThA_om (Nat.sub (Nat.shiftLeft 1 (Nat.mul 24 D.ThA_NB)) 1)))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThA_owd (Nat.mul 24 D.ThA_NB))
  (CFSG.KC.Th.Gen.ltN D.ThA_I0 D.ThA_NO))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (Nat.mul D.ThA_nT D.ThA_NO) D.ThA_NORD)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.sumOK D.ThA_AL D.ThA_MD D.ThA_ND D.ThA_NORD D.ThA_SUM)
  (CFSG.KC.Th.DceS.stabStart D.ThA_E1))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.stabStart D.ThA_E2)
  (CFSG.KC.Th.DceS.lettersSub D.ThA_LT D.ThA_LC D.ThA_TL D.ThA_VL D.ThA_NL D.ThB_LT))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.commOK D.ThA_LT D.ThA_TL D.ThA_VL D.ThA_NL (CFSG.KC.Th.DceS.let24 D.ThB_LT 0))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.mat D.ThA_CB 0) (CFSG.KC.Th.DceS.let24 D.ThB_LT 0))
  (CFSG.KC.Th.Gen.eqN (Nat.mod (Nat.mul D.ThK1_nLive D.ThK3_nLive) D.ThA_NCL) 0)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThA_NORD (Nat.div (Nat.mul D.ThK1_nLive D.ThK3_nLive) D.ThA_NCL))
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf14) (CFSG.KC.Th.DceS.bits D.ThB_MD 200 20)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf37) (CFSG.KC.Th.DceS.bits D.ThB_MD 20 20))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf16) (CFSG.KC.Th.DceS.bits D.ThB_MD 40 20))
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf17) (CFSG.KC.Th.DceS.bits D.ThB_MD 60 20)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf18) (CFSG.KC.Th.DceS.bits D.ThB_MD 80 20))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf19) (CFSG.KC.Th.DceS.bits D.ThB_MD 100 20))
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf20) (CFSG.KC.Th.DceS.bits D.ThB_MD 120 20))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf21) (CFSG.KC.Th.DceS.bits D.ThB_MD 140 20))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf22) (CFSG.KC.Th.DceS.bits D.ThB_MD 160 20))
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf23) (CFSG.KC.Th.DceS.bits D.ThB_MD 180 20)))))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf26) D.ThB_NO)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf37) D.ThB_nT))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.lettersOK D.ThB_LT D.ThB_LC D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.relsOK D.ThB_RR D.ThB_LT D.ThB_LC D.ThB_TL D.ThB_VL D.ThB_NL D.ThB_RH D.ThB_NR)
  (CFSG.KC.Th.DceS.wordsOK D.ThB_WD D.ThB_RR D.ThB_LI D.ThB_NL D.ThB_NR D.ThB_WH D.ThB_nW))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.usqOK D.ThB_RR D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL D.ThB_NR D.ThB_USQ D.ThB_W D.ThB_Wi D.ThB_UH)
  (CFSG.KC.Th.DceS.selOK D.ThB_NB D.ThB_sel))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThB_om (Nat.sub (Nat.shiftLeft 1 (Nat.mul 24 D.ThB_NB)) 1))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThB_owd (Nat.mul 24 D.ThB_NB))
  (CFSG.KC.Th.Gen.ltN D.ThB_I0 D.ThB_NO)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (Nat.mul D.ThB_nT D.ThB_NO) (Nat.mul D.ThK1_nLive D.ThK3_nLive))
  (CFSG.KC.Th.DceS.sumOK D.ThB_AL D.ThB_MD D.ThB_ND (Nat.mul D.ThK1_nLive D.ThK3_nLive) D.ThB_SUM))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.stabStart D.ThB_E1)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.stabStart D.ThB_E2)
  (CFSG.KC.Th.DceS.stabStart D.ThB_E3))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.stabStart D.ThB_E4)
  (CFSG.KC.Th.DceS.stabStart D.ThB_E5))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.stabStart D.ThB_E6)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.stabStart D.ThB_E7)
  (CFSG.KC.Th.DceS.stabStart D.ThB_E8))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.DceS.stabStart D.ThB_E9)
  (CFSG.KC.Th.DceS.stabStart D.ThB_E10))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThB_NL 16)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThB_LC 20011376718272490338853433276725592320)
  (CFSG.KC.Th.Gen.eqN D.ThB_NR 39))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThB_RH 1243246491195555662985712545119472705112553111610534931758030933907000127540406711912033812736)
  (CFSG.KC.Th.Gen.eqN (Nat.mul (Nat.mul D.ThK1_nLive D.ThK3_nLive) D.ThB_SUM) 90745943887872000))
  (CFSG.KC.Th.andB
  (CFSG.KC.LceS.wordsOK D.ThK1_selWT D.ThK1_selRT D.ThK1_selST D.ThK1_INV D.ThK1_INV8 256 D.ThK1_HS)
  (CFSG.KC.Th.andB
  (CFSG.KC.LceS.invOK D.ThK1_INV D.ThK1_INV8 10)
  (CFSG.KC.LceS.aliveOK D.ThK1_LVs 5 16923 D.ThK1_nLive)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThK1_nC 16923)
  (CFSG.KC.Th.TcS.litOK D.ThK1_litRT 14))
  (CFSG.KC.Th.andB
  (CFSG.KC.LceS.wordsOK D.ThK2_selWT D.ThK2_selRT D.ThK2_selST D.ThK2_INV D.ThK2_INV8 512 D.ThK2_HS)
  (CFSG.KC.Th.andB
  (CFSG.KC.LceS.invOK D.ThK2_INV D.ThK2_INV8 12)
  (CFSG.KC.LceS.aliveOK D.ThK2_LVs 10 39573 D.ThK2_nLive))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThK2_nC 39573)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.TcS.litOK D.ThK2_litRT 20)
  (CFSG.KC.LceS.wordsOK D.ThK3_selWT D.ThK3_selRT D.ThK3_selST D.ThK3_INV D.ThK3_INV8 512 D.ThK3_HS)))
  (CFSG.KC.Th.andB
  (CFSG.KC.LceS.invOK D.ThK3_INV D.ThK3_INV8 14)
  (CFSG.KC.Th.andB
  (CFSG.KC.LceS.aliveOK D.ThK3_LVs 27 106919 D.ThK3_nLive)
  (CFSG.KC.Th.Gen.eqN D.ThK3_nC 106919)))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.TcS.litOK D.ThK3_litRT 27)
  (CFSG.KC.Th.OutS.invRank 6 (CFSG.KC.Th.DceS.let24 D.ThB_LT 0)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 0 2048 32) 15)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 2048 2048 32) 6)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 4096 2048 32) 4))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 6144 2048 32) 2)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 8192 2048 32) 2))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 10240 2048 32) 2)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 12288 2048 32) 0)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 14336 2048 32) 2)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 16384 2048 32) 0)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 18432 2048 32) 0))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 20480 2048 32) 1)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 22528 2048 32) 1)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 24576 2048 32) 2))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 26624 2048 32) 4)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 28672 2048 32) 0)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 30720 2048 32) 0)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 32768 2048 32) 8)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E1 34816 2048 32) 2)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E2 0 2048 32) 5))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E2 2048 2048 32) 2)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E2 4096 2048 32) 0))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E2 6144 2048 32) 0)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E2 8192 2048 32) 0)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E2 10240 2048 32) 4))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E2 12288 1536 24) 8)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E3 0 486 8) 0))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E4 0 288 5) 3)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E5 0 54 1) 0)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E6 0 6 1) 0)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E7 0 126 2) 0)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E8 0 78 2) 0))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E9 0 72 2) 0)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E10 0 2048 32) 0)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.OutS.countA D.ThB_E10 2048 1480 24) 0))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.OutS.coreOK D.ThB_E6 D.ThB_LT D.ThB_LI 2 6)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.mat D.ThO_CB2 0) (CFSG.KC.Th.DceS.mat D.ThB_E1 3))
  (CFSG.KC.Th.OutS.invRank 12 (CFSG.KC.Th.DceS.mat D.ThO_CB2 0))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf49) 68796)
  (CFSG.KC.Th.andB
  (CFSG.KC.relsNorm D.ThA_RR 29)
  (CFSG.KC.relsNorm D.ThB_RR 39)))))))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN D.ThA_ND 255)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN D.ThB_ND 12)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN D.ThA_NF 4294967296)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN D.ThB_NF 4294967296)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.leN D.ThA_NR 29)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf39 (CFSG.KC.Th.DceS.mkS D.ThB_NF D.ThB_ND))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf15)
    (CFSG.KC.Th.DceS.bits D.ThB_MD 20 20))
  (CFSG.KC.Th.andB (CFSG.KC.Th.DceS.notB (CFSG.KC.Th.DceS.recOK D.ThA_ND D.ThA_NO true
    (CFSG.KC.Th.DceS.rec D.ThA_FB 4 2336 D.ThA_NF)))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf42 16924)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf43 (CFSG.KC.LceS.mkS 77723 16923))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf44 39574)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf45 (CFSG.KC.LceS.mkS 173901 39573))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf46 106920)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf47 (CFSG.KC.LceS.mkS 551839 106919))
  (CFSG.KC.Th.andB (CFSG.KC.Bind.hintsOK D.ThK1_selWT 256 14 0 D.ThK1_HS)
  (CFSG.KC.Th.andB (CFSG.Certificates.LCE.wtPer D.ThK1_selWT 256)
  (CFSG.KC.Th.andB (CFSG.KC.Th.TcS.litOK D.ThK1_selRT 14)
  (CFSG.KC.Th.andB (CFSG.KC.Bind.hintsOK D.ThK3_selWT 512 27 5 D.ThK3_HS)
  (CFSG.KC.Th.andB (CFSG.Certificates.LCE.wtPer D.ThK3_selWT 512)
  (CFSG.KC.Th.andB (CFSG.KC.Th.TcS.litOK D.ThK3_selRT 27)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN (D.ThK3_selST 0) 4)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN (D.ThK3_selST 1) 8196)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN (D.ThK3_selST 2) 16388)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN (D.ThK3_selST 3) 24580)
  (CFSG.KC.Th.Gen.eqN (D.ThK3_selST 4) 32772)))))))))))))))))))))))))

@[expose] noncomputable def dceStructPins (D : DceStructData) : Bool :=
  CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThB_ND 11)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThB_AL 2047)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThB_MD
    5669277530485510631759370250422092589367217792282136242055806976)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN (Nat.mul D.ThK1_nLive D.ThK3_nLive) 634023936)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThA_NCL 819)
  (CFSG.KC.Th.Gen.eqN D.sf48 68797)))))

@[expose] noncomputable def dceStructChk (D : DceStructData) : Bool :=
  CFSG.KC.Th.andB (dceStructChkGen D) (dceStructPins D)

end CFSG.KC.Th.Gen


end
