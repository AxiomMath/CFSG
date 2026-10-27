module

public import CFSG.Certificates.Kernel.Th.Gen.Dce

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th.Gen

theorem andL {a b : Bool} (h : CFSG.KC.Th.andB a b = true) : a = true := andB_left h

theorem andR {a b : Bool} (h : CFSG.KC.Th.andB a b = true) : b = true := andB_right h

structure Chk (D : DceData) : Prop where
  a_gom :
    (CFSG.KC.Th.DceS.runGom D.ThA_HB D.ThA_GB D.ThA_OB D.ThA_osh D.ThA_owd D.ThA_om
    D.ThA_NB D.ThA_sel D.ThA_I0 D.ThA_nH D.cs3 1) = (Nat.succ D.ThA_NO)
  a_hdr :
    (CFSG.KC.Th.DceS.runHdr D.ThA_HB D.ThA_FB D.ThA_LT D.ThA_TL D.ThA_VL D.ThA_NL 4 2336 0
    D.cs4 1) = (Nat.succ D.ThA_nH)
  a_psi :
    (CFSG.KC.Th.DceS.runT D.ThA_HB D.ThA_TB D.ThA_OB D.ThA_RR D.ThA_FB D.ThA_LT D.ThA_TL
    D.ThA_VL D.ThA_NL D.ThA_NR D.ThA_nH D.ThA_nT D.ThA_osh D.ThA_owd D.ThA_om D.ThA_NB D.ThA_sel
    D.ThA_I0 4 2336 0 D.cs11 1) = (Nat.succ D.ThA_nT)
  a_facts :
    (CFSG.KC.Th.DceS.runFacts D.ThA_FB D.ThA_HB D.ThA_GB D.ThA_TB D.ThA_WD 4 2336
    D.ThA_LT D.ThA_TL D.ThA_VL D.ThA_NL D.ThA_ND D.ThA_NO D.ThA_nH D.ThA_nT D.ThA_nW D.ThA_W
    D.ThA_Wi true D.cs12 4294967296) = (CFSG.KC.Th.DceS.mkS D.ThA_NF D.ThA_ND)
  b_cover :
    (CFSG.KC.Th.DceS.runCover D.ThB_FB D.ThB_OB 5 1184 D.ThB_osh D.ThB_owd D.ThB_om
    D.ThB_NB D.ThB_sel D.ThB_NF D.ThB_NO D.ThB_AL D.cs13 1) = (Nat.add 1 (Nat.shiftLeft D.ThB_ND
    20))
  b_sorted10 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E10) 17
    (CFSG.KC.Th.DceS.bits D.ThB_MD 200 20) D.cs14 1) = D.sf14
  b_sorted1 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E1) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 20 20) D.cs15 1) = D.sf15
  b_sorted2 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E2) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 40 20) D.cs16 1) = D.sf16
  b_sorted3 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E3) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 60 20) D.cs17 1) = D.sf17
  b_sorted4 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E4) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 80 20) D.cs18 1) = D.sf18
  b_sorted5 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E5) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 100 20) D.cs19 1) = D.sf19
  b_sorted6 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E6) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 120 20) D.cs20 1) = D.sf20
  b_sorted7 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E7) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 140 20) D.cs21 1) = D.sf21
  b_sorted8 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E8) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 160 20) D.cs22 1) = D.sf22
  b_sorted9 :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat D.ThB_E9) 17 (CFSG.KC.Th.DceS.bits
    D.ThB_MD 180 20) D.cs23 1) = D.sf23
  b_gom :
    (CFSG.KC.Th.DceS.runGom D.ThB_HB D.ThB_GB D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om
    D.ThB_NB D.ThB_sel D.ThB_I0 D.ThB_nH D.cs24 1) = (Nat.succ D.ThB_NO)
  b_hdr :
    (CFSG.KC.Th.DceS.runHdr D.ThB_HB D.ThA_FB D.ThB_LT D.ThB_TL D.ThB_VL D.ThB_NL 4 2336
    D.ThA_NF D.cs25 1) = (Nat.succ D.ThB_nH)
  b_pts :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om)
    15 D.ThB_NO D.cs26 1) = D.sf26
  b_stab10 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E10 5 1184 D.ThB_NF 10 D.ThB_SG10 D.cs27 2)
    = (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 200 20))
  b_stab1 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E1 5 1184 D.ThB_NF 1 D.ThB_SG1 D.cs28 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 20 20))
  b_stab2 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E2 5 1184 D.ThB_NF 2 D.ThB_SG2 D.cs29 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 40 20))
  b_stab3 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E3 5 1184 D.ThB_NF 3 D.ThB_SG3 D.cs30 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 60 20))
  b_stab4 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E4 5 1184 D.ThB_NF 4 D.ThB_SG4 D.cs31 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 80 20))
  b_stab5 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E5 5 1184 D.ThB_NF 5 D.ThB_SG5 D.cs32 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 100 20))
  b_stab6 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E6 5 1184 D.ThB_NF 6 D.ThB_SG6 D.cs33 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 120 20))
  b_stab7 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E7 5 1184 D.ThB_NF 7 D.ThB_SG7 D.cs34 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 140 20))
  b_stab8 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E8 5 1184 D.ThB_NF 8 D.ThB_SG8 D.cs35 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 160 20))
  b_stab9 :
    (CFSG.KC.Th.DceS.runStab D.ThB_FB D.ThB_E9 5 1184 D.ThB_NF 9 D.ThB_SG9 D.cs36 2) =
    (Nat.succ (CFSG.KC.Th.DceS.bits D.ThB_MD 180 20))
  b_tsig :
    (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.tSig D.ThB_HB D.ThB_TB) 17 D.ThB_nT
    D.cs37 1) = D.sf37
  b_psi :
    (CFSG.KC.Th.DceS.runT D.ThB_HB D.ThB_TB D.ThB_OB D.ThB_RR D.ThA_FB D.ThB_LT D.ThB_TL
    D.ThB_VL D.ThB_NL D.ThB_NR D.ThB_nH D.ThB_nT D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NB D.ThB_sel
    D.ThB_I0 4 2336 D.ThA_NF D.cs38 1) = (Nat.succ D.ThB_nT)
  b_facts1 :
    (CFSG.KC.Th.DceS.runFacts D.ThB_FB D.ThB_HB D.ThB_GB D.ThB_TB D.ThB_WD 5 1184
    D.ThB_LT D.ThB_TL D.ThB_VL D.ThB_NL D.ThB_ND D.ThB_NO D.ThB_nH D.ThB_nT D.ThB_nW D.ThB_W
    D.ThB_Wi false D.cs39 4294967296) = D.sf39
  k1_cover :
    (CFSG.KC.LceS.runCover D.ThK1_blk D.ThK1_LVs 77723 10 D.cs42 1) = D.sf42
  k1_facts :
    (CFSG.KC.LceS.runFacts D.ThK1_blk D.ThK1_selWT D.ThK1_INV D.ThK1_nC 10 D.cs43
    4294967296) = D.sf43
  k3_cover :
    (CFSG.KC.LceS.runCover D.ThK3_blk D.ThK3_LVs 551839 14 D.cs46 1) = D.sf46
  k3_facts :
    (CFSG.KC.LceS.runFacts D.ThK3_blk D.ThK3_selWT D.ThK3_INV D.ThK3_nC 14 D.cs47
    4294967296) = D.sf47
  a_letters :
    (CFSG.KC.Th.DceS.lettersOK D.ThA_LT D.ThA_LC D.ThA_LI D.ThA_TL D.ThA_VL D.ThA_NL)
    = true
  a_rels :
    (CFSG.KC.Th.DceS.relsOK D.ThA_RR D.ThA_LT D.ThA_LC D.ThA_TL D.ThA_VL D.ThA_NL
    D.ThA_RH D.ThA_NR) = true
  a_words :
    (CFSG.KC.Th.DceS.wordsOK D.ThA_WD D.ThA_RR D.ThA_LI D.ThA_NL D.ThA_NR D.ThA_WH
    D.ThA_nW) = true
  a_usq :
    (CFSG.KC.Th.DceS.usqOK D.ThA_RR D.ThA_LT D.ThA_LI D.ThA_TL D.ThA_VL D.ThA_NL D.ThA_NR
    D.ThA_USQ D.ThA_W D.ThA_Wi D.ThA_UH) = true
  a_sub :
    (CFSG.KC.Th.DceS.lettersSub D.ThA_LT D.ThA_LC D.ThA_TL D.ThA_VL D.ThA_NL D.ThB_LT) =
    true
  b_cnt10 :
    (CFSG.KC.Th.DceS.sortedCount D.sf14) = (CFSG.KC.Th.DceS.bits D.ThB_MD 200 20)
  b_cnt2 :
    (CFSG.KC.Th.DceS.sortedCount D.sf16) = (CFSG.KC.Th.DceS.bits D.ThB_MD 40 20)
  b_cnt3 :
    (CFSG.KC.Th.DceS.sortedCount D.sf17) = (CFSG.KC.Th.DceS.bits D.ThB_MD 60 20)
  b_cnt4 :
    (CFSG.KC.Th.DceS.sortedCount D.sf18) = (CFSG.KC.Th.DceS.bits D.ThB_MD 80 20)
  b_cnt5 :
    (CFSG.KC.Th.DceS.sortedCount D.sf19) = (CFSG.KC.Th.DceS.bits D.ThB_MD 100 20)
  b_cnt6 :
    (CFSG.KC.Th.DceS.sortedCount D.sf20) = (CFSG.KC.Th.DceS.bits D.ThB_MD 120 20)
  b_cnt7 :
    (CFSG.KC.Th.DceS.sortedCount D.sf21) = (CFSG.KC.Th.DceS.bits D.ThB_MD 140 20)
  b_cnt8 :
    (CFSG.KC.Th.DceS.sortedCount D.sf22) = (CFSG.KC.Th.DceS.bits D.ThB_MD 160 20)
  b_cnt9 :
    (CFSG.KC.Th.DceS.sortedCount D.sf23) = (CFSG.KC.Th.DceS.bits D.ThB_MD 180 20)
  b_cntpts :
    (CFSG.KC.Th.DceS.sortedCount D.sf26) = D.ThB_NO
  b_cnttsig :
    (CFSG.KC.Th.DceS.sortedCount D.sf37) = D.ThB_nT
  b_letters :
    (CFSG.KC.Th.DceS.lettersOK D.ThB_LT D.ThB_LC D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL)
    = true
  b_rels :
    (CFSG.KC.Th.DceS.relsOK D.ThB_RR D.ThB_LT D.ThB_LC D.ThB_TL D.ThB_VL D.ThB_NL
    D.ThB_RH D.ThB_NR) = true
  b_words :
    (CFSG.KC.Th.DceS.wordsOK D.ThB_WD D.ThB_RR D.ThB_LI D.ThB_NL D.ThB_NR D.ThB_WH
    D.ThB_nW) = true
  b_usq :
    (CFSG.KC.Th.DceS.usqOK D.ThB_RR D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL D.ThB_NR
    D.ThB_USQ D.ThB_W D.ThB_Wi D.ThB_UH) = true
  b_sel :
    (CFSG.KC.Th.DceS.selOK D.ThB_NB D.ThB_sel) = true
  b_om :
    D.ThB_om = (Nat.sub (Nat.shiftLeft 1 (Nat.mul 24 D.ThB_NB)) 1)
  b_owd :
    D.ThB_owd = (Nat.mul 24 D.ThB_NB)
  b_i0 :
    D.ThB_I0 < D.ThB_NO
  b_nord :
    (Nat.mul D.ThB_nT D.ThB_NO) = (Nat.mul D.ThK1_nLive D.ThK3_nLive)
  b_sum :
    (CFSG.KC.Th.DceS.sumOK D.ThB_AL D.ThB_MD D.ThB_ND (Nat.mul D.ThK1_nLive D.ThK3_nLive)
    D.ThB_SUM) = true
  b_start1 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E1) = true
  b_start2 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E2) = true
  b_start3 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E3) = true
  b_start4 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E4) = true
  b_start5 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E5) = true
  b_start6 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E6) = true
  b_start7 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E7) = true
  b_start8 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E8) = true
  b_start9 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E9) = true
  b_start10 :
    (CFSG.KC.Th.DceS.stabStart D.ThB_E10) = true
  b_nl :
    D.ThB_NL = 16
  b_lc :
    D.ThB_LC = 20011376718272490338853433276725592320
  b_nr :
    D.ThB_NR = 39
  b_rh :
    D.ThB_RH =
    1243246491195555662985712545119472705112553111610534931758030933907000127540406711912033812736
  b_order :
    (Nat.mul (Nat.mul D.ThK1_nLive D.ThK3_nLive) D.ThB_SUM) = 90745943887872000
  k1_words :
    (CFSG.KC.LceS.wordsOK D.ThK1_selWT D.ThK1_selRT D.ThK1_selST D.ThK1_INV D.ThK1_INV8
    256 D.ThK1_HS) = true
  k1_inv :
    (CFSG.KC.LceS.invOK D.ThK1_INV D.ThK1_INV8 10) = true
  k1_alive :
    (CFSG.KC.LceS.aliveOK D.ThK1_LVs 5 16923 D.ThK1_nLive) = true
  k1_nc :
    D.ThK1_nC = 16923
  k3_words :
    (CFSG.KC.LceS.wordsOK D.ThK3_selWT D.ThK3_selRT D.ThK3_selST D.ThK3_INV D.ThK3_INV8
    512 D.ThK3_HS) = true
  k3_inv :
    (CFSG.KC.LceS.invOK D.ThK3_INV D.ThK3_INV8 14) = true
  k3_alive :
    (CFSG.KC.LceS.aliveOK D.ThK3_LVs 27 106919 D.ThK3_nLive) = true
  k3_nc :
    D.ThK3_nC = 106919
  a_norm :
    (CFSG.KC.relsNorm D.ThA_RR 29) = true
  b_norm :
    (CFSG.KC.relsNorm D.ThB_RR 39) = true
  a_nd :
    D.ThA_ND < 255
  b_nd :
    D.ThB_ND < 12
  a_nf :
    D.ThA_NF < 4294967296
  b_nf :
    D.ThB_NF < 4294967296
  a_nr :
    D.ThA_NR ≤ 29
  b_sf39 :
    D.sf39 = (CFSG.KC.Th.DceS.mkS D.ThB_NF D.ThB_ND)
  b_cnt1 :
    (CFSG.KC.Th.DceS.sortedCount D.sf15) = (CFSG.KC.Th.DceS.bits D.ThB_MD 20 20)
  a_term :
    (CFSG.KC.Th.DceS.notB (CFSG.KC.Th.DceS.recOK D.ThA_ND D.ThA_NO true
    (CFSG.KC.Th.DceS.rec D.ThA_FB 4 2336 D.ThA_NF))) = true
  k1_sf42 :
    D.sf42 = 16924
  k1_sf43 :
    D.sf43 = (CFSG.KC.LceS.mkS 77723 16923)
  k3_sf46 :
    D.sf46 = 106920
  k3_sf47 :
    D.sf47 = (CFSG.KC.LceS.mkS 551839 106919)
  k1_hints :
    (CFSG.KC.Bind.hintsOK D.ThK1_selWT 256 14 0 D.ThK1_HS) = true
  k1_per :
    (CFSG.Certificates.LCE.wtPer D.ThK1_selWT 256) = true
  k1_rt :
    (CFSG.KC.Th.TcS.litOK D.ThK1_selRT 14) = true
  k3_hints :
    (CFSG.KC.Bind.hintsOK D.ThK3_selWT 512 27 5 D.ThK3_HS) = true
  k3_per :
    (CFSG.Certificates.LCE.wtPer D.ThK3_selWT 512) = true
  k3_rt :
    (CFSG.KC.Th.TcS.litOK D.ThK3_selRT 27) = true
  k3_st0 :
    (D.ThK3_selST 0) = 4
  k3_st1 :
    (D.ThK3_selST 1) = 8196
  k3_st2 :
    (D.ThK3_selST 2) = 16388
  k3_st3 :
    (D.ThK3_selST 3) = 24580
  k3_st4 :
    (D.ThK3_selST 4) = 32772

theorem chk_of (D : DceData) (h : dceChk D = true) : Chk D := by
  unfold dceChk at h
  have n := h
  have nL := andL n
  have nR := andR n
  have nLL := andL nL
  have nLR := andR nL
  have nRL := andL nR
  have nRR := andR nR
  have nLLL := andL nLL
  have nLLR := andR nLL
  have nLRL := andL nLR
  have nLRR := andR nLR
  have nRRL := andL nRR
  have nRRR := andR nRR
  have nLLLL := andL nLLL
  have nLLLR := andR nLLL
  have nLLRL := andL nLLR
  have nLLRR := andR nLLR
  have nLRLL := andL nLRL
  have nLRLR := andR nLRL
  have nLRRL := andL nLRR
  have nLRRR := andR nLRR
  have nRRRL := andL nRRR
  have nRRRR := andR nRRR
  have nLLLLL := andL nLLLL
  have nLLLLR := andR nLLLL
  have nLLLRL := andL nLLLR
  have nLLLRR := andR nLLLR
  have nLLRLL := andL nLLRL
  have nLLRLR := andR nLLRL
  have nLLRRL := andL nLLRR
  have nLLRRR := andR nLLRR
  have nLRLLL := andL nLRLL
  have nLRLLR := andR nLRLL
  have nLRLRL := andL nLRLR
  have nLRLRR := andR nLRLR
  have nLRRLL := andL nLRRL
  have nLRRLR := andR nLRRL
  have nLRRRL := andL nLRRR
  have nLRRRR := andR nLRRR
  have nRRRRL := andL nRRRR
  have nRRRRR := andR nRRRR
  have nLLLLLR := andR nLLLLL
  have nLLLLRR := andR nLLLLR
  have nLLLRLL := andL nLLLRL
  have nLLLRLR := andR nLLLRL
  have nLLLRRL := andL nLLLRR
  have nLLLRRR := andR nLLLRR
  have nLLRLLL := andL nLLRLL
  have nLLRLLR := andR nLLRLL
  have nLLRLRL := andL nLLRLR
  have nLLRLRR := andR nLLRLR
  have nLLRRLL := andL nLLRRL
  have nLLRRLR := andR nLLRRL
  have nLLRRRL := andL nLLRRR
  have nLRLLLR := andR nLRLLL
  have nLRLLRL := andL nLRLLR
  have nLRLLRR := andR nLRLLR
  have nLRLRLL := andL nLRLRL
  have nLRLRLR := andR nLRLRL
  have nLRLRRL := andL nLRLRR
  have nLRLRRR := andR nLRLRR
  have nLRRLLL := andL nLRRLL
  have nLRRLLR := andR nLRRLL
  have nLRRLRL := andL nLRRLR
  have nLRRLRR := andR nLRRLR
  have nLRRRLL := andL nLRRRL
  have nLRRRRL := andL nLRRRR
  have nLRRRRR := andR nLRRRR
  have nRRRRRL := andL nRRRRR
  have nRRRRRR := andR nRRRRR
  have nLLLLLRL := andL nLLLLLR
  have nLLLLRRL := andL nLLLLRR
  have nLLLLRRR := andR nLLLLRR
  have nLLLRLLL := andL nLLLRLL
  have nLLLRLLR := andR nLLLRLL
  have nLLLRLRL := andL nLLLRLR
  have nLLLRLRR := andR nLLLRLR
  have nLLLRRLL := andL nLLLRRL
  have nLLLRRLR := andR nLLLRRL
  have nLLLRRRL := andL nLLLRRR
  have nLLLRRRR := andR nLLLRRR
  have nLLRLLLL := andL nLLRLLL
  have nLLRLLLR := andR nLLRLLL
  have nLLRLLRL := andL nLLRLLR
  have nLLRLLRR := andR nLLRLLR
  have nLLRLRLL := andL nLLRLRL
  have nLLRLRRL := andL nLLRLRR
  have nLLRRLLL := andL nLLRRLL
  have nLLRRLRR := andR nLLRRLR
  have nLLRRRLL := andL nLLRRRL
  have nLLRRRLR := andR nLLRRRL
  have nLRLLLRL := andL nLRLLLR
  have nLRLLRLL := andL nLRLLRL
  have nLRLLRLR := andR nLRLLRL
  have nLRLLRRL := andL nLRLLRR
  have nLRLLRRR := andR nLRLLRR
  have nLRLRLLL := andL nLRLRLL
  have nLRLRLLR := andR nLRLRLL
  have nLRLRLRL := andL nLRLRLR
  have nLRLRLRR := andR nLRLRLR
  have nLRLRRLL := andL nLRLRRL
  have nLRLRRLR := andR nLRLRRL
  have nLRLRRRL := andL nLRLRRR
  have nLRLRRRR := andR nLRLRRR
  have nLRRLLLL := andL nLRRLLL
  have nLRRLLLR := andR nLRRLLL
  have nLRRLLRL := andL nLRRLLR
  have nLRRLLRR := andR nLRRLLR
  have nLRRLRLL := andL nLRRLRL
  have nLRRLRLR := andR nLRRLRL
  have nLRRLRRL := andL nLRRLRR
  have nLRRLRRR := andR nLRRLRR
  have nLRRRLLL := andL nLRRRLL
  have nLRRRLLR := andR nLRRRLL
  have nLRRRRLL := andL nLRRRRL
  have nLRRRRLR := andR nLRRRRL
  have nLRRRRRL := andL nLRRRRR
  have nLRRRRRR := andR nLRRRRR
  have nRRRRRRL := andL nRRRRRR
  have nRRRRRRR := andR nRRRRRR
  have nLLLLLRLL := andL nLLLLLRL
  have nLLLLLRLR := andR nLLLLLRL
  have nLLLLRRLL := andL nLLLLRRL
  have nLLLLRRLR := andR nLLLLRRL
  have nLLLLRRRL := andL nLLLLRRR
  have nLLLLRRRR := andR nLLLLRRR
  have nLLLRLLLL := andL nLLLRLLL
  have nLLLRLLLR := andR nLLLRLLL
  have nLLLRLLRL := andL nLLLRLLR
  have nLLLRLLRR := andR nLLLRLLR
  have nLLLRLRLL := andL nLLLRLRL
  have nLLLRLRLR := andR nLLLRLRL
  have nLLLRLRRL := andL nLLLRLRR
  have nLLLRLRRR := andR nLLLRLRR
  have nLLLRRLLL := andL nLLLRRLL
  have nLLLRRLLR := andR nLLLRRLL
  have nLLLRRLRL := andL nLLLRRLR
  have nLLLRRLRR := andR nLLLRRLR
  have nLLLRRRLL := andL nLLLRRRL
  have nLLLRRRLR := andR nLLLRRRL
  have nLLLRRRRL := andL nLLLRRRR
  have nLLLRRRRR := andR nLLLRRRR
  have nLLRLLLRL := andL nLLRLLLR
  have nLLRLLLRR := andR nLLRLLLR
  have nLLRLLRLL := andL nLLRLLRL
  have nLLRLLRLR := andR nLLRLLRL
  have nLLRLLRRL := andL nLLRLLRR
  have nLLRLLRRR := andR nLLRLLRR
  have nLLRLRLLL := andL nLLRLRLL
  have nLLRLRLLR := andR nLLRLRLL
  have nLLRLRRLL := andL nLLRLRRL
  have nLLRLRRLR := andR nLLRLRRL
  have nLLRRLLLL := andL nLLRRLLL
  have nLLRRLLLR := andR nLLRRLLL
  have nLLRRLRRR := andR nLLRRLRR
  have nLLRRRLLL := andL nLLRRRLL
  have nLLRRRLLR := andR nLLRRRLL
  have nLLRRRLRL := andL nLLRRRLR
  have nLRLLLRLL := andL nLRLLLRL
  have nLRLLRLLR := andR nLRLLRLL
  have nLRLLRLRR := andR nLRLLRLR
  have nLRLLRRLL := andL nLRLLRRL
  have nLRLLRRLR := andR nLRLLRRL
  have nLRLLRRRL := andL nLRLLRRR
  have nLRLLRRRR := andR nLRLLRRR
  have nLRLRLLLL := andL nLRLRLLL
  have nLRLRLLLR := andR nLRLRLLL
  have nLRLRLLRL := andL nLRLRLLR
  have nLRLRLLRR := andR nLRLRLLR
  have nLRLRLRLL := andL nLRLRLRL
  have nLRLRLRLR := andR nLRLRLRL
  have nLRLRLRRL := andL nLRLRLRR
  have nLRLRLRRR := andR nLRLRLRR
  have nLRLRRLLL := andL nLRLRRLL
  have nLRLRRLLR := andR nLRLRRLL
  have nLRLRRLRL := andL nLRLRRLR
  have nLRLRRLRR := andR nLRLRRLR
  have nLRLRRRLL := andL nLRLRRRL
  have nLRLRRRLR := andR nLRLRRRL
  have nLRLRRRRL := andL nLRLRRRR
  have nLRLRRRRR := andR nLRLRRRR
  have nLRRLLLRL := andL nLRRLLLR
  have nLRRLLLRR := andR nLRRLLLR
  have nLRRLLRLL := andL nLRRLLRL
  have nLRRLLRLR := andR nLRRLLRL
  have nLRRLLRRL := andL nLRRLLRR
  have nLRRLLRRR := andR nLRRLLRR
  have nLRRLRLLL := andL nLRRLRLL
  have nLRRLRLLR := andR nLRRLRLL
  have nLRRLRLRL := andL nLRRLRLR
  have nLRRLRLRR := andR nLRRLRLR
  have nLRRLRRLL := andL nLRRLRRL
  have nLRRLRRLR := andR nLRRLRRL
  have nLRRLRRRL := andL nLRRLRRR
  have nLRRLRRRR := andR nLRRLRRR
  have nLRRRLLLL := andL nLRRRLLL
  have nLRRRLLLR := andR nLRRRLLL
  have nLRRRLLRL := andL nLRRRLLR
  have nLRRRRLLR := andR nLRRRRLL
  have nLRRRRLRL := andL nLRRRRLR
  have nLRRRRLRR := andR nLRRRRLR
  have nLRRRRRLL := andL nLRRRRRL
  have nLRRRRRRL := andL nLRRRRRR
  have nLRRRRRRR := andR nLRRRRRR
  have nRRRRRRRL := andL nRRRRRRR
  have nRRRRRRRR := andR nRRRRRRR
  have nRRRRRRRRL := andL nRRRRRRRR
  have nRRRRRRRRR := andR nRRRRRRRR
  have nRRRRRRRRRL := andL nRRRRRRRRR
  have nRRRRRRRRRR := andR nRRRRRRRRR
  have nRRRRRRRRRRL := andL nRRRRRRRRRR
  have nRRRRRRRRRRR := andR nRRRRRRRRRR
  have nRRRRRRRRRRRR := andR nRRRRRRRRRRR
  have nRRRRRRRRRRRRR := andR nRRRRRRRRRRRR
  have nRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRRRRRL := andL nRRRRRRRRRRRRRRRRRRRRRRRR
  have nRRRRRRRRRRRRRRRRRRRRRRRRR := andR nRRRRRRRRRRRRRRRRRRRRRRRR
  exact
    { a_gom := Nat.eq_of_beq_eq_true nLLLLLRLL
      a_hdr := Nat.eq_of_beq_eq_true nLLLLLRLR
      a_psi := Nat.eq_of_beq_eq_true nLLLLRRLL
      a_facts := Nat.eq_of_beq_eq_true nLLLLRRLR
      b_cover := Nat.eq_of_beq_eq_true nLLLLRRRL
      b_sorted10 := Nat.eq_of_beq_eq_true nLLLLRRRR
      b_sorted1 := Nat.eq_of_beq_eq_true nLLLRLLLL
      b_sorted2 := Nat.eq_of_beq_eq_true nLLLRLLLR
      b_sorted3 := Nat.eq_of_beq_eq_true nLLLRLLRL
      b_sorted4 := Nat.eq_of_beq_eq_true nLLLRLLRR
      b_sorted5 := Nat.eq_of_beq_eq_true nLLLRLRLL
      b_sorted6 := Nat.eq_of_beq_eq_true nLLLRLRLR
      b_sorted7 := Nat.eq_of_beq_eq_true nLLLRLRRL
      b_sorted8 := Nat.eq_of_beq_eq_true nLLLRLRRR
      b_sorted9 := Nat.eq_of_beq_eq_true nLLLRRLLL
      b_gom := Nat.eq_of_beq_eq_true nLLLRRLLR
      b_hdr := Nat.eq_of_beq_eq_true nLLLRRLRL
      b_pts := Nat.eq_of_beq_eq_true nLLLRRLRR
      b_stab10 := Nat.eq_of_beq_eq_true nLLLRRRLL
      b_stab1 := Nat.eq_of_beq_eq_true nLLLRRRLR
      b_stab2 := Nat.eq_of_beq_eq_true nLLLRRRRL
      b_stab3 := Nat.eq_of_beq_eq_true nLLLRRRRR
      b_stab4 := Nat.eq_of_beq_eq_true nLLRLLLL
      b_stab5 := Nat.eq_of_beq_eq_true nLLRLLLRL
      b_stab6 := Nat.eq_of_beq_eq_true nLLRLLLRR
      b_stab7 := Nat.eq_of_beq_eq_true nLLRLLRLL
      b_stab8 := Nat.eq_of_beq_eq_true nLLRLLRLR
      b_stab9 := Nat.eq_of_beq_eq_true nLLRLLRRL
      b_tsig := Nat.eq_of_beq_eq_true nLLRLLRRR
      b_psi := Nat.eq_of_beq_eq_true nLLRLRLLL
      b_facts1 := Nat.eq_of_beq_eq_true nLLRLRLLR
      k1_cover := Nat.eq_of_beq_eq_true nLLRLRRLL
      k1_facts := Nat.eq_of_beq_eq_true nLLRLRRLR
      k3_cover := Nat.eq_of_beq_eq_true nLLRRLLLL
      k3_facts := Nat.eq_of_beq_eq_true nLLRRLLLR
      a_letters := nLLRRLRRR
      a_rels := nLLRRRLLL
      a_words := nLLRRRLLR
      a_usq := nLLRRRLRL
      a_sub := nLRLLLRLL
      b_cnt10 := Nat.eq_of_beq_eq_true nLRLLRLLR
      b_cnt2 := Nat.eq_of_beq_eq_true nLRLLRLRR
      b_cnt3 := Nat.eq_of_beq_eq_true nLRLLRRLL
      b_cnt4 := Nat.eq_of_beq_eq_true nLRLLRRLR
      b_cnt5 := Nat.eq_of_beq_eq_true nLRLLRRRL
      b_cnt6 := Nat.eq_of_beq_eq_true nLRLLRRRR
      b_cnt7 := Nat.eq_of_beq_eq_true nLRLRLLLL
      b_cnt8 := Nat.eq_of_beq_eq_true nLRLRLLLR
      b_cnt9 := Nat.eq_of_beq_eq_true nLRLRLLRL
      b_cntpts := Nat.eq_of_beq_eq_true nLRLRLLRR
      b_cnttsig := Nat.eq_of_beq_eq_true nLRLRLRLL
      b_letters := nLRLRLRLR
      b_rels := nLRLRLRRL
      b_words := nLRLRLRRR
      b_usq := nLRLRRLLL
      b_sel := nLRLRRLLR
      b_om := Nat.eq_of_beq_eq_true nLRLRRLRL
      b_owd := Nat.eq_of_beq_eq_true nLRLRRLRR
      b_i0 := Nat.blt_eq.mp nLRLRRRLL
      b_nord := Nat.eq_of_beq_eq_true nLRLRRRLR
      b_sum := nLRLRRRRL
      b_start1 := nLRLRRRRR
      b_start2 := nLRRLLLL
      b_start3 := nLRRLLLRL
      b_start4 := nLRRLLLRR
      b_start5 := nLRRLLRLL
      b_start6 := nLRRLLRLR
      b_start7 := nLRRLLRRL
      b_start8 := nLRRLLRRR
      b_start9 := nLRRLRLLL
      b_start10 := nLRRLRLLR
      b_nl := Nat.eq_of_beq_eq_true nLRRLRLRL
      b_lc := Nat.eq_of_beq_eq_true nLRRLRLRR
      b_nr := Nat.eq_of_beq_eq_true nLRRLRRLL
      b_rh := Nat.eq_of_beq_eq_true nLRRLRRLR
      b_order := Nat.eq_of_beq_eq_true nLRRLRRRL
      k1_words := nLRRLRRRR
      k1_inv := nLRRRLLLL
      k1_alive := nLRRRLLLR
      k1_nc := Nat.eq_of_beq_eq_true nLRRRLLRL
      k3_words := nLRRRRLLR
      k3_inv := nLRRRRLRL
      k3_alive := nLRRRRLRR
      k3_nc := Nat.eq_of_beq_eq_true nLRRRRRLL
      a_norm := nLRRRRRRL
      b_norm := nLRRRRRRR
      a_nd := Nat.blt_eq.mp nRL
      b_nd := Nat.blt_eq.mp nRRL
      a_nf := Nat.blt_eq.mp nRRRL
      b_nf := Nat.blt_eq.mp nRRRRL
      a_nr := Nat.le_of_ble_eq_true nRRRRRL
      b_sf39 := Nat.eq_of_beq_eq_true nRRRRRRL
      b_cnt1 := Nat.eq_of_beq_eq_true nRRRRRRRL
      a_term := nRRRRRRRRL
      k1_sf42 := Nat.eq_of_beq_eq_true nRRRRRRRRRL
      k1_sf43 := Nat.eq_of_beq_eq_true nRRRRRRRRRRL
      k3_sf46 := Nat.eq_of_beq_eq_true nRRRRRRRRRRRRRL
      k3_sf47 := Nat.eq_of_beq_eq_true nRRRRRRRRRRRRRRL
      k1_hints := nRRRRRRRRRRRRRRRL
      k1_per := nRRRRRRRRRRRRRRRRL
      k1_rt := nRRRRRRRRRRRRRRRRRL
      k3_hints := nRRRRRRRRRRRRRRRRRRL
      k3_per := nRRRRRRRRRRRRRRRRRRRL
      k3_rt := nRRRRRRRRRRRRRRRRRRRRL
      k3_st0 := Nat.eq_of_beq_eq_true nRRRRRRRRRRRRRRRRRRRRRL
      k3_st1 := Nat.eq_of_beq_eq_true nRRRRRRRRRRRRRRRRRRRRRRL
      k3_st2 := Nat.eq_of_beq_eq_true nRRRRRRRRRRRRRRRRRRRRRRRL
      k3_st3 := Nat.eq_of_beq_eq_true nRRRRRRRRRRRRRRRRRRRRRRRRL
      k3_st4 := Nat.eq_of_beq_eq_true nRRRRRRRRRRRRRRRRRRRRRRRRR
    }

end CFSG.KC.Th.Spec.Dce

end
