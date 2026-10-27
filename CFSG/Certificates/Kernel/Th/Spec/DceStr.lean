module

public import CFSG.Certificates.Kernel.Th.Gen.Dce
public import CFSG.Certificates.Kernel.Th.Gen.DceStruct

public section

namespace CFSG.KC.Th.Spec.DceStr

open CFSG.KC.Th CFSG.KC.Th.Gen

@[expose] def toDce (D : DceStructData) : DceData where
  ThA_AL := D.ThA_AL
  ThA_CB := D.ThA_CB
  ThA_E1 := D.ThA_E1
  ThA_E2 := D.ThA_E2
  ThA_FB := D.ThA_FB
  ThA_GB := D.ThA_GB
  ThA_HB := D.ThA_HB
  ThA_I0 := D.ThA_I0
  ThA_LC := D.ThA_LC
  ThA_LI := D.ThA_LI
  ThA_LT := D.ThA_LT
  ThA_MD := D.ThA_MD
  ThA_NB := D.ThA_NB
  ThA_NCL := D.ThA_NCL
  ThA_ND := D.ThA_ND
  ThA_NF := D.ThA_NF
  ThA_NL := D.ThA_NL
  ThA_NO := D.ThA_NO
  ThA_NORD := D.ThA_NORD
  ThA_NR := D.ThA_NR
  ThA_OB := D.ThA_OB
  ThA_RH := D.ThA_RH
  ThA_RR := D.ThA_RR
  ThA_SG1 := D.ThA_SG1
  ThA_SG2 := D.ThA_SG2
  ThA_SUM := D.ThA_SUM
  ThA_TB := D.ThA_TB
  ThA_TL := D.ThA_TL
  ThA_UH := D.ThA_UH
  ThA_USQ := D.ThA_USQ
  ThA_VL := D.ThA_VL
  ThA_W := D.ThA_W
  ThA_WD := D.ThA_WD
  ThA_WH := D.ThA_WH
  ThA_Wi := D.ThA_Wi
  ThA_nH := D.ThA_nH
  ThA_nT := D.ThA_nT
  ThA_nW := D.ThA_nW
  ThA_om := D.ThA_om
  ThA_osh := D.ThA_osh
  ThA_owd := D.ThA_owd
  ThA_sel := D.ThA_sel
  ThB_AL := D.ThB_AL
  ThB_E1 := D.ThB_E1
  ThB_E10 := D.ThB_E10
  ThB_E2 := D.ThB_E2
  ThB_E3 := D.ThB_E3
  ThB_E4 := D.ThB_E4
  ThB_E5 := D.ThB_E5
  ThB_E6 := D.ThB_E6
  ThB_E7 := D.ThB_E7
  ThB_E8 := D.ThB_E8
  ThB_E9 := D.ThB_E9
  ThB_FB := D.ThB_FB
  ThB_GB := D.ThB_GB
  ThB_HB := D.ThB_HB
  ThB_I0 := D.ThB_I0
  ThB_LC := D.ThB_LC
  ThB_LI := D.ThB_LI
  ThB_LT := D.ThB_LT
  ThB_MD := D.ThB_MD
  ThB_NB := D.ThB_NB
  ThB_ND := D.ThB_ND
  ThB_NF := D.ThB_NF
  ThB_NL := D.ThB_NL
  ThB_NO := D.ThB_NO
  ThB_NR := D.ThB_NR
  ThB_OB := D.ThB_OB
  ThB_RH := D.ThB_RH
  ThB_RR := D.ThB_RR
  ThB_SG1 := D.ThB_SG1
  ThB_SG10 := D.ThB_SG10
  ThB_SG2 := D.ThB_SG2
  ThB_SG3 := D.ThB_SG3
  ThB_SG4 := D.ThB_SG4
  ThB_SG5 := D.ThB_SG5
  ThB_SG6 := D.ThB_SG6
  ThB_SG7 := D.ThB_SG7
  ThB_SG8 := D.ThB_SG8
  ThB_SG9 := D.ThB_SG9
  ThB_SUM := D.ThB_SUM
  ThB_TB := D.ThB_TB
  ThB_TL := D.ThB_TL
  ThB_UH := D.ThB_UH
  ThB_USQ := D.ThB_USQ
  ThB_VL := D.ThB_VL
  ThB_W := D.ThB_W
  ThB_WD := D.ThB_WD
  ThB_WH := D.ThB_WH
  ThB_Wi := D.ThB_Wi
  ThB_nH := D.ThB_nH
  ThB_nT := D.ThB_nT
  ThB_nW := D.ThB_nW
  ThB_om := D.ThB_om
  ThB_osh := D.ThB_osh
  ThB_owd := D.ThB_owd
  ThB_sel := D.ThB_sel
  ThK1_HS := D.ThK1_HS
  ThK1_INV := D.ThK1_INV
  ThK1_INV8 := D.ThK1_INV8
  ThK1_LVs := D.ThK1_LVs
  ThK1_blk := D.ThK1_blk
  ThK1_litRT := D.ThK1_litRT
  ThK1_nC := D.ThK1_nC
  ThK1_nLive := D.ThK1_nLive
  ThK1_selRT := D.ThK1_selRT
  ThK1_selST := D.ThK1_selST
  ThK1_selWT := D.ThK1_selWT
  ThK2_HS := D.ThK2_HS
  ThK2_INV := D.ThK2_INV
  ThK2_INV8 := D.ThK2_INV8
  ThK2_LVs := D.ThK2_LVs
  ThK2_blk := D.ThK2_blk
  ThK2_litRT := D.ThK2_litRT
  ThK2_nC := D.ThK2_nC
  ThK2_nLive := D.ThK2_nLive
  ThK2_selRT := D.ThK2_selRT
  ThK2_selST := D.ThK2_selST
  ThK2_selWT := D.ThK2_selWT
  ThK3_HS := D.ThK3_HS
  ThK3_INV := D.ThK3_INV
  ThK3_INV8 := D.ThK3_INV8
  ThK3_LVs := D.ThK3_LVs
  ThK3_blk := D.ThK3_blk
  ThK3_litRT := D.ThK3_litRT
  ThK3_nC := D.ThK3_nC
  ThK3_nLive := D.ThK3_nLive
  ThK3_selRT := D.ThK3_selRT
  ThK3_selST := D.ThK3_selST
  ThK3_selWT := D.ThK3_selWT
  cs0 := D.cs0
  cs1 := D.cs1
  sf1 := D.sf1
  cs2 := D.cs2
  sf2 := D.sf2
  cs3 := D.cs3
  cs4 := D.cs4
  cs5 := D.cs5
  sf5 := D.sf5
  cs6 := D.cs6
  cs7 := D.cs7
  sf7 := D.sf7
  cs8 := D.cs8
  cs9 := D.cs9
  cs10 := D.cs10
  sf10 := D.sf10
  cs11 := D.cs11
  cs12 := D.cs12
  cs13 := D.cs13
  cs14 := D.cs14
  sf14 := D.sf14
  cs15 := D.cs15
  sf15 := D.sf15
  cs16 := D.cs16
  sf16 := D.sf16
  cs17 := D.cs17
  sf17 := D.sf17
  cs18 := D.cs18
  sf18 := D.sf18
  cs19 := D.cs19
  sf19 := D.sf19
  cs20 := D.cs20
  sf20 := D.sf20
  cs21 := D.cs21
  sf21 := D.sf21
  cs22 := D.cs22
  sf22 := D.sf22
  cs23 := D.cs23
  sf23 := D.sf23
  cs24 := D.cs24
  cs25 := D.cs25
  cs26 := D.cs26
  sf26 := D.sf26
  cs27 := D.cs27
  cs28 := D.cs28
  cs29 := D.cs29
  cs30 := D.cs30
  cs31 := D.cs31
  cs32 := D.cs32
  cs33 := D.cs33
  cs34 := D.cs34
  cs35 := D.cs35
  cs36 := D.cs36
  cs37 := D.cs37
  sf37 := D.sf37
  cs38 := D.cs38
  cs39 := D.cs39
  sf39 := D.sf39
  cs40 := D.cs40
  cs41 := D.cs41
  sf41 := D.sf41
  cs42 := D.cs42
  sf42 := D.sf42
  cs43 := D.cs43
  sf43 := D.sf43
  cs44 := D.cs44
  sf44 := D.sf44
  cs45 := D.cs45
  sf45 := D.sf45
  cs46 := D.cs46
  sf46 := D.sf46
  cs47 := D.cs47
  sf47 := D.sf47

private theorem andI {a b : Bool} (ha : a = true) (hb : b = true) : CFSG.KC.Th.andB a b = true := by
  rw [ha, hb]
  rfl

theorem dceChk_toDce (D : DceStructData) (h : dceStructChkGen D = true) : dceChk (toDce D) = true := by
  unfold dceStructChkGen at h
  unfold dceChk
  exact
    andI
    (andI
      (andI
        (andI
          (andI
            (andI
              (andI
                (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left h))))))))
                (andI
                  (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left h))))))))))
              (andI
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left h))))))))))
                (andI
                  (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left h))))))))
                  (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left h)))))))))))
            (andI
              (andI
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left h))))))))))
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left h))))))))))
              (andI
                (andI
                  (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left h)))))))))))))
          (andI
            (andI
              (andI
                (andI
                  (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left h))))))))
                  (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left h)))))))))))
              (andI
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left h)))))))))
                (andI
                  (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left h)))))))))))
            (andI
              (andI
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left h))))))))))
                (andI
                  (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left h))))))))
                  (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left h))))))))))
              (andI
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left h))))))))))
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left h)))))))))))))
        (andI
          (andI
            (andI
              (andI
                (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left h))))))))
                (andI
                  (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left h)))))))))))
              (andI
                (andI
                  (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left h)))))))))
                  (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left h))))))))))))
            (andI
              (andI
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left h))))))))))
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left h))))))))))
              (andI
                (andI
                  (andB_right (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left h)))))))))))))
          (andI
            (andI
              (andI
                (andI
                  (andB_left (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left h))))))))
                  (andB_right (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left h))))))))))
              (andI
                (andI
                  (andB_right (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left h))))))))))))
            (andI
              (andI
                (andI
                  (andB_left (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left h))))))))
                  (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left h)))))))))))
              (andI
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_right (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left h))))))))))))))
      (andI
        (andI
          (andI
            (andI
              (andI
                (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left h))))))))))
              (andI
                (andI
                  (andB_right (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left h))))))))))))
            (andI
              (andI
                (andI
                  (andB_left (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left h))))))))
                  (andB_right (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left h)))))))))))
              (andI
                (andI
                  (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left h)))))))))
                  (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left h)))))))))))))
          (andI
            (andI
              (andI
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left h))))))))))
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left h))))))))))
              (andI
                (andI
                  (andB_right (andB_left (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left h))))))))
                  (andB_left (andB_right (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left h))))))))))))
            (andI
              (andI
                (andI
                  (andB_left (andB_left (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left h))))))))
                  (andB_right (andB_left (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left h)))))))))))
              (andI
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left h)))))))))
                (andI
                  (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left h))))))))
                  (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left h)))))))))))))
        (andI
          (andI
            (andI
              (andI
                (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left h)))))))))
                (andI
                  (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left h)))))))))
                  (andB_left (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left h))))))))))
              (andI
                (andI
                  (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left h))))))))))))
            (andI
              (andI
                (andI
                  (andB_left (andB_left (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left h))))))))
                  (andB_right (andB_left (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left h)))))))))))
              (andI
                (andI
                  (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left h)))))))))
                  (andB_left (andB_left (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left h)))))))))
                (andI
                  (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left h))))))))))))
          (andI
            (andI
              (andI
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left h))))))))))
                (andI
                  (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left h))))))))
                  (andB_right (andB_left (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left h))))))))))
              (andI
                (andI
                  (andB_left (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left h))))))))))
                (andI
                  (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right (andB_left h)))))))))
                  (andB_left (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left h)))))))))))
            (andI
              (andI
                (andI
                  (andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left h)))))))))
                  (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left h))))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left h))))))))
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left h)))))))))))
              (andI
                (andI
                  (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left h)))))))))
                  (andB_left (andB_left (andB_left (andB_left (andB_left (andB_right (andB_right (andB_left h)))))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left h)))))))))
                  (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left h))))))))))))))))
    (andI
      (andB_left (andB_right h))
      (andI
        (andB_left (andB_right (andB_right h)))
        (andI
          (andB_left (andB_right (andB_right (andB_right h))))
          (andI
            (andB_left (andB_right (andB_right (andB_right (andB_right h)))))
            (andI
              (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right h))))))
              (andI
                (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))
                (andI
                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))
                  (andI
                    (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))
                    (andI
                      (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))))
                      (andI
                        (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))
                        (andI
                          (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))))))
                          (andI
                            (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))))
                            (andI
                              (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))))))))
                              (andI
                                (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))))))
                                (andI
                                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))))))))))
                                  (andI
                                    (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))))))))
                                    (andI
                                      (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))))))))))))
                                      (andI
                                        (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))))))))))
                                        (andI
                                          (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))))))))))))))
                                          (andI
                                            (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))))))))))))
                                            (andI
                                              (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))))))))))))))))
                                              (andI
                                                (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))))))))))))))
                                                (andI
                                                  (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))))))))))))))))))))
                                                  (andI
                                                    (andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))))))))))))))))
                                                    (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h)))))))))))))))))))))))))))))))))))))))))))))))))

end CFSG.KC.Th.Spec.DceStr

end
