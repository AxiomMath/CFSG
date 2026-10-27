module

public import CFSG.Certificates.Kernel.Th.Gen.Ts

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.Gen

theorem tsAndB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true :=
  ⟨fun h => ⟨andB_left h, andB_right h⟩, fun h => by rw [h.1]; exact h.2⟩

theorem eq_of_eqN' {a b : ℕ} (h : eqN a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ne_of_neN' {a b : ℕ} (h : neN a b = true) : a ≠ b := by
  intro e
  subst e
  unfold neN BigS.notB at h
  rw [show Nat.beq a a = true from Nat.beq_refl a] at h
  exact Bool.noConfusion h

structure TsLeaves (D : TsData) : Prop where
  c0 :
    (CFSG.KC.Th.DceS.runSorted D.ThTs_ROWS 12 2457 D.cs0 1) = D.sf0
  c1 :
    (CFSG.KC.Th.TsS.runItems
      (CFSG.KC.Th.TsS.permOK D.ThTs_ROWS D.ThTs_PX D.ThTs_PY D.ThS_rm (D.ThTs_RB 1) (D.ThTs_RB 3)
        2457) D.cs1 1)
    = D.sf1
  c2 :
    (CFSG.KC.Th.TsS.runItems (CFSG.KC.Th.TsS.invOK D.ThTs_TP D.ThTs_INV 2457) D.cs2 1) = D.sf2
  c3 :
    (CFSG.KC.Th.TsS.runItems
      (CFSG.KC.Th.TsS.treeOK D.ThTs_TP D.ThTs_TPA D.ThTs_TLA D.ThTs_PX D.ThTs_PY 2457) D.cs3 1)
    = D.sf3
  c4 :
    (CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
      D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE) = true
  c5 :
    (CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA) = true
  c6 :
    (CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB) = true
  m3_0 :
    (D.ThM3_RB 0) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SB)
  m3_1 :
    (D.ThM3_RB 1) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 0) D.ThSeed_SB)
  m3_2 :
    (D.ThM3_RB 2) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 0) (D.ThM3_RB 1))
  m3_3 :
    (D.ThM3_RB 3) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 0) (D.ThM3_RB 2))
  m3_4 :
    (D.ThM3_RB 4) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA (D.ThM3_RB 3))
  m3_5 :
    (D.ThM3_RB 5) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 3) D.ThSeed_SA)
  m3_6 :
    (D.ThM3_RB 6)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 5) 2 2) (D.ThM3_RB 4))
  m3_7 :
    (D.ThM3_RB 7) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 3) (D.ThM3_RB 2))
  m3_8 :
    (D.ThM3_RB 8) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 0) (D.ThM3_RB 7))
  m3_9 :
    (D.ThM3_RB 9) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 8) (D.ThM3_RB 1))
  m3_10 :
    (D.ThM3_RB 10) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA (D.ThM3_RB 9))
  m3_11 :
    (D.ThM3_RB 11) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 9) D.ThSeed_SA)
  m3_12 :
    (D.ThM3_RB 12)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 11) 18 5) (D.ThM3_RB 10))
  m3_13 :
    (D.ThM3_RB 13) = (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 12) 14 4)
  m3_14 :
    (D.ThM3_RB 14)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 4)
        (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 6) 9 4))
  m3_15 :
    (D.ThM3_RB 15) = (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 14) 5 3)
  m3_16 :
    (D.ThM3_RB 16)
    = (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE
        (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14)
          (D.ThM3_RB 15) 84 4) 9 4)
  ts_0 :
    (D.ThTs_RB 0) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB)
  ts_1 :
    (D.ThTs_RB 1)
    = (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE D.ThSeed_SA D.ThSeed_SB (D.ThTs_RB 0)
        19676527007948218914 33)
  ts_2 :
    (D.ThTs_RB 2)
    = (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE D.ThSeed_SA D.ThSeed_SB (D.ThTs_RB 0)
        546472502307675765001542338109559680589977148440078108285031978964036 115)
  ts_3 :
    (D.ThTs_RB 3) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 2) (D.ThTs_RB 2))
  ts_4 :
    (D.ThTs_RB 4)
    = (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThTs_RB 1) (D.ThTs_RB 2) (D.ThTs_RB 3)
        71641224 15)
  ts_5 :
    (D.ThTs_RB 5)
    = (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThTs_RB 1) (D.ThTs_RB 2) (D.ThTs_RB 3)
        74159786122 20)
  ts_6 :
    (D.ThTs_RB 6)
    = (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThTs_RB 1) (D.ThTs_RB 2) (D.ThTs_RB 3)
        69 4)
  ts_7 :
    (D.ThTs_RB 7)
    = (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThTs_RB 1) (D.ThTs_RB 2) (D.ThTs_RB 3)
        162 4)
  ts_8 :
    (D.ThTs_RB 8)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 6) (D.ThTs_RB 4)) (D.ThTs_RB 7))
  ts_9 :
    (D.ThTs_RB 9)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 6) (D.ThTs_RB 5)) (D.ThTs_RB 7))
  ts_11 :
    (D.ThTs_RB 11)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 4) (D.ThTs_RB 10)) (D.ThTs_RB 8))
          (D.ThTs_RB 9)) (D.ThTs_RB 4))
  ts_13 :
    (D.ThTs_RB 13)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 12) (D.ThTs_RB 12)) (D.ThTs_RB 4))
          (D.ThTs_RB 5)) (D.ThTs_RB 5))
  ts_14 :
    (D.ThTs_RB 14)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
              (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                  (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 13) (D.ThTs_RB 11))
                            (D.ThTs_RB 13)) (D.ThTs_RB 11)) (D.ThTs_RB 13)) (D.ThTs_RB 11))
                    (D.ThTs_RB 13)) (D.ThTs_RB 11)) (D.ThTs_RB 13)) (D.ThTs_RB 11)) (D.ThTs_RB 13))
          (D.ThTs_RB 11)) (D.ThTs_RB 13))
  ts_15 :
    (D.ThTs_RB 15)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
              (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 12) (D.ThTs_RB 12)) (D.ThTs_RB 8))
            (D.ThTs_RB 4)) (D.ThTs_RB 9)) (D.ThTs_RB 5))
  ts_16 :
    (D.ThTs_RB 16) = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 15) (D.ThTs_RB 15))
  ts_18 :
    (D.ThTs_RB 18)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
              (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                  (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 14) (D.ThTs_RB 17)) (D.ThTs_RB 17))
                  (D.ThTs_RB 14)) (D.ThTs_RB 16)) (D.ThTs_RB 16)) (D.ThTs_RB 14)) (D.ThTs_RB 16))
        (D.ThTs_RB 14))
  c587 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 4) (D.ThTs_RB 19)) = D.ThS_ONE
  c588 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 5) (D.ThTs_RB 12)) = D.ThS_ONE
  c589 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 8) (D.ThTs_RB 20)) = D.ThS_ONE
  c590 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 9) (D.ThTs_RB 10)) = D.ThS_ONE
  c591 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 11) (D.ThTs_RB 21)) = D.ThS_ONE
  c592 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 13) (D.ThTs_RB 22)) = D.ThS_ONE
  c593 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 14) (D.ThTs_RB 23)) = D.ThS_ONE
  c594 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 15) (D.ThTs_RB 24)) = D.ThS_ONE
  c595 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 16) (D.ThTs_RB 17)) = D.ThS_ONE
  c596 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 18) (D.ThTs_RB 25)) = D.ThS_ONE
  ts_26 :
    (D.ThTs_RB 26)
    = (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE D.ThSeed_SA D.ThSeed_SB (D.ThTs_RB 0)
        373911662824283980869 35)
  ts_27 :
    (D.ThTs_RB 27)
    = (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE D.ThSeed_SA D.ThSeed_SB (D.ThTs_RB 0)
        747708476841837865098 35)
  ts_28 :
    (D.ThTs_RB 28)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 27) D.ThSeed_SA) (D.ThTs_RB 26))
  ts_29 :
    (D.ThTs_RB 29)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 26) (D.ThTs_RB 6)) (D.ThTs_RB 27))
  ts_30 :
    (D.ThTs_RB 30)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 26) (D.ThTs_RB 7)) (D.ThTs_RB 27))
  ts_31 :
    (D.ThTs_RB 31)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 29) D.ThSeed_SA) (D.ThTs_RB 30))
  ts_32 :
    (D.ThTs_RB 32)
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
              (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14)
                (D.ThM3_RB 15) 1352160579797152663358438253090 52)
              (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14)
                (D.ThM3_RB 15) 85004562 14))
            (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14)
              (D.ThM3_RB 15) 340018248 16))
          (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14)
            (D.ThM3_RB 15) 18539942178 18))
        (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14)
          (D.ThM3_RB 15) 5655040296 18))
  c604 :
    (CFSG.KC.Th.TsS.natsRun D.ThTs_ROWS 2457 true D.ThTs_Lrows) = true
  c605 :
    (CFSG.KC.Th.TsS.natsRun D.ThTs_PX 2457 false D.ThTs_Lpx) = true
  c606 :
    (CFSG.KC.Th.TsS.natsRun D.ThTs_PY 2457 false D.ThTs_Lpy) = true
  c607 :
    (CFSG.KC.Th.TsS.natsRun D.ThTs_TP 2457 false D.ThTs_Ltp) = true
  c608 :
    (CFSG.KC.Th.TsS.natsRun D.ThTs_TPA 2457 false D.ThTs_Ltpa) = true
  c609 :
    (CFSG.KC.Th.TsS.natsRun D.ThTs_TLA 2457 false D.ThTs_Ltla) = true
  c610 :
    (CFSG.KC.Th.DceS.sortedCount D.sf0) = 2457
  c611 :
    (D.ThTs_ROWS 0) = 188699030134974771940902637381138826052768254673852968596118984082230640546
  c612 :
    (D.ThTs_TP 0) = 0
  c613 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 1) (D.ThTs_RB 1)) = D.ThS_ONE
  c614 :
    (D.ThTs_RB 1) ≠ D.ThS_ONE
  c615 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 2) (D.ThTs_RB 2)) (D.ThTs_RB 2))
    = D.ThS_ONE
  c616 :
    (D.ThTs_RB 2) ≠ D.ThS_ONE
  c617 :
    (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE
      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 1) (D.ThTs_RB 2)) 21 5)
    = D.ThS_ONE
  c618 :
    (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE
      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 1) (D.ThTs_RB 2)) 3 2)
    ≠ D.ThS_ONE
  c619 :
    (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE
      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 1) (D.ThTs_RB 2)) 7 3)
    ≠ D.ThS_ONE
  c620 :
    (CFSG.KC.Th.canon2
      (CFSG.KC.Th.vecB D.ThS_rm
        (Nat.land
          (CFSG.KC.Th.canon2
            327208660843949311569856638931134950366718123578765707520623978699011294545
            53118203310247861616881865655955129280624587562044029180903589568007838922)
          115792089237316195423570985008687907853269984665640564039457584007913129639935)
        (D.ThTs_RB 1))
      (CFSG.KC.Th.vecB D.ThS_rm
        (Nat.shiftRight
          (CFSG.KC.Th.canon2
            327208660843949311569856638931134950366718123578765707520623978699011294545
            53118203310247861616881865655955129280624587562044029180903589568007838922) 256)
        (D.ThTs_RB 1)))
    = (CFSG.KC.Th.canon2
        327208660843949311569856638931134950366718123578765707520623978699011294545
        53118203310247861616881865655955129280624587562044029180903589568007838922)
  c621 :
    (CFSG.KC.Th.canon2
      (CFSG.KC.Th.vecB D.ThS_rm
        (Nat.land
          (CFSG.KC.Th.canon2
            327208660843949311569856638931134950366718123578765707520623978699011294545
            53118203310247861616881865655955129280624587562044029180903589568007838922)
          115792089237316195423570985008687907853269984665640564039457584007913129639935)
        (D.ThTs_RB 3))
      (CFSG.KC.Th.vecB D.ThS_rm
        (Nat.shiftRight
          (CFSG.KC.Th.canon2
            327208660843949311569856638931134950366718123578765707520623978699011294545
            53118203310247861616881865655955129280624587562044029180903589568007838922) 256)
        (D.ThTs_RB 3)))
    = (CFSG.KC.Th.canon2
        327208660843949311569856638931134950366718123578765707520623978699011294545
        53118203310247861616881865655955129280624587562044029180903589568007838922)
  c622 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 4) (D.ThTs_RB 28))
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 28) (D.ThTs_RB 4))
  c623 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 5) (D.ThTs_RB 28))
    = (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 28) (D.ThTs_RB 5))
  c624 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
              (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                  (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                              (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 15) (D.ThTs_RB 18))
                              (D.ThTs_RB 14)) (D.ThTs_RB 4)) (D.ThTs_RB 14)) (D.ThTs_RB 25))
                      (D.ThTs_RB 15)) (D.ThTs_RB 17)) (D.ThTs_RB 14)) (D.ThTs_RB 17))
              (D.ThTs_RB 14)) (D.ThTs_RB 16)) (D.ThTs_RB 14)) (D.ThTs_RB 16)) (D.ThTs_RB 18))
    = (D.ThTs_RB 1)
  c625 :
    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
          (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
            (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
              (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                  (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                    (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                      (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
                        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThTs_RB 16) (D.ThTs_RB 16))
                        (D.ThTs_RB 16)) (D.ThTs_RB 9)) (D.ThTs_RB 11)) (D.ThTs_RB 25))
                (D.ThTs_RB 15)) (D.ThTs_RB 11)) (D.ThTs_RB 17)) (D.ThTs_RB 14)) (D.ThTs_RB 17))
      (D.ThTs_RB 25))
    = (D.ThTs_RB 2)
  c626 :
    (D.ThTs_RB 31) = (D.ThTs_RB 32)
  c627 :
    (D.ThTs_RB 31) ≠ D.ThS_ONE
  c628 :
    (D.ThTs_RB 31) ≠ (D.ThM3_RB 16)
  c629 :
    D.sf1 = 2458
  c630 :
    D.sf2 = 2458
  c631 :
    D.sf3 = 2458

theorem tsChk_leaves {D : TsData} (h : tsChk D = true) : TsLeaves D := by
  simp only [tsChk, tsAndB_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨x0, x1⟩, ⟨x2, x3⟩⟩, ⟨⟨x4, x5⟩, ⟨x6, -⟩⟩⟩, ⟨⟨-, ⟨-, ⟨x12, x13⟩⟩⟩, ⟨⟨x14, x15⟩,
      ⟨x16, ⟨x17, x18⟩⟩⟩⟩⟩, ⟨⟨⟨⟨x19, x20⟩, ⟨x21, ⟨x22, x23⟩⟩⟩, ⟨⟨x24, x25⟩, ⟨x26, ⟨x27, x28⟩⟩⟩⟩,
      -⟩⟩, -⟩, -⟩, -⟩, ⟨-, ⟨-, ⟨⟨-, ⟨⟨⟨-, ⟨x571, ⟨x572, x573⟩⟩⟩, ⟨⟨x574, x575⟩, ⟨x576, ⟨x577,
      x578⟩⟩⟩⟩, ⟨⟨⟨x579, x580⟩, ⟨x581, ⟨x582, x583⟩⟩⟩, ⟨⟨x584, x585⟩, ⟨x586, ⟨x587, x588⟩⟩⟩⟩⟩⟩,
      ⟨⟨⟨⟨⟨x589, x590⟩, ⟨x591, ⟨x592, x593⟩⟩⟩, ⟨⟨x594, x595⟩, ⟨x596, ⟨x597, x598⟩⟩⟩⟩, ⟨⟨⟨x599,
      x600⟩, ⟨x601, ⟨x602, x603⟩⟩⟩, ⟨⟨x604, x605⟩, ⟨x606, ⟨x607, x608⟩⟩⟩⟩⟩, ⟨⟨⟨⟨x609, x610⟩, ⟨x611,
      ⟨x612, x613⟩⟩⟩, ⟨⟨x614, x615⟩, ⟨x616, ⟨x617, x618⟩⟩⟩⟩, ⟨⟨⟨x619, x620⟩, ⟨x621, ⟨x622, x623⟩⟩⟩,
      ⟨⟨x624, x625⟩, ⟨x626, ⟨x627, x628⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩, ⟨x629, ⟨x630, x631⟩⟩⟩ := h
  exact ⟨eq_of_eqN' x0, eq_of_eqN' x1, eq_of_eqN' x2, eq_of_eqN' x3, x4, x5, x6, eq_of_eqN' x12,
      eq_of_eqN' x13, eq_of_eqN' x14, eq_of_eqN' x15, eq_of_eqN' x16, eq_of_eqN' x17,
      eq_of_eqN' x18, eq_of_eqN' x19, eq_of_eqN' x20, eq_of_eqN' x21, eq_of_eqN' x22,
      eq_of_eqN' x23, eq_of_eqN' x24, eq_of_eqN' x25, eq_of_eqN' x26, eq_of_eqN' x27,
      eq_of_eqN' x28, eq_of_eqN' x571, eq_of_eqN' x572, eq_of_eqN' x573, eq_of_eqN' x574,
      eq_of_eqN' x575, eq_of_eqN' x576, eq_of_eqN' x577, eq_of_eqN' x578, eq_of_eqN' x579,
      eq_of_eqN' x580, eq_of_eqN' x581, eq_of_eqN' x582, eq_of_eqN' x583, eq_of_eqN' x584,
      eq_of_eqN' x585, eq_of_eqN' x586, eq_of_eqN' x587, eq_of_eqN' x588, eq_of_eqN' x589,
      eq_of_eqN' x590, eq_of_eqN' x591, eq_of_eqN' x592, eq_of_eqN' x593, eq_of_eqN' x594,
      eq_of_eqN' x595, eq_of_eqN' x596, eq_of_eqN' x597, eq_of_eqN' x598, eq_of_eqN' x599,
      eq_of_eqN' x600, eq_of_eqN' x601, eq_of_eqN' x602, eq_of_eqN' x603, x604, x605, x606, x607,
      x608, x609, eq_of_eqN' x610, eq_of_eqN' x611, eq_of_eqN' x612, eq_of_eqN' x613,
      ne_of_neN' x614, eq_of_eqN' x615, ne_of_neN' x616, eq_of_eqN' x617, ne_of_neN' x618,
      ne_of_neN' x619, eq_of_eqN' x620, eq_of_eqN' x621, eq_of_eqN' x622, eq_of_eqN' x623,
      eq_of_eqN' x624, eq_of_eqN' x625, eq_of_eqN' x626, ne_of_neN' x627, ne_of_neN' x628,
      eq_of_eqN' x629, eq_of_eqN' x630, eq_of_eqN' x631⟩

end CFSG.KC.Th.Spec

end
