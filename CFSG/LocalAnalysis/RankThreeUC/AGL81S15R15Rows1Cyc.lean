module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515D
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517J
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftCore
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K3DvdL3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511P
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512I
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520D

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem s15_rows_lifts_to_20_of_cyc
    (hT : LieOddRankTable) (hK63 : K63) (hK4143 : K4143) (hK7145 : K7145)
    (hK517_4a : K517_4a) (hK517_4b : K517_4b) (hK517_6 : K517_6) (hK518 : K518)
    (hK541 : K541) (hK57 : K57) (hKParU5 : KParU5) (hK5192 : K5192) (hKA10Gen : KA10Gen)
    (hKLiftA7 : KLiftA7) (hK421D : K421Data) (hK421N : K421NonTransLin) (hK89 : K89Sp)
    (hKSch : KSch) (hList : KListI1) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (hKSMOdd : KSMOdd)
    (hKSMAlt : KSMAlt) (hKOut : KOut)
    (hO812 : O812six) (hO1517 : O1517b) (hO1521 : O1521) (hO1521b : O1521b)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hOne : Row1520One G M T T₁ T₂) (hcyc : CycHat G M T) (ctx : S15Ctx2 G M T T₁ T₂) :
    RowLifts G M T T₁ T₂ ∧ Row1511 G M T T₁ T₂ ∧ Row1512 G M T T₁ T₂ ∧ Row1513 G M T T₁ T₂ ∧
      Row1514 G M T T₁ T₂ ∧ Row1515 G M T T₁ T₂ ∧ Row1516 G M T T₁ T₂ ∧ Row1517 G M T T₁ T₂ ∧
      Row1518 G M T T₁ T₂ ∧ Row1519 G M T T₁ T₂ ∧ Row1520 G M T T₁ T₂ := by
  have hLift : RowLifts G M T T₁ T₂ :=
    liftsExist_of_ctx2 hKSch hK63 hList hcyc ctx
  have h11 : Row1511 G M T T₁ T₂ :=
    row1511' hK518 hK517_6 hKSMU4 hKSML3 hK89 K3DvdL3_holds hLift ctx
  have h12 : Row1512 G M T T₁ T₂ := row1512 hT hKSMOdd hKSMU4 hKSMAlt hK541 hKParU5 ctx
  have h13 : Row1513 G M T T₁ T₂ :=
    row1513 hT hKSMOdd hKSMU4 hKSML3 hK541 hK517_4a hK517_4b hK518 hKParU5 ctx hLift h11
  have h14 : Row1514 G M T T₁ T₂ := row1514 hT hKSMOdd hKSMU4 hKSML3 hK517_4b ctx h11
  have h15 : Row1515 G M T T₁ T₂ :=
    row1515 hT hKSML3 hKSMAlt hKSMOdd hKSMU4 hK57 hK541 hKLiftA7 ctx
  have h16 : Row1516 G M T T₁ T₂ := row1516 hT.alt hKSMAlt hKA10Gen hK5192 hK518 hLift ctx
  have h17 : Row1517 G M T T₁ T₂ :=
    row1517 hK518 hK517_6 hK89 K3DvdL3_holds hKSML3 hK4143 hK421D hK421N hKSMOdd hT.chev
      KOutLin_holds hK517_4a hO812 hO1517 hO1521 hO1521b ctx h11
  have h18 : Row1518 G M T T₁ T₂ := row1518 h13 h17
  have h19 : Row1519 G M T T₁ T₂ :=
    row1519 hT hKSMOdd hKSML3 hK517_4a hK518 h11 h14 h16 h17 h18 hLift ctx
  have h20 : Row1520 G M T T₁ T₂ :=
    row1520 hOne hK7145 hKOut hT hKSMOdd hKSMU4 hKSML3 hKSMAlt ctx h11 h12 h15 h19
  exact ⟨hLift, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
