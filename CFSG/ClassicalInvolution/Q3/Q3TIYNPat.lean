module

public import CFSG.ClassicalInvolution.Q3.Q3TIYNRows
public import CFSG.ClassicalInvolution.Q3.Q3TD3Y
public import CFSG.ClassicalInvolution.Q3.Q3TD3Ge7
public import CFSG.ClassicalInvolution.Q3.Q3TD3Five
public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Asm
public import CFSG.ClassicalInvolution.Q3.Q3TD3R6Main
public import CFSG.ClassicalInvolution.Q3.Q3TWC2
public import CFSG.ClassicalInvolution.Q3.Q3TY12
public import CFSG.ClassicalInvolution.Q3.Q3TWWPairProved
public import CFSG.ClassicalInvolution.Q3.Q3TWLOdd
public import CFSG.ClassicalInvolution.Q3.Q3TWY33
public import CFSG.ClassicalInvolution.Q3.Q3TY49

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.ClassicalInvolution.Q3.Q3TY
open CFSG.ClassicalInvolution.RouteD.TWD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

section Gen

theorem partnerPattern_of_y4_genOn {P : StatedLieTag → ℕ → Prop} {tY : StatedLieTag} {nY : ℕ}
    {Pat : ∀ {G : Type} [Group G], Set (Subgroup G) → Subgroup G → Subgroup G → G → Prop}
    (hY : YData3 tY nY) (hrow : TwinRow tY nY) (hProw : P tY nY)
    (hadm : StatedLieAdmissible tY nY 3 1)
    (hsign : tY = .PSL ∨ tY = .PSU ∨ tY = .PSp ∨ tY = .POmegaOdd ∨ tY = .POmegaPlus ∨
      tY = .POmegaMinus)
    (h3 : OddThreeFreeInput) (hcls : TwinInvolution3) (hP : CommutingProductP1Input3)
    (hY2 : TwinYType3On P) (hY4 : TwinYPatternAtL3 tY nY Pat) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
        LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z →
        ∀ β ∈ conjClass3 K, ∀ t : G, IsClassicalMember3 β t →
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) →
          HasFixedMember (conjClass3 K) K β z → Pat (conjClass3 K) K β t := by
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ hfix
  obtain ⟨c⟩ := nonempty_tctx3 hY h3 hR hshape
  obtain ⟨T, e, J, J', w, e', s, hcfg⟩ :=
    Q3TD.twinYConfigL3_of_partner_gen hrow hadm hsign hcls h3 hnab hR hshape c hβ ht hKβ hfix
  have hst : s = t := involution_unique3 hcfg.clsβ ht
  subst hst
  obtain ⟨hex, -⟩ := hR.setup
  have hKT : Commutes K T := hcfg.twin.comm_K T hcfg.twin.mem hcfg.twin.ne
  have hJΩ : J ∈ conjClass3 K := hcfg.mem_J.1
  have hJ'Ω : J' ∈ conjClass3 K := hcfg.mem_J'.1
  have hTΩ : T ∈ conjClass3 K := hcfg.twin.mem.1
  have hclsJ : conjClass3 J = conjClass3 K := conjClass3_eq_of_mem hJΩ
  have hSJ : RouteD3Setup J w := RouteD3Setup.of_mem_conjClass3 hR hJΩ hcfg.clsJ
  have hshapeJ : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 J) w :=
    localShapeC3_at_member hR hshape hJΩ hcfg.clsJ
  have hJJ' : Commutes J J' :=
    hcfg.twinJ.comm_K J' hcfg.twinJ.mem hcfg.twinJ.ne
  obtain ⟨hP1u, hO3u⟩ := hP G K z hR T hTΩ hKT e.u e.u_mem_sup
    (twinElt_orderOf_u3 e hR.cls (hex K ⟨1, conjSub_one K⟩) hKT)
    (twinElt_u_not_mem_left3 e hR.cls (hex K ⟨1, conjSub_one K⟩) hKT)
    (twinElt_u_not_mem_right3 e hcfg.clsT (hex T hTΩ) hKT)
  obtain ⟨hP1u', hO3u'⟩ := hP G J w hSJ J' (by rw [hclsJ]; exact hJ'Ω) hJJ' e'.u e'.u_mem_sup
    (twinElt_orderOf_u3 e' hcfg.clsJ (hex J hJΩ) hJJ')
    (twinElt_u_not_mem_left3 e' hcfg.clsJ (hex J hJΩ) hJJ')
    (twinElt_u_not_mem_right3 e' hcfg.clsJ' (hex J' hJ'Ω) hJJ')
  rw [hclsJ] at hP1u' hO3u'
  have hty := hY2 G hnab K z hR tY nY hrow hProw hshape T hcfg.twin hcfg.clsT e hP1u hO3u
  have hty' := hY2 G hnab J w hSJ tY nY hrow hProw hshapeJ J' (by rw [hclsJ]; exact hcfg.twinJ)
    hcfg.clsJ' e' (by rw [hclsJ]; exact hP1u') (by rw [hclsJ]; exact hO3u')
  rw [hclsJ] at hty'
  exact hY4 G hnab K z hR hshape T e J J' w e' β s hcfg hP1u hO3u hP1u' hO3u' hty hty'

end Gen

section D

theorem partnerPatternStmtD3_of_y4On {P : StatedLieTag → ℕ → Prop} {m : ℕ} (hm : 4 ≤ m)
    (hPm : P .POmegaPlus m) (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On P)
    (hY4 : TwinYPatternAtL3 .POmegaPlus m
      (fun Ω K β t => Q3TD.PartnerPatternPlus3 m Ω K β t)) : Q3TD.PartnerPatternStmtD3 m :=
  partnerPattern_of_y4_genOn (tY := .POmegaPlus) (nY := m)
    (yData3_plus hm ⟨Nat.prime_three, le_rfl, by show 4 ≤ m; omega⟩) (Or.inl ⟨rfl, rfl, hm⟩) hPm
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ m; omega⟩
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h3 hcls hP hY2 hY4

theorem partnerPatternStmtD3_allOn (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On TwinRowNeedD3) :
    ∀ m, 4 ≤ m → Q3TD.PartnerPatternStmtD3 m := by
  intro m hm
  rcases (by omega : m = 4 ∨ m = 5 ∨ m = 6 ∨ 7 ≤ m) with rfl | rfl | rfl | h
  · exact Q3TD.partnerPatternStmtD3_four h3
  · exact Q3TD.partnerPatternStmtD3_five h3
  · exact partnerPatternStmtD3_of_y4On (P := TwinRowNeedD3) hm ⟨rfl, rfl⟩ h3 hcls hP hY2
      (Q3TD.twinYPatternAtL3_plus6 h3 hcls)
  · exact Q3TD.partnerPatternStmtD3_ge7 h3 h

theorem chainPiece3TwinD_of_inputsOn (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On TwinRowNeedD3) : ChainPiece3TwinD :=
  Q3TD.chainPiece3TwinD_of_pattern h3 (partnerPatternStmtD3_allOn h3 hcls hP hY2)

theorem piece3TwinD_of_inputsOn (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On TwinRowNeedD3) : Piece3TwinD :=
  piece3TwinD_of_chain h3 (chainPiece3TwinD_of_inputsOn h3 hcls hP hY2)

theorem piece3TwinD_of_inputs_noY2 (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) : Piece3TwinD :=
  piece3TwinD_of_inputsOn h3 hcls hP (twinYType3On_needed_D_of_odd3 h3)

end D

section TD

theorem partnerPatternStmt3_of_y4On {P : StatedLieTag → ℕ → Prop} {m : ℕ} (hm : 4 ≤ m)
    (hPm : P .POmegaMinus m) (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On P)
    (hY4 : TwinYPatternAtL3 .POmegaMinus m
      (fun Ω K β t => PartnerPatternMinus3 m Ω K β t)) : PartnerPatternStmt3 m :=
  have hadm : StatedLieAdmissible .POmegaMinus m 3 1 := ⟨Nat.prime_three, le_rfl, hm⟩
  partnerPattern_of_y4_genOn (tY := .POmegaMinus) (nY := m) (Q3TY.yData3_minus hm hadm)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩))))) hPm hadm
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h3 hcls hP hY2 hY4

theorem partnerPatternStmt3_fourOn (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On TwinRowNeedTD3) :
    PartnerPatternStmt3 4 :=
  partnerPatternStmt3_of_y4On (P := TwinRowNeedTD3) le_rfl ⟨rfl, Or.inl rfl⟩ h3 hcls hP hY2
    (twinYPatternAtL3_td4 h3 hcls)

theorem partnerPatternStmt3_fiveOn (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On TwinRowNeedTD3) :
    PartnerPatternStmt3 5 :=
  partnerPatternStmt3_of_y4On (P := TwinRowNeedTD3) (by norm_num) ⟨rfl, Or.inr rfl⟩ h3 hcls hP hY2
    (twinYPatternAtL3_td5 h3 hcls)

theorem chainPiece3TwinTD_of_inputsOn (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On TwinRowNeedTD3) :
    Q3TW.ChainPiece3TwinTD :=
  chainPiece3TwinTD_of_pattern h3 fun m hm => by
    rcases Nat.lt_or_ge m 8 with h8 | h8
    · interval_cases m
      · exact partnerPatternStmt3_fourOn h3 hcls hP hY2
      · exact partnerPatternStmt3_fiveOn h3 hcls hP hY2
      · exact partnerPatternStmt3_six h3
      · exact partnerPatternStmt3_seven h3
    · exact partnerPatternStmt3_ge8 h3 h8

end TD

section B

theorem partnerPatternStmtB3_of_y4On {P : StatedLieTag → ℕ → Prop} {m : ℕ} (hm : 3 ≤ m)
    (hPm : P .POmegaOdd m) (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On P)
    (hY4 : TwinYPatternAtL3 .POmegaOdd m
      (fun Ω K β t => Q3TWC.PartnerPatternBPair3 m Ω K β t)) : Q3TWC.PartnerPatternStmtB3 m :=
  have hadm : StatedLieAdmissible .POmegaOdd m 3 1 := ⟨Nat.prime_three, le_rfl, hm, by norm_num⟩
  partnerPattern_of_y4_genOn (tY := .POmegaOdd) (nY := m) (yData3_odd hm hadm)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩))) hPm hadm
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h3 hcls hP hY2 hY4

theorem chainPiece3TwinBPair_of_y4On (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On TwinRowNeedB3)
    (hY4 : ∀ m, 3 ≤ m → TwinYPatternAtL3 .POmegaOdd m
      (fun Ω K β t => Q3TWC.PartnerPatternBPair3 m Ω K β t)) : Q3TW.ChainPiece3TwinBPair :=
  Q3TWC.chainPiece3TwinBPair_of_pattern h3 fun m hm =>
    partnerPatternStmtB3_of_y4On (P := TwinRowNeedB3) hm ⟨rfl, hm⟩ h3 hcls hP hY2 (hY4 m hm)

theorem piece3TwinB_of_y4On (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3On TwinRowNeedB3)
    (hY4 : ∀ m, 3 ≤ m → TwinYPatternAtL3 .POmegaOdd m
      (fun Ω K β t => Q3TWC.PartnerPatternBPair3 m Ω K β t)) : Piece3TwinB :=
  Q3TW.piece3TwinB_of_chain_pair h3 Q3TW.weakCT3OddMapPair_proved Q3TW.leviEmbed3Odd_proved
    (chainPiece3TwinBPair_of_y4On h3 hcls hP hY2 hY4)

end B

end CFSG.ClassicalInvolution.Q3.Q3TIY
