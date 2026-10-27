module

public import CFSG.GH74.Generic.BProg.B2.T1G2
public import CFSG.GH74.Generic.BProg.B2.T1One
public import CFSG.GH74.Generic.BProg.B2.T1Uniq
public import CFSG.GH74.Generic.BProg.B2.Thm2Done

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Done


theorem listedWeakSigMinFamG5_proved
    : ListedWeakSigMinFamG5 := by
  have hL5 : ∀ (J : Type) [Group J] {p f : ℕ}, p ^ f = 5 → LieModel J .PSL 3 p f → GenLoc J :=
    fun J _ p f h5 hJ => genLoc_psl3_five h5 hJ
  have hU : ∀ (J : Type) [Group J] [Finite J] {p f : ℕ},
      (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) → LieModel J .PSU 3 p f → GenProp J :=
    fun J _ _ p f hq hJ => by
      rcases hq with h5 | h7 | h9
      · exact GenLocU3Small.genProp_psu3_five_nine (Or.inl h5) hJ
      · exact genProp_psu3_seven h7 hJ
      · exact GenLocU3Small.genProp_psu3_five_nine (Or.inr h9) hJ
  have hl4 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → TA7.PuL4m J → WeakSig2NormG4 J :=
    fun _ _ _ hq h => weakSig2NormG4_puL4m thm2Done_extStmt thm2Done_quatStmt thm2Done_outerStmt hq h
  have hs1 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape1 J → WeakSig2NormG4 J :=
    fun _ _ _ hq h => weakSig2NormG4_qShape1 (fun _ _ _ hF4 => genLoc4_sl4_lin_all hF4)
      thm2Done_extStmt thm2Done_quatStmt thm2Done_outerStmt hq h
  have hs3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape3 J → WeakSig2NormG4 J :=
    fun J _ _ hq h => weakSig2NormG4_qShape3 hL5 hU hq h
  have hp3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsSimpleGroup J → QShape3 J →
      WeakSig2TwoG4 J := fun J _ _ hq hs h => weakSig2TwoG4_qShape3 hL5 hU hs hq h
  exact listedWeakSigMinFamG5_of hl4 (fun J _ _ hq h => weakSig2NormG4_pul3sq hq h) hs1 hs3 hp3

theorem stage2Thm1_proved
    : Stage2Thm1 := by
  intro G _ _ x K A M P Q hs
  have hL4m : TA7.RefinePuL4 := fun N _ _ H t L hs h4 hJ => puL4m_of_gen4_proved H t L hs h4 hJ
  have hG2r : TA7.RefinePuG2 := fun N _ _ H t L hs hJ => puG2Odd_of_shape H t L hs hJ
  have hB : B_B2_g4 := CFSG.GH74.GLS.b_B2_g4_proved
  have hPump : PumpupTableU := PumpupOutOrders.pumpupTableU_proved
  obtain ⟨H, hPre⟩ := stage2Concl1Pre_of_proved hB hs
  have hG2 := T1G2.h_G2_of_pre hL4m hG2r hB hPump hs hPre
  have hO := T1One.O_ne_of_pre listedWeakSigMinFamG5_proved hL4m hG2r hB hPump hs hPre
  have hCore : Stage2Concl1Core x K M Q H := hPre.toCore hG2 hO
  have h2 : Stage2Concl2 M := (stage2Thm2C_proved G x K A M P Q H hs hCore).toConcl2
  exact ⟨H, Stage2Concl1.ofCore hCore (T1Uniq.preuniq_of_core hs hCore h2)⟩

end Done

end CFSG.GH74.Generic.BProg.B2
