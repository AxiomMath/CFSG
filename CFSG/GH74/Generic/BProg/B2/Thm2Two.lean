module

public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyG5
public import CFSG.GH74.Generic.BProg.B2.FamilyEasy
public import CFSG.GH74.Generic.BProg.B2.FamilyL3
public import CFSG.GH74.Generic.BProg.B2.L3Cover
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Five
public import CFSG.GH74.Generic.BProg.B2.PuL4GraphUniFinal
public import CFSG.GH74.Generic.BProg.B2.PuG2Odd
public import CFSG.GH74.Generic.BProg.B2.PumpupTableProved
public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyRank1
public import CFSG.GH74.Generic.BProg.B2.SDLeaf
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Done
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Three
public import CFSG.GH74.Generic.BProg.B2.GenLocU3Final

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Final2

theorem stage2Thm2C_of_inputs_l4_s1
    (hl4 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → TA7.PuL4m J → WeakSig2NormG4 J)
    (hs1 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape1 J → WeakSig2NormG4 J) :
    Stage2Thm2C := by
  have hU : ∀ (J : Type) [Group J] [Finite J] {p f : ℕ},
      (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) → LieModel J .PSU 3 p f → GenProp J :=
    fun J _ _ p f hq hJ => by
      rcases hq with h5 | h7 | h9
      · exact GenLocU3Small.genProp_psu3_five_nine (Or.inl h5) hJ
      · exact genProp_psu3_seven h7 hJ
      · exact GenLocU3Small.genProp_psu3_five_nine (Or.inr h9) hJ
  have hL33 : ∀ (J : Type) [Group J] [Finite J], LieModel J .PSL 3 3 1 → GenLoc4 J :=
    fun J _ _ hJ => genLoc4_l3_three hJ
  have hL5 : ∀ (J : Type) [Group J] {p f : ℕ}, p ^ f = 5 → LieModel J .PSL 3 p f → GenLoc J :=
    fun J _ p f h5 hJ => genLoc_psl3_five h5 hJ
  have hL4m : TA7.RefinePuL4 := fun N _ _ H t L hs h4 hJ => puL4m_of_gen4_proved H t L hs h4 hJ
  have hG2 : TA7.RefinePuG2 := fun N _ _ H t L hs hJ => puG2Odd_of_shape H t L hs hJ
  have hB : B_B2_g4 := CFSG.GH74.GLS.b_B2_g4_proved
  have hNo : NoJPrimeNonSD := noJPrimeNonSD
  have hPump : PumpupTableU := PumpupOutOrders.pumpupTableU_proved
  have hs3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape3 J → WeakSig2NormG4 J :=
    fun J _ _ hq h => weakSig2NormG4_qShape3 hL5 hU hq h
  have hp3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsSimpleGroup J → QShape3 J →
      WeakSig2TwoG4 J := fun J _ _ hq hs h => weakSig2TwoG4_qShape3 hL5 hU hs hq h
  have hFam : ListedWeakSigMinFamG5 :=
    listedWeakSigMinFamG5_of hl4 (fun J _ _ hq h => weakSig2NormG4_pul3sq hq h) hs1 hs3 hp3
  have hRank1 : RankOneRecog := rankOneRecog
  have hc23 : SD2.C23Kill :=
    SD2.c23Kill_of_min_g5 hL4m hG2 hB hPump (ListedWeakSigMinG5.of_fam hFam)
  have hWS : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → SD2.SmallLie J →
      WeakSig2NormG4 J :=
    fun J _ _ => smallLie_weakSig_of (fun J _ _ hq h => weakSig2NormG4_of_l3Three hL33 hq h)
      (fun J _ _ hq h => weakSig2NormG4_of_qShape3Cover hs3 hq h) (J := J)
  have hSD : SD.Thm2CaseSDJ :=
    SD2.thm2CaseSDJ_of hc23 (fun J _ _ h => genProp_qShape3SD hU h) hp3 hWS
  exact stage2Thm2C_of_min_fam_g5 hL4m hG2 hB hNo hPump hFam hRank1 SD.TwoA7TermG.pumpupTwoA7GH hSD

end Final2

end CFSG.GH74.Generic.BProg.B2
