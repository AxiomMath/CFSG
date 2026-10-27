module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves
public import CFSG.LocalAnalysis.OddStandard.HigherRank.BlowUpARigid
public import CFSG.GH74.GLS.C3.Layer1.PU4Proved
public import CFSG.GH74.GLS.C3.Layer1.EvenSelTerm
import CFSG.GH74.GLS.C3.Layer1.St1RigMain
import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank
public import CFSG.Sporadic.ONOddCore.MOddCore

public section

namespace CFSG.OddStandard.HigherRank

open CFSG Subgroup
open CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.ComponentClassification.GSThmB

theorem blowUpAFalse
    (hP9 : GS82PumpInputs.L34ExpFourPumpInput) (hStd : L34StandardInput) : BlowUpAFalse := by
  intro X _ _ hs hnab hKP hncat hbal v M hv hMC hMpc hML h16
  have hX : IsKProperSimple X := ⟨hs, hnab, hKP⟩
  have hOdd : ∀ y : X, orderOf y = 2 → pPrimeCore 2 ↥(centralizer ({y} : Set X)) = ⊥ :=
    fun y hy => by
      have h := hbal y hy
      rwa [Sporadic.ONOddCore.oddCore_eq_pPrimeCore] at h
  have h3M : 3 ≤ pRank 2 ↥M :=
    GrSLit.GrS5.three_le_pRank_of_l34 (isL34Quotient_iff_lieModel_fusionZStar.mp hML)
  have h3X : 3 ≤ pRank 2 X := h3M.trans (GH74.GLS.Bg.pRank_subgroup_le one_lt_two M)
  have hR : ∀ y : X, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set X)) :=
    rankThreeCentralizers X hs hnab h3X
  have hILo : IsILo 2 v M := ⟨hv, by simp only [oBound, ite_true]; exact hR v hv, hMC, hMpc⟩
  have hrig : IsPRigid 2 v M :=
    ⟨hILo, fun x' K' hlong => kBar_equiv_of_chain hP9 hX hlong.2 hML h16⟩
  obtain ⟨x, K, hlong, hrigK, hgmK⟩ := exists_rigid_gilman hrig
  have hT2 : IsTwoTerminal x K :=
    isTwoTerminal_of_noDiag hrigK hgmK (noDiag_of_rigid_gilman hR hrigK hgmK)
  obtain ⟨eK⟩ := hrig.2 x K hlong
  have hKL : IsL34Quotient (kBar K) := isL34Quotient_of_mulEquiv eK.symm hML
  have hK16 : Nat.card ↥(center (kBar K)) = 16 :=
    (Nat.card_congr (Subgroup.centerCongr eK).toEquiv).trans h16
  have hTK : GH74.GLS.EvenSelP.TermK K := GH74.GLS.EvenSelP.termK_of_twoTerminal hX h3X hOdd hT2
  have hx2 : orderOf x = 2 := hT2.1.1
  have hxC : x ∈ centralizer (K : Set X) := fun k hk => by
    have := hT2.1.2.2.1 hk
    exact mem_centralizer_singleton_iff.mp this
  have hTP : IsTerminalPair 2 x K := ⟨hx2, hTK.comp x hx2 hxC, hTK.even, hTK.comp⟩
  have hK2 : 2 ≤ pRank 2 ↥K :=
    le_trans (by norm_num)
      (GrSLit.GrS5.three_le_pRank_of_l34 (isL34Quotient_iff_lieModel_fusionZStar.mp hKL))
  have hstd := b_cor_PU4_proved X hX x K hTP.1 hT2.1.2.2 hK2 hTP
  have hKq := GH74.Generic.BProg.IsTerminalPair.isQuasisimple hTP
  have hO : pPrimeCore 2 ↥K ≠ ⊤ := by
    intro htop
    have hodd := odd_card_pPrimeCore ↥K
    rw [htop, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hTP.2.2.1)
  have hLie : Blueprint.LieModel (↥K ⧸ center ↥K) .PSL 3 2 2 :=
    Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (CatLeaf.fusionZStar_eq_center_of_quasisimple hKq hO))
      (isL34Quotient_iff_lieModel_fusionZStar.mp hKL)
  have : IsSimpleGroup X := hs
  rcases hStd X hnab hKP K hstd hLie with e | e | e
  · exact hncat (Or.inr (Or.inr (Or.inr (Or.inr ⟨.Suz, e⟩))))
  · exact hncat (Or.inr (Or.inr (Or.inr (Or.inr ⟨.He, e⟩))))
  · exact hncat (Or.inr (Or.inr (Or.inr (Or.inr ⟨.ONan, e⟩))))

end CFSG.OddStandard.HigherRank
