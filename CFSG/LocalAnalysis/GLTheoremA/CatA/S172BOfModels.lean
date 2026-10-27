module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BSmall

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem s172FactB_of_models (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hexist : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V) (n : ℕ), (QuadraticMap.polarBilin Q).Nondegenerate →
      Module.finrank (ZMod 2) V = 2 * n → CFSG.GroupTheory.WeirSylow.IsPlusType Q → 7 ≤ n → Odd n →
      (∀ E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q), IsElemAbelian 3 E →
        Nat.card E ≤ 3 ^ (n - 1)) →
      S172X.ModelExist 3 ↥(CFSG.RankThree.Classical2.orthDerived Q) (n - 1) (isUnA (n - 1) 2)
        (isOmMA (n - 1) 2) (isUnA (n - 2) 2))
    (hfive : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V), (QuadraticMap.polarBilin Q).Nondegenerate →
      Module.finrank (ZMod 2) V = 2 * 5 → CFSG.GroupTheory.WeirSylow.IsPlusType Q →
      (∀ E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q), IsElemAbelian 3 E →
        Nat.card E ≤ 3 ^ 4) →
      S172X.ModelSolvable 3 ↥(CFSG.RankThree.Classical2.orthDerived Q) 4 (isUnA 4 2)) :
    S172FactB := by
  intro n hodd Ω _ _ S B D K x hcfg hS hK
  by_cases hn3 : n < 3
  · exact ((S172B.not_catalogIs_isOmPA_of_lt_three (PSimple 3 S) 2 hn3) hS).elim
  · have hn3' : 3 ≤ n := by omega
    by_cases hn5 : n < 5
    · have hn_eq : n = 3 := by
        obtain ⟨k, hk⟩ := hodd
        omega
      subst hn_eq
      norm_num at hK
      exact ((S172B.not_catalogIs_isUnA_two_two (PSimple 3 K)) hK).elim
    · have hn5' : 5 ≤ n := by omega
      obtain ⟨V, instV, instVM, instVFD, Q, hQ, hdim, hplus, hθ⟩ :=
        S172B.exists_omegaPlusTwo_model (n := n) (by omega : 4 ≤ n)
      letI := instV
      letI := instVM
      letI := instVFD
      have hR := S172B.liftableRank_orthDerived hQ hdim hplus hn3' hodd
      have hBin := S172B.mem_sup_centralizer_of_innerDiagMarking_plus hRig hcfg.qs
        (by omega : 4 ≤ n) (k := 1) (by simpa using hS) hcfg.idiag
      rcases eq_or_lt_of_le hn5' with h5eq | h7
      · have hn_eq : n = 5 := h5eq.symm
        subst hn_eq
        have hR' : S172X.LiftableRank 3 ↥(CFSG.RankThree.Classical2.orthDerived Q) 4 := hR
        exact (S172X.false_of_modelSolvable_of_mem_sup hθ hR'
          (hfive V Q hQ hdim hplus hR'.1) Ω S B D K x hcfg hBin hS hK).elim
      · have h7' : 7 ≤ n := by
          obtain ⟨k, hk⟩ := hodd
          omega
        exact S172X.exist_of_model_of_mem_sup hθ hR
          (hexist V Q n hQ hdim hplus h7' hodd hR.1) Ω S B D K x hcfg hBin hS hK

end CFSG.LocalAnalysis.GLTheoremA.S172

end
