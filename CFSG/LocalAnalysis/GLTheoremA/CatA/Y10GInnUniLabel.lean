module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniRed
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.Assembly.OpenBridges
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem uniLabelDict_of_ggLabelRigidInput (hRig : GGLabelRigidInput) : UniLabelDict := by
  intro J _ _ labJ a m E _ _ τ' hτ' ha hτ'm hE hJ hφ
  obtain ⟨φ⟩ := hφ
  obtain ⟨hlab, hs, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hJ
  haveI := hs
  have hm : 1 ≤ m := by
    by_contra hm0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show m = 0 by omega] at h2
    norm_num at h2
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · obtain rfl : a = 2 := by omega
    obtain ⟨k, _, _, hk, ⟨ψ⟩⟩ := exists_quot_heldSU_two_equiv_psl τ' hτ' hτ'm hE
    rw [Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig J labJ 2 m k le_rfl hk hJ
      ⟨φ.trans ψ⟩]
  · by_cases h31 : a = 3 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h31
      exfalso
      haveI := isSolvable_quot_heldSU_three_two τ' hτ' (fun x => by simpa using hτ'm x)
        (by simpa using hE)
      exact not_isSolvable_quot_center
        (solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    · have ham : (a, 2 ^ m) ≠ (3, 2) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      obtain ⟨ψ⟩ := nonempty_quot_heldSU_equiv_statedProj uniScalar_holds τ' hτ' hτ'm hE ha3 ham
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hiso : GGLabelIso labJ ⟨.twA, b, m⟩ :=
        hRig labJ ⟨.twA, b, m⟩ (J ⧸ Subgroup.center J) hlab
          (largeEvenInLambda2_twA hm (by omega) fun hb => by omega) hhas
          (ggHasLabel_twA hE (φ.trans ψ))
      rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso]
      rfl

section Certificates


theorem uniLabelDict_holds : UniLabelDict :=
  uniLabelDict_of_ggLabelRigidInput ggLabelRigidInput_holds

theorem innDiagUni_holds : Y10GField.InnDiagUni :=
  innDiagUni_of_pieces uniScalar_holds Y10GInnLin.linLabelDict_holds uniLabelDict_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
