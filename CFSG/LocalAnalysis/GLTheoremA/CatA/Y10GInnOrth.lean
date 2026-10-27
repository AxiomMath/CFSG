module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Open
open CFSG.StandardType (GGLabelRigidInput ggLabelRigidInput_holds)

theorem innDiagOrth_of_ggLabelRigidInput (hRig : GGLabelRigidInput) : InnDiagOrth := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  obtain ⟨hmodel, a, rfl⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hFam hin
  have hap : a ^ p = 1 := by
    have hc : a ^ p ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := DFunLike.congr_fun (show MulAut.conj (a ^ p) = 1 by rw [map_pow, hα]) z
      rw [MulAut.conj_apply, MulAut.one_apply] at hz
      exact (mul_inv_eq_iff_eq_mul.mp hz).symm
    rw [hcen] at hc
    exact Subgroup.mem_bot.mp hc
  obtain ⟨t, ht, hG⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t labK.rank 2 (canonLabel labK).n := by
    rcases hmodel with hG | hG
    · exact ⟨_, Or.inl rfl, hG⟩
    · exact ⟨_, Or.inr rfl, hG⟩
  rcases Y10GInnOrthComp.quotCenter_cases_of_glaPComponent_conj_omega ht hG hp hp2 a hap hJ with
    ⟨b, k, E, _, _, hb, hE, hnk, hφ⟩ | ⟨b, k, E, _, _, τ, hτ, hb, hτk, hE, hnk, hφ⟩ |
      ⟨s, K', _, _, hs, hK', hne, ⟨φ⟩⟩ | ⟨s, hM | hM⟩
  ·
    rw [Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _ labJ b k E hb hE hlabJ hφ]
    exact hnk
  ·
    rw [Y10GInnUni.uniLabelDict_of_ggLabelRigidInput hRig _ labJ b k E τ hτ hb hτk hE hlabJ hφ]
    exact hnk
  ·
    rw [Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs hK' hne hlabJ φ]
  ·
    rw [(Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig _ labJ s _ hlabJ).1 hM]
  ·
    rw [(Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig _ labJ s _ hlabJ).2 hM]

section Certificates


theorem innDiagOrth_holds : InnDiagOrth :=
  innDiagOrth_of_ggLabelRigidInput ggLabelRigidInput_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
