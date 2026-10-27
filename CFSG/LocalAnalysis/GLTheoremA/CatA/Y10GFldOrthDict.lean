module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F

@[expose] def OrthLabelDict : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (labJ : GLALabel) (m f : ℕ),
    HasLabel J (fun l : GLALabel => l = labJ) →
      (StatedClassicalModel (J ⧸ Subgroup.center J) .POmegaPlus m 2 f →
        canonLabel labJ = ⟨.D, m, f⟩) ∧
      (StatedClassicalModel (J ⧸ Subgroup.center J) .POmegaMinus m 2 f →
        canonLabel labJ = ⟨.twD, m, f⟩)

theorem orthLabelDict_of_ggLabelRigidInput (hRig : CFSG.StandardType.GGLabelRigidInput) :
    OrthLabelDict := by
  intro J _ _ labJ m f hJ
  obtain ⟨hlab, -, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hJ
  refine ⟨fun hM => ?_, fun hM => ?_⟩
  ·
    obtain ⟨-, hf, hm⟩ := hM.1
    have hm3 : m ≠ 3 := by omega
    have hhas' : CFSG.StandardType.GGHasLabel ⟨.D, m, f⟩ (J ⧸ Subgroup.center J) := by
      show if m = 3 then _ else _
      rw [if_neg hm3]
      exact CFSG.StandardType.recipeOmegaPlus_of_statedClassicalModel hM
    rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso
      (hRig labJ ⟨.D, m, f⟩ _ hlab ⟨hf, (by omega : 3 ≤ m)⟩ hhas hhas')]
    simp [canonLabel, hm3]
  ·
    obtain ⟨-, hf, hm⟩ := hM.1
    have hm2 : m ≠ 2 := by omega
    have hm3 : m ≠ 3 := by omega
    have hhas' : CFSG.StandardType.GGHasLabel ⟨.twD, m, f⟩ (J ⧸ Subgroup.center J) := by
      show if m = 2 then _ else if m = 3 then _ else _
      rw [if_neg hm2, if_neg hm3]
      exact CFSG.StandardType.recipeOmegaMinus_of_statedClassicalModel hM
    rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso
      (hRig labJ ⟨.twD, m, f⟩ _ hlab ⟨hf, (by omega : 2 ≤ m)⟩ hhas hhas')]
    simp [canonLabel, hm2, hm3]

theorem orthLabelDict_holds :
    OrthLabelDict :=
  orthLabelDict_of_ggLabelRigidInput CFSG.StandardType.ggLabelRigidInput_holds

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth
