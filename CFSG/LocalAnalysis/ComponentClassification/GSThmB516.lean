module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Outer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTableReduced

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Row516InnerStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K → False

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem not_row516 (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexElim) (hST : SuzukiTausskyInput)
    (hFus : CFProp23Row516) (hStab : CFAutL2Stab) (hCent : CF516Cent)
    (hinner : Row516InnerStatement) (hsec : h.SectionData) : ¬ h.Row516 := by
  intro hrow
  have hin := h.mem_of_row516 hB1 hB6 hB7 hCF23 hCF24 hCFc hCFi hST hFus hStab hCent hsec hrow
  obtain ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ := hrow
  obtain ⟨H', _, _, h', -, ⟨eK⟩, -, -, hJ', hKa', hin', -⟩ := hsec
  have hJs : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
  obtain ⟨eJ⟩ := hJ' (center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_J)
  have hJ'' : Blueprint.LieModel (OddBar h'.J) .PSL 2 p (2 * f) :=
    lieModel_of_mulEquiv_ne_zero eJ.symm (by norm_num) hJ
  have hK'' : Blueprint.LieModel (ZStarBar h'.K) .PSL 4 p f ∨
      Blueprint.LieModel (ZStarBar h'.K) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h'.K) .POmegaMinus 4 p e := by
    rcases hK with hL | hL | ⟨e, he, hL⟩
    · exact Or.inl (lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL)
    · exact Or.inr (Or.inl (lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL))
    · exact Or.inr (Or.inr ⟨e, he, lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL⟩)
  exact hinner H' h' ⟨p, f, hp, hp2, hf, hJ'', hKa'.mpr hKa, hK''⟩ (hin'.mpr hin)

end Hyp52

theorem elim516_of_inputs (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexElim) (hST : SuzukiTausskyInput)
    (hFus : CFProp23Row516) (hStab : CFAutL2Stab) (hCent : CF516Cent)
    (hinner : Row516InnerStatement) (hsec : SectionStatement) : Elim516Statement := by
  intro X _ _ _ hnonab hKP hz hU h hmax hbd hnB1 hnB2a
  exact h.not_row516 hB1 hB6 hB7 hCF23 hCF24 hCFc hCFi hST hFus hStab hCent hinner
    (hsec X hnonab hKP hz hU h hmax hbd hnB1 hnB2a)

end CFSG.ComponentClassification.GSThmB
