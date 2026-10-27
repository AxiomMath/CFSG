module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27RCaseIISix
public import CFSG.Quasithin.Background.SmithC27RCaseIIEight
public import CFSG.Quasithin.Background.SmithC27RCaseIIEightB
public import CFSG.Quasithin.Background.SmithC27RCaseIIOuter8

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {H R M K : Subgroup G}

theorem three_of_residueTypeII_sym_F4 (hC129 : ASC129Statement G) (hC132 : ASInputs.AS_C_1_32_F4)
    (h : Hyp27 H R M K) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hV : IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hJK : ∀ T : Subgroup (MulAut (IntMod (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hV)),
      IsSylowTwoOf T (jPStar hV R K) → jPStar hV R K = autI hV K ⊔ T)
    {n : ℕ} (hn : n = 6 ∨ n = 8) (π : Equiv.Perm (Fin n) →* ↥(jPStar hV R K))
    (hπ : (FFModel.symDn n).RealizesVia (jPStar hV R K) (commV (autI hV K))
      (fixV (autI hV K) ⊓ commV (autI hV K)) π)
    (hπK : ∀ σ : Equiv.Perm (Fin n),
      ((π σ : ↥(jPStar hV R K)) : MulAut (IntMod (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hV)) ∈
        autI hV K ↔ σ ∈ alternatingGroup (Fin n)) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  have hs := h.starHyp
  have hKJ : autI hV K ≤ jPStar hV R K := by
    obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup _) ≤ jPStar hV R K)
      (IsPGroup.of_card (n := 0) (by simp))
    rw [hJK T hT]
    exact le_sup_left
  obtain ⟨C⟩ := nonempty_caseIICtx hs hV hn hKJ π hπ hπK
  rcases hn with rfl | rfl
  · exact three_of_caseII_six_F4 hC132 h hnS C
  · rcases radical_outer_eight (C.isPGroup_bar_R hs) (C.isRadSig_bar_R h.isTwoRadicalIn_sup hs)
      (C.not_bar_R_le_alt hs (by norm_num)) with ⟨T, hT, hTN⟩ | ⟨a, b, hab, hRab⟩ | ⟨g, hg⟩
    · exact three_of_caseII_eight_sylow h hnS C hT hTN
    · exact three_of_caseII_eight_swap hC129 h C hab hRab
    · exact (false_of_caseII_d8v4 h (C.conjB8 g) (by rw [CaseIICtx.bar_conjB8]; exact hg)).elim

end CFSG.Quasithin.SmithC27
