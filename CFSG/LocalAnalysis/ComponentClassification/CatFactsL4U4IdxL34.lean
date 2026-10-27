module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxS
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxRed
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4FixL34

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Idx

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem T_le_case_l34
    (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 5 1 ∨ Blueprint.LieModel (OddBar h.J) .PSL 2 7 1)
    (hKa : conjugate h.K h.a = h.K) (hK : Blueprint.LieModel (ZStarBar h.K) .PSL 3 2 2) :
    h.T ≤ zpowers h.a ⊔ h.B := by
  apply T_le_of_fixCatS h hKa
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hLie : Blueprint.LieModel (OddBar h.K ⧸ center (OddBar h.K)) .PSL 3 2 2 :=
    lieModel_of_mulEquiv_ne_zero eZ.symm (by norm_num) hK
  obtain ⟨ψ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hLie
  have hZJ : center (OddBar h.J) = ⊥ := by
    rcases hJ with hJ | hJ
    · exact IdxRed.center_eq_bot_of_psl2 hJ
    · exact IdxRed.center_eq_bot_of_psl2 hJ
  refine fixCatS_of_cover h.isQuasisimple_K.1 hZJ (FixCat.of_mulEquiv ψ (FixL34.fixCat_S ?_))
  rcases hJ with hJ | hJ
  · left
    rw [card_of_lieModel_psl2 (by norm_num) hJ]
    rfl
  · right
    rw [card_of_lieModel_psl2 (by norm_num) hJ]
    rfl

end Idx

end CFSG.ComponentClassification.CatFactsL4U4
