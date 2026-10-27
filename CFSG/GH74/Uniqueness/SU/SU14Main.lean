module

public import CFSG.GH74.Uniqueness.SU.SU14Alt
public import CFSG.GH74.Uniqueness.SU.SU14Basic
public import CFSG.GH74.Uniqueness.SU.SU14Hbar
public import CFSG.GH74.Uniqueness.SU.SU14Walter
public import CFSG.GH74.Uniqueness.SU.SU7Stmts
public import CFSG.GH74.Uniqueness.SU.SU12Stmts
public import CFSG.GH74.Uniqueness.SU.SU13Stmts
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup CFSG.Blueprint

theorem S_Thm182_of_stmts
    (h183 : SU4.Lemma183Stmt) (h184 : SU7.Thm184Stmt)
    (h211 : SU10.Prop211Stmt) (h213 : SU10.Cor213Stmt) (h221 : SU12.Prop221Stmt)
    (h231 : SU13.Thm231Stmt) : S_Thm182 := by
  intro G _ _ hsimple hnonab hkgh S hrank hgamma
  obtain ⟨U, hsetup, hUS, hUc⟩ := exists_setup18 hsimple hnonab hkgh S hrank
  obtain ⟨M, hHyp⟩ := exists_hyp184 h183 hsetup hgamma
  obtain ⟨hΓ, hnoiso⟩ := h184 G S U M hHyp
  obtain ⟨z, hzord, hzc⟩ := exists_central_involution_sylow S hUS hUc
  have hH21 : SU10.Hyp21 S M z := hyp21_of hHyp hΓ hnoiso hzord hzc
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hzc s hs)
  obtain ⟨hOle, hcases⟩ := h211 G S M z hH21
  by_cases hC : centralizer ({z} : Set G) ≤ M
  · exact Or.inr (h213 G S M z hH21 hC)
  · have hshape := hcases.resolve_left hC
    rcases hshape with hb | ⟨hA, -, -⟩
    ·
      exfalso
      have hbot := h221 G S M z
        { toHyp21 := hH21, not_le := hC, oPrime_le := hOle, shape := hb }
      exact h231 G hsimple hnonab z hzord 9 (Or.inl rfl)
        (isTwoAlt_of_pPrimeCore_eq_bot _ hbot hb.1)
    ·
      obtain ⟨Y, _, hY, ⟨e⟩⟩ := hA
      obtain ⟨eY⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model Y hY
      obtain ⟨hcomm, h8, h5⟩ := sylow_facts_of_hbar S hSC eY e
      exact Or.inl (isSporadic_J1_of_abelian_sylow hsimple hnonab S hcomm h8
        (h5.trans (Subgroup.card_subgroup_dvd_card _)))

end CFSG.GH74.Uniqueness.SU.SU14
