module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement

section Setting

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} (hGN : GNSetting X T)
  (hV : IsElemAbelian 2 (gnV T)) [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

include hGN hV in
theorem map_mk_le_normalizer_component {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    {A : Subgroup X} (hA : IsMaxElemAbelian T A) :
    A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
  (le_bestOffenderSub (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep hV hGN hA)).trans
    (bestOffenderSub_le_normalizer_component (gnRep hV) (gnRep_injective hV)
      ((isComponent_iff_open L).2 hL))

include hGN hV in
theorem exists_maxElemAbelian_commutator_eq {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    ∃ A : Subgroup X, IsMaxElemAbelian T A ∧ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = L := by
  have hC : CFSG.IsComponent L := (isComponent_iff_open L).2 hL
  have hQ : CFSG.IsQuasisimple L := hC.1
  have hLbot : L ≠ ⊥ := by
    intro h
    have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
    subst h
    have : Nontrivial
        (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T))) :=
      hs.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne
      (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T)))
    induction x using QuotientGroup.induction_on with
    | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b => exact hxy (congrArg QuotientGroup.mk (Subsingleton.elim a b))
  have hnorm := fun A (hA : IsMaxElemAbelian T A) => map_mk_le_normalizer_component hGN hV hL hA
  by_contra hno
  push Not at hno
  have hcen : ∀ A : Subgroup X, IsMaxElemAbelian T A →
      A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
    intro A hA
    by_cases hb : ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = ⊥
    · intro a ha l hl
      have : ⁅l, a⁆ ∈ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ :=
        Subgroup.commutator_mem_commutator hl ha
      rw [hb, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.1 this
    · exact absurd (commutator_eq_of_ne_bot hQ (hnorm A hA) hb) (hno A hA)
  have hJle : gnImg T (thompsonJ T) ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
    unfold gnImg thompsonJ
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hA => hcen A hA
  apply hLbot
  rw [← hJ, eq_bot_iff, Subgroup.commutator_le]
  intro l hl j hj
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2
    (Subgroup.mem_centralizer_iff.1 (hJle hj) l hl)

include hGN hV in
theorem exists_rep_offender_J {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    ∃ A : Subgroup (X ⧸ gnC T), CFSG.IsElementaryAbelian 2 A ∧
      CFSG.RankThree.FFModules.IsBestOffender (gnRep hV) A ∧
      A ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ∧ ⁅L, A⁆ = L ∧
      A ≤ gnImg T (thompsonJ T) := by
  obtain ⟨A, hAmax, hLA⟩ := exists_maxElemAbelian_commutator_eq hGN hV hL hJ
  refine ⟨A.map (QuotientGroup.mk' (gnC T)), isElementaryAbelian_map_mk hAmax,
    isBestOffender_gnRep hV hGN hAmax, map_mk_le_normalizer_component hGN hV hL hAmax, hLA, ?_⟩
  unfold gnImg
  exact Subgroup.map_mono (le_iSup₂_of_le A hAmax le_rfl)

end Setting

end CFSG.LocalAnalysis.RankThreeUC.S15
