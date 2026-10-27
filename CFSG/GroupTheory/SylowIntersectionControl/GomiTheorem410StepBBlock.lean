module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Type
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBComponent
import CFSG.GroupTheory.AschbacherBlockNatural
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Lift
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBNaturalSL
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBNaturalAlt
import CFSG.Quasithin.Background.G2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort
import CFSG.RankThree.S4Free.StellmacherW

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (PstarSet)

variable {Ω : Type} [Group Ω] [Finite Ω] {G : Subgroup Ω}

private theorem omegaOneCenterIn_eq_omegaOneCenterOf_bblk {K : Type} [Group K]
    (X : Subgroup K) : omegaOneCenterIn X = omegaOneCenterOf X := by
  unfold omegaOneCenterIn omegaOneCenterOf centerOf
  rw [CFSG.center_map_subtype_eq_inf_centralizer X]
  rfl

private theorem map_omegaOneCenterIn_bblk {K L : Type} [Group K] [Group L] (f : K →* L)
    (hf : Function.Injective f) (T : Subgroup K) :
    (omegaOneCenterIn T).map f = omegaOneCenterIn (T.map f) := by
  rw [omegaOneCenterIn_eq_omegaOneCenterOf_bblk,
    omegaOneCenterIn_eq_omegaOneCenterOf_bblk,
    CFSG.RankThree.S4Free.omegaOneCenterOf_map_of_injective' hf T]

private theorem commutator_pCoreOf_le_omegaOneCenterOf_bblk {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B) (hQB : ⁅pCoreOf 2 G, B⁆ ≤ gomiV G) :
    ⁅pCoreOf 2 B, B⁆ ≤ omegaOneCenterOf (pCoreOf 2 B) := by
  intro x hx
  have hxR : x ∈ pCoreOf 2 B :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B)) hx
  have hxV : x ∈ gomiV G := by
    have hle : ⁅pCoreOf 2 B, B⁆ ≤ gomiV G := by
      rw [← commutator_pCoreOf_eq_of_isSubnormal hB.le hB.subnormal hB.residual]
      exact hQB
    exact hle hx
  have hRQ : pCoreOf 2 B ≤ pCoreOf 2 G :=
    CFSG.QuasithinUnique.Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hB.le hB.subnormal
  exact mem_omegaOneCenterOf hxR
    (fun y hy => mem_centralizer_of_mem_omegaOneCenterOf hxV (hRQ hy))
    (sq_eq_one_of_mem_omegaOneCenterOf hxV)

omit [Finite Ω] in
private theorem commutator_pCore_le_omegaOneCenterIn_bblk {B : Subgroup Ω}
    (hcomm : ⁅pCoreOf 2 B, B⁆ ≤ omegaOneCenterOf (pCoreOf 2 B)) :
    ⁅pCore 2 ↥B, (⊤ : Subgroup ↥B)⁆ ≤ omegaOneCenterIn (pCore 2 ↥B) := by
  rw [← Subgroup.map_le_map_iff_of_injective (f := B.subtype) B.subtype_injective]
  rw [Subgroup.map_commutator, map_omegaOneCenterIn_bblk B.subtype B.subtype_injective,
    Subgroup.map_top, Subgroup.range_subtype]
  show ⁅pCoreOf 2 B, B⁆ ≤ omegaOneCenterIn (pCoreOf 2 B)
  rw [omegaOneCenterIn_eq_omegaOneCenterOf_bblk]
  exact hcomm

theorem hasGomiBlock_of_isGomiTwoComponent {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hQB : ⁅pCoreOf 2 G, B⁆ ≤ gomiV G)
    (hnat : (∃ n, 2 ≤ n ∧ IsNaturalSLTwoModule ↥B n) ∨ ∃ n, 1 ≤ n ∧ IsNaturalAltModule ↥B n) :
    HasGomiBlock G := by
  have hU : ⁅pCore 2 ↥B, (⊤ : Subgroup ↥B)⁆ ≤ omegaOneCenterIn (pCore 2 ↥B) :=
    commutator_pCore_le_omegaOneCenterIn_bblk
      (commutator_pCoreOf_le_omegaOneCenterOf_bblk hB hQB)
  have hB₀ : IsAschbacherBlockGomi (⊤ : Subgroup ↥B) :=
    isAschbacherBlockGomi_top_of_isNaturalModule hB.residual hB.quotient hU hnat
  refine hasGomiBlock_of_isSubnormal (H := B) (B₀ := ⊤) hB.le hB₀ ?_ ?_
  · rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hB.subnormal
  · rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hQB

open scoped IsMulCommutative in
theorem IsGomi410bComponent.isGomi410Type_or_hasGomiBlock {W : Subgroup Ω}
    [IsMulCommutative ↥W] {B : Subgroup Ω} {M : Subgroup (MulAut ↥W)}
    (hB : IsGomi410bComponent G W B M) (hW2 : ∀ w : ↥W, w ^ 2 = 1) (h37 : GomiFact37Two)
    {Y S' : Subgroup (MulAut ↥W)} (hM : GomiFact37Hyp Y S' M)
    (hMP : ⁅M, sSup (PstarSet Y)⁆ ≠ ⊥) : IsGomi410Type G B ∨ HasGomiBlock G := by
  have hMeq : M = autOn B W := hB.autOn_eq.symm
  subst M
  rcases h37 ↥W hW2 Y S' (autOn B W) hM hMP with
    ⟨m, hm, hSL, hnat⟩ | ⟨m, hm, hA, hnat⟩ | ⟨hA7, hcard16⟩
  · exact Or.inr (hasGomiBlock_of_isGomiTwoComponent hB.twoComponent hB.commutator_pCoreOf_le
      (Or.inl ⟨m, hm, isNaturalSLTwoModule_of_binaryNaturalSL hB.le_normalizer
        hB.inf_centralizer_eq hB.commutator_eq hSL hnat⟩))
  · rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega] at hA hnat
    exact Or.inr (hasGomiBlock_of_isGomiTwoComponent hB.twoComponent hB.commutator_pCoreOf_le
      (Or.inr ⟨m - 1, by omega, isNaturalAltModule_of_realizes hB.le_normalizer
        hB.inf_centralizer_eq hB.commutator_eq hA hnat⟩))
  · obtain ⟨e⟩ := hB.quotient_equiv
    obtain ⟨e₇⟩ := hA7
    refine Or.inl (Or.inr (Or.inr ⟨⟨e.trans e₇⟩, ?_⟩))
    rw [hB.commutator_gomiV_eq,
      ← CFSG.Quasithin.AutOn.map_commV_autOn_eq hB.le_normalizer,
      Subgroup.card_map_of_injective W.subtype_injective]
    exact hcard16

end CFSG.GroupTheory
