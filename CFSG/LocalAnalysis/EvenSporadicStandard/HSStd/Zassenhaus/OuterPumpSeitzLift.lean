module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpExcludeE
public import CFSG.LieType.Simplicity.Classical
public import CFSG.GH74.Orders.LieType
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.LieModelSimple
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Open.StandardDefs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.EvenSporadicStandard.HSStd
  CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

theorem perfect_centerless_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hnc : ∃ a b : Y, a * b ≠ b * a) : commutator Y = ⊤ ∧ center Y = ⊥ := by
  obtain ⟨a, b, hab⟩ := hnc
  have hc : center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h | h
    · exact h
    · exact absurd (mem_center_iff.1 (h ▸ mem_top b) a) hab
  refine ⟨?_, hc⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
  · exfalso
    have := (_root_.commutator_eq_bot_iff_center_eq_top (G := Y)).1 h
    rw [hc] at this
    exact bot_ne_top this
  · exact h

theorem commutator_eq_self_of_commutator_top {Y : Type*} [Group Y] {K : Subgroup Y}
    (h : commutator ↥K = ⊤) : ⁅K, K⁆ = K := by
  have h2 : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h2, h, Subgroup.map_top, Subgroup.range_subtype]

theorem isSimpleGroup_of_lieModel_psl_four_two {Y : Type} [Group Y] (h : LieModel Y .PSL 4 2 2) :
    IsSimpleGroup Y :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem card_psl_four_two {Y : Type} [Group Y] (h : LieModel Y .PSL 4 2 2) :
    Nat.card Y = 987033600 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_four (h.statedClassicalModel (by decide))

theorem not_commutative_psl_four_two {Y : Type} [Group Y] (h : LieModel Y .PSL 4 2 2) :
    ∃ a b : Y, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hs := isSimpleGroup_of_lieModel_psl_four_two h
  have hcard := card_psl_four_two h
  let _ : CommGroup Y := { ‹Group Y› with mul_comm := hcon }
  have : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  have hp := IsSimpleGroup.prime_card (α := Y)
  rw [hcard] at hp
  exact absurd hp (by norm_num)

section Lift

variable {G : Type} [Group G]

theorem isQuasisimple_outerLift_of_simple (v : G) {K : Subgroup (OuterSection v)}
    [IsSimpleGroup ↥K] (hK : ⁅K, K⁆ = K) (hKc : center ↥K = ⊥) :
    CFSG.IsQuasisimple ↥(outerLift v K) := by
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv (outerLiftEquiv v K) ?_
  refine (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 ?_
  exact ⟨commutator_top_of_commutator_eq_self
    (liftCore_perfect (QuotientGroup.mk'_surjective _) (ker_mk_vSub_le_center v) hK),
    MulEquiv.isSimpleGroup (liftCore_quotientEquiv (QuotientGroup.mk'_surjective _)
      (ker_mk_vSub_le_center v) hK hKc)⟩

theorem isCompIn_outerLift_of_simple (v : G) {K : Subgroup (OuterSection v)}
    [IsSimpleGroup ↥K] (hK : ⁅K, K⁆ = K) (hKc : center ↥K = ⊥) (hs : K.IsSubnormal) :
    IsCompIn (outerLift v K) (centralizer ({v} : Set G)) := by
  refine isCompIn_of_subnormal (outerLift_le v K) (isQuasisimple_outerLift_of_simple v hK hKc) ?_
  rw [outerLift_subgroupOf]
  exact liftCore_isSubnormal _ hs

noncomputable def outerLiftQuotientEquiv (v : G) {K : Subgroup (OuterSection v)}
    (hK : ⁅K, K⁆ = K) (hKc : center ↥K = ⊥) :
    (↥(outerLift v K) ⧸ center ↥(outerLift v K)) ≃* ↥K :=
  (quotientCenterEquivOfEquiv (outerLiftEquiv v K)).symm.trans
    (liftCore_quotientEquiv (QuotientGroup.mk'_surjective _) (ker_mk_vSub_le_center v) hK hKc)

end Lift

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
