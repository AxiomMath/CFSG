module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Config

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

namespace CoreConfig

variable {Y : Subgroup X} {u z : X} (hc : CoreConfig Y u z)
include hc

theorem caseTwo_mem_twoCore : u ∈ CFSG.Open.pCore 2 X := by
  have hnorm : (Subgroup.zpowers u).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((hc.commute_center g).zpow_right k).eq, mul_inv_cancel_right]
    exact hn⟩
  exact le_twoCore hnorm (isPGroup_zpowers_of_orderOf_eq_two hc.order) (Subgroup.mem_zpowers u)

theorem caseTwo_twoCore_le : CFSG.Open.pCore 2 X ≤ Y := by
  obtain ⟨P, hPY, -, -, -⟩ := hc.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((twoCore_isPGroup X).le_sylow_of_normal P).trans hPY

theorem caseTwo_twoCore_pRank : CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) = 1 := by
  have hle : CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) ≤ 1 := by
    by_contra h
    have hN := hc.normalizer_le _ hc.caseTwo_twoCore_le (by omega)
    rw [Subgroup.normalizer_eq_top] at hN
    exact hc.ne_top (top_le_iff.mp hN)
  have hge : 1 ≤ CFSG.Open.pRank 2 (CFSG.Open.pCore 2 X) :=
    CFSG.SectionRank.le_pRank (by decide) (Subgroup.zpowers_le.mpr hc.caseTwo_mem_twoCore)
      (involution_zpowers_elementary u hc.order) (by rw [Nat.card_zpowers, hc.order, pow_one])
  omega

theorem caseTwo_mem_pCore : u ∈ CFSG.pCore 2 X := by
  exact hc.caseTwo_mem_twoCore

theorem caseTwo_pCore_pRank : CFSG.Open.pRank 2 (CFSG.pCore 2 X) = 1 := by
  exact hc.caseTwo_twoCore_pRank

theorem caseTwo_eq_of_mem_twoCore {w : X} (hw : w ∈ CFSG.Open.pCore 2 X) (hw2 : orderOf w = 2) :
    w = u :=
  eq_of_mem_twoCore_of_rank_one hc.center hc.order hc.caseTwo_mem_pCore hc.caseTwo_pCore_pRank
    (by exact hw) hw2

omit [Finite X] hc in
theorem caseTwo_lever_mem_centralizer {P : Sylow 2 X} (hzc : ∀ p ∈ (P : Subgroup X), Commute p z) :
    z ∈ Subgroup.centralizer ((P : Subgroup X) : Set X) :=
  Subgroup.mem_centralizer_iff.mpr fun p hp => (hzc p hp).eq

theorem caseTwo_not_forall_commute :
    ¬ ∀ J : Subgroup X, CFSG.IsComponent J → ∀ j ∈ J, Commute z j := by
  intro h
  obtain ⟨P, -, -, -, hzc⟩ := hc.sylow
  have hzO := mem_pCore_of_commute_components hc.oddCore_eq_bot P
    (caseTwo_lever_mem_centralizer hzc) h
  exact hc.lever_ne (hc.caseTwo_eq_of_mem_twoCore hzO hc.lever_order)

theorem caseTwo_layer_ne_bot : CFSG.layer X ≠ ⊥ := by
  intro hbot
  refine hc.caseTwo_not_forall_commute fun J hJ => ?_
  have hJle : J ≤ CFSG.layer X := le_sSup hJ
  rw [hbot] at hJle
  have : Nontrivial J := CFSG.ComponentClassification.Quasisimple.nontrivial
    ((CFSG.isComponent_iff_open J).mp hJ).2.2
  exact absurd (le_bot_iff.mp hJle) (J.nontrivial_iff_ne_bot.mp this)

theorem caseTwo_commute_component_of_pRank_le_one {P : Sylow 2 X} {y : X} (hy : orderOf y = 2)
    (hyc : y ∈ Subgroup.centralizer ((P : Subgroup X) : Set X)) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (huJ : u ∈ J) (hrank : CFSG.Open.pRank 2 J ≤ 1) :
    ∀ j ∈ J, Commute y j :=
  commute_of_pRank_le_one hc.center hc.order hJ huJ hrank hy
    (mem_normalizer_component hc.oddCore_eq_bot P hyc hJ) inf_le_right
    (P.isPGroup'.to_le inf_le_left)
    (fun _ hRJ hR => card_le_card_sylow_inf_of_isSubnormal P hJ.2 hRJ hR)
    (fun q hq => (Subgroup.mem_centralizer_iff.mp hyc q hq.1).symm)

theorem caseTwo_false_of_forall_pRank_le_one
    (hcomp : ∀ J : Subgroup X, CFSG.IsComponent J → u ∈ J ∧ CFSG.Open.pRank 2 J ≤ 1) : False := by
  obtain ⟨P, -, -, -, hzc⟩ := hc.sylow
  exact hc.caseTwo_not_forall_commute fun J hJ =>
    hc.caseTwo_commute_component_of_pRank_le_one hc.lever_order
      (caseTwo_lever_mem_centralizer hzc) hJ (hcomp J hJ).1 (hcomp J hJ).2

theorem caseTwo_exists_two_le_pRank (hcase : ∀ J : Subgroup X, CFSG.IsComponent J → u ∈ J) :
    ∃ J : Subgroup X, CFSG.IsComponent J ∧ 2 ≤ CFSG.Open.pRank 2 J := by
  by_contra h
  push Not at h
  exact hc.caseTwo_false_of_forall_pRank_le_one fun J hJ => ⟨hcase J hJ, by have := h J hJ; omega⟩

theorem caseTwo_mem_of_normal (hcase : ∀ J : Subgroup X, CFSG.IsComponent J → u ∈ J)
    {L : Subgroup X} [L.Normal] (hne : L ≠ ⊥) : u ∈ L :=
  mem_of_normal_of_forall_component_mem hc.oddCore_eq_bot hc.center hc.order hc.caseTwo_mem_pCore
    hc.caseTwo_pCore_pRank hcase hne

end CoreConfig

end CFSG.ProperTwoGeneratedCore.TheoremC
