module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem two_le_twoRank_of_frame {A R : Subgroup G} {g : G} {E F : Subgroup G}
    (hF : Frame G A A R g E F) {H : Subgroup G} (hAH : A ≤ H) : 2 ≤ twoRank ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRK : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hsupE : (E ⊓ A) ⊔ R = E := by
    refine le_antisymm (sup_le inf_le_left hF.R_le_E) fun e he => ?_
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRK hF.R_le_E hF.E_le he
    exact mul_mem (mem_sup_left ha) (mem_sup_right hr)
  have hRN : R ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    intro r hr
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
    exact congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx.1⟩ ⟨r, hF.R_le_E hr⟩)
  have h := card_sup_mul_card_inf hRN
  rw [hsupE, hF.cardE, hF.cardR] at h
  have hpos : 0 < Nat.card ((E ⊓ A) ⊓ R : Subgroup G) := Nat.card_pos
  have h16 : 16 ≤ Nat.card (E ⊓ A : Subgroup G) := by nlinarith
  have hEA : IsElemAbelian 2 (E ⊓ A) := AS76b.IsElemAbelian.mono hF.elemE inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_two_of_isElemAbelian hEA)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k <;> omega
  have hk' : Nat.card ((E ⊓ A).subgroupOf H) = 2 ^ k := by
    rw [← hk]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_right.trans hAH)).toEquiv
  exact hk2.trans (CFSG.SectionRank.le_pRank one_lt_two le_top (isElemAbelian_subgroupOf hEA H) hk')

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hq : Open.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hs
  have : Nontrivial (Q ⧸ center Q) := hq.2.toNontrivial
  have : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
  rw [hq.1] at h
  exact lt_irrefl _ h

end CFSG.ComponentClassification.AS81
