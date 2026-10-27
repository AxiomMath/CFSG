module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Ctx
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem jElem_le (S : Subgroup G) : JElem S ≤ S := by
  refine (Subgroup.closure_le S).2 ?_
  rintro x ⟨A, hA, hx⟩
  exact hA.1 hx

theorem secB_le_inf (S L : Subgroup G) : secB S L ≤ S ⊓ L :=
  jElem_le (S ⊓ L)

theorem secB_le_S (S L : Subgroup G) : secB S L ≤ S :=
  (secB_le_inf S L).trans inf_le_left

theorem secB_le_L (S L : Subgroup G) : secB S L ≤ L :=
  (secB_le_inf S L).trans inf_le_right

theorem isSimpleGroup_of_isPSp43 [Finite G] {L : Subgroup G} (h : IsPSp43 L) :
    IsSimpleGroup ↥L := by
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
  exact (CFSG.LieType.Simplicity.fam_classical_converse ↥L ⟨.PSp, 2, 3, 1, hmodel⟩).2.2

theorem inf_centralizer_eq_bot_of_psp43 [Finite G] {L : Subgroup G} (hq : IsQuasisimple ↥L)
    (h : IsPSp43 L) : L ⊓ centralizer (L : Set G) = ⊥ := by
  haveI : IsSimpleGroup ↥L := isSimpleGroup_of_isPSp43 h
  have hcenter : Subgroup.center ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hc | hc
    · exact hc
    · exfalso
      have hcomm : commutator ↥L = ⊥ := (commutator_eq_bot_iff_center_eq_top ↥L).2 hc
      have htop : (⊤ : Subgroup ↥L) = ⊥ := (Group.isPerfect_def.mp hq.1).symm.trans hcomm
      exact (IsSimpleGroup.toNontrivial (G := ↥L)).exists_pair_ne.elim fun a ⟨b, hab⟩ =>
        hab (by
          have ha : a ∈ (⊥ : Subgroup ↥L) := htop ▸ Subgroup.mem_top a
          have hb : b ∈ (⊥ : Subgroup ↥L) := htop ▸ Subgroup.mem_top b
          rw [Subgroup.mem_bot] at ha hb
          rw [ha, hb])
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨hxL, hxC⟩ := hx
  have hmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC a a.2)
  rw [hcenter, Subgroup.mem_bot] at hmem
  have : x = 1 := congrArg Subtype.val hmem
  simp [this]

end CFSG.OddStandard.SmallF3.Omega
