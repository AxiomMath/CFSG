module

public import CFSG.Assembly.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open
open scoped commutatorElement

theorem mem_center_of_commutator_mem_center {G : Type} [Group G] (hq : IsQuasisimple G) {x : G}
    (h : ∀ y : G, ⁅x, y⁆ ∈ Subgroup.center G) : x ∈ Subgroup.center G := by
  have hperf : Group.IsPerfect G := ⟨hq.1⟩
  have hsimp : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  have hperfQ : Group.IsPerfect (G ⧸ Subgroup.center G) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center G))
      (QuotientGroup.mk'_surjective _)
  have hcen : (QuotientGroup.mk x : G ⧸ Subgroup.center G) ∈
      Subgroup.center (G ⧸ Subgroup.center G) := by
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have hg : ⁅(QuotientGroup.mk g : G ⧸ Subgroup.center G),
        (QuotientGroup.mk x : G ⧸ Subgroup.center G)⁆ = 1 := by
      have hm : (QuotientGroup.mk' (Subgroup.center G) : G →* G ⧸ Subgroup.center G) ⁅g, x⁆ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have := h g
        rw [← commutatorElement_inv, inv_mem_iff] at this
        exact this
      rw [map_commutatorElement] at hm
      exact hm
    exact commutatorElement_eq_one_iff_mul_comm.mp hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (G ⧸ Subgroup.center G)) with
    hbot | htop
  · rw [hbot] at hcen
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
    exact hcen
  · exfalso
    have hle : commutator (G ⧸ Subgroup.center G) ≤ ⊥ := by
      show ⁅(⊤ : Subgroup (G ⧸ Subgroup.center G)), (⊤ : Subgroup (G ⧸ Subgroup.center G))⁆ ≤ ⊥
      rw [Subgroup.commutator_le]
      intro a _ b _
      have hab : a ∈ Subgroup.center (G ⧸ Subgroup.center G) := by
        rw [htop]; exact Subgroup.mem_top a
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_center_iff.mp hab) b).symm
    have htop' : commutator (G ⧸ Subgroup.center G) = ⊤ := Group.IsPerfect.commutator_eq_top
    have hsub : Subsingleton (G ⧸ Subgroup.center G) := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ commutator (G ⧸ Subgroup.center G) := by
        rw [htop']; exact Subgroup.mem_top a
      have hb : b ∈ commutator (G ⧸ Subgroup.center G) := by
        rw [htop']; exact Subgroup.mem_top b
      have ha' := hle ha
      have hb' := hle hb
      rw [Subgroup.mem_bot] at ha' hb'
      rw [ha', hb']
    exact (not_subsingleton (G ⧸ Subgroup.center G)) hsub

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
