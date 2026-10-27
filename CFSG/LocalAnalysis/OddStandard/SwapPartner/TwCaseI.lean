module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

private lemma tw_conj_mul_comm {G : Type*} [Group G] {y u v : G} (h : u * v = v * u) :
    (y * u * y⁻¹) * (y * v * y⁻¹) = (y * v * y⁻¹) * (y * u * y⁻¹) := by
  rw [conj_mul, h, ← conj_mul]

private lemma tw_conj_inv_conj {G : Type*} [Group G] (y b : G) :
    y * (y⁻¹ * b * y) * y⁻¹ = b := by
  rw [← MulAut.conj_apply, ← MulAut.conj_symm_apply, MulEquiv.apply_symm_apply]

theorem false_of_normal_abar_of_conj {X : Type*} [Group X] {t : X} {Sg V : Subgroup X}
    (h : SwapShape t Sg V) [(⁅Sg, Sg⁆ : Subgroup X).Normal] {y a : X}
    (ha : a ∈ (⁅Sg, Sg⁆ : Subgroup X)) (ha1 : a ≠ 1) (hy : y * t * y⁻¹ = t * a) : False := by
  have hnorm : (⁅Sg, Sg⁆ : Subgroup X).Normal := inferInstance
  have hcenter_mem : ∀ b : X, b ∈ (⁅Sg, Sg⁆ : Subgroup X) → b * a = a * b := by
    intro b hb
    have hbt : b * t = t * b :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.commutator_sg_le_centralizer hb)
    have hb' : y⁻¹ * b * y ∈ (⁅Sg, Sg⁆ : Subgroup X) := by
      simpa using hnorm.conj_mem b hb y⁻¹
    have hb't : (y⁻¹ * b * y) * t = t * (y⁻¹ * b * y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.commutator_sg_le_centralizer hb')
    have hconj : b * (t * a) = (t * a) * b := by
      have h1 := tw_conj_mul_comm (y := y) hb't
      rwa [tw_conj_inv_conj y b, hy] at h1
    have h2 : t * (b * a) = t * (a * b) := by
      rw [← mul_assoc, ← hbt, mul_assoc, hconj, mul_assoc]
    exact mul_left_cancel h2
  have hcenter : (⟨a, ha⟩ : (⁅Sg, Sg⁆ : Subgroup X)) ∈
      Subgroup.center (⁅Sg, Sg⁆ : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (hcenter_mem (b : X) b.2)
  haveI : IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X) := h.isSimpleGroup_commutator_sg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (⁅Sg, Sg⁆ : Subgroup X)) with hbot | htop
  · rw [hbot, Subgroup.mem_bot] at hcenter
    exact ha1 (Subtype.ext_iff.mp hcenter)
  · haveI hmul : IsMulCommutative (⁅Sg, Sg⁆ : Subgroup X) :=
      Subgroup.center_eq_top_iff.mp htop
    have hp : (Nat.card (⁅Sg, Sg⁆ : Subgroup X)).Prime :=
      Group.is_simple_iff_prime_card.mp ‹IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X)›
    rw [h.card_commutator_sg] at hp
    rcases hp.eq_one_or_self_of_dvd 2 (by norm_num) with h2 | h2
    · exact absurd h2 (by norm_num)
    · exact absurd h2 (by norm_num)

end CFSG.OddStandard.AltStdSec.SwapPartner
