module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSFuse
public import CFSG.ClassicalInvolution.Q3.Q3T6DSComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Three

variable (d : Std20Three K K' J S R R' W V z t) {a : G} (h : AConf3 S K K' J z a)
include d h

theorem s_hyp51At_z : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) z := by
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (d.viol.hzK.commute_of_mem hw).symm
  have hK'C : K' ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (d.late_hzK'.commute_of_mem hw).symm
  have hBab := d.s_B_isElemAbelian h.hA h.ha2
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr d.late_zt_comm.symm
  have hnot_t := Lemma52Proof.oddQuotMk_not_mem_zpowers hBab hzB hz1 htB d.viol.hzJ.ne_one
    d.late_ne_inv htC
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L →
      MovedByAll (Subgroup.closure ({z, t, a} : Set G)) z L → False := by
    intro L hL hmov
    have hc₁' : ⁅L, modOdd z K⁆ = ⊥ :=
      d.commutator_component_modOdd3 d.late_mem_K d.viol.hzK hL
    have hc₂' : ⁅L, modOdd z K'⁆ = ⊥ :=
      d.commutator_component_modOdd3 d.late_mem_K' d.late_hzK' hL
    obtain ⟨y, hyL, hy⟩ := hmov _ (oddQuotMk_mem_modOdd htB htC) hnot_t
    apply hy
    have htcl : t ∈ Subgroup.closure ((K : Set G) ∪ (K' : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      exact d.htKK
    refine oddQuotMk_centralizes_of_closure (a := z) (L := L)
      (𝒵 := (K : Set G) ∪ (K' : Set G)) ?_ htcl htC y hyL
    intro g hg
    rcases hg with hg | hg
    · exact ⟨hKC hg, fun y' hy' =>
        (T7S22.commute_of_commutator_eq_bot hc₁' hy' (oddQuotMk_mem_modOdd hg (hKC hg))).symm⟩
    · exact ⟨hK'C hg, fun y' hy' =>
        (T7S22.commute_of_commutator_eq_bot hc₂' hy' (oddQuotMk_mem_modOdd hg (hK'C hg))).symm⟩
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end Std20Three

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
