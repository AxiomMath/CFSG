module

public import CFSG.ClassicalInvolution.Asc77.AscT3SFuse
public import CFSG.ClassicalInvolution.Asc77.AscT7S22Z
public import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Comm

variable {G : Type} [Group G]

theorem oddQuotMk_comm_of_commutator_mem {c a k : G}
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (hkC : k ∈ Subgroup.centralizer ({c} : Set G))
    (h : ⁅a, k⁆ ∈ oddCoreIn (Subgroup.centralizer ({c} : Set G))) :
    oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨k, hkC⟩ =
      oddQuotMk c ⟨k, hkC⟩ * oddQuotMk c ⟨a, haC⟩ := by
  have hcC : ⁅a, k⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [commutatorElement_def]
    exact (Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem haC hkC)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem haC))
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hkC)
  have h1 := oddQuotMk_eq_one_of_mem_oddCoreIn h hcC
  have e : (⟨a, haC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨k, hkC⟩ =
      ⟨⁅a, k⁆, hcC⟩ * (⟨k, hkC⟩ * ⟨a, haC⟩) := by
    apply Subtype.ext
    change a * k = ⁅a, k⁆ * (k * a)
    rw [commutatorElement_def]
    group
  rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]

end Comm

section Hyp

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G}
  {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t) {a : G} (h : AConf S K K' J z a)
include d h

theorem s_hyp51At_z : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) z := by
  have hq : 5 ≤ p ^ f := d.branch.five
  have hΩ := d.hyp
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hc₁ : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ d.late_mem_K d.viol.hzK
  have hc₂ : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ d.late_mem_K' d.late_hzK'
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := T7S22.le_centralizer_of_classical hc₁
  have hK'C : K' ≤ Subgroup.centralizer ({z} : Set G) := T7S22.le_centralizer_of_classical hc₂
  have hK₁c : CFSG.IsComponent (modOdd z K) :=
    (CFSG.isComponent_iff_open _).mpr (isComponentOf_modOdd hc₁ hq)
  have hK₂c : CFSG.IsComponent (modOdd z K') :=
    (CFSG.isComponent_iff_open _).mpr (isComponentOf_modOdd hc₂ hq)
  have hBab := d.s_B_isElemAbelian h.hA h.ha2
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have haB : a ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d.s_comm_z h.hA.1.1)
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr d.late_zt_comm.symm
  have haz : a ≠ z := fun e => d.s_a_not_mem_closure h.c4 h.hA h.ha1 (by
    rw [e]
    exact Subgroup.subset_closure (by simp))
  have hnot_a := Lemma52Proof.oddQuotMk_not_mem_zpowers hBab hzB hz1 haB h.ha1 haz haC
  have hnot_t := Lemma52Proof.oddQuotMk_not_mem_zpowers hBab hzB hz1 htB d.viol.hzJ.ne_one
    d.late_ne_inv htC
  have hKO : oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal (T7A.isSubnormal_centralizer d.hyp d.late_mem_K d.viol.hzK)
  have hK'O : oddCoreOf K' ≤ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal
      (T7A.isSubnormal_centralizer d.hyp d.late_mem_K' d.late_hzK')
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L →
      MovedByAll (Subgroup.closure ({z, t, a} : Set G)) z L → False := by
    intro L hL hmov
    by_cases hLK : L = modOdd z K
    · obtain ⟨y, hyL, hy⟩ := hmov _ (oddQuotMk_mem_modOdd haB haC) hnot_a
      rw [hLK] at hyL
      obtain ⟨k', hk'K, rfl⟩ := mem_modOdd_iff.mp hyL
      exact hy (oddQuotMk_comm_of_commutator_mem haC k'.2 (hKO (d.s_comm_K h.hA hk'K)))
    by_cases hLK' : L = modOdd z K'
    · obtain ⟨y, hyL, hy⟩ := hmov _ (oddQuotMk_mem_modOdd haB haC) hnot_a
      rw [hLK'] at hyL
      obtain ⟨k', hk'K, rfl⟩ := mem_modOdd_iff.mp hyL
      exact hy (oddQuotMk_comm_of_commutator_mem haC k'.2 (hK'O (d.s_comm_K' h.hA hk'K)))
    have hc₁' : ⁅L, modOdd z K⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hL hK₁c).resolve_left hLK
    have hc₂' : ⁅L, modOdd z K'⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hL hK₂c).resolve_left hLK'
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

end Std20

end Hyp

end CFSG.ClassicalInvolution.Asc77.T3CII
