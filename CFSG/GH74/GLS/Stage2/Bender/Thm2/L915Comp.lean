module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG
open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem exists_component_noncentral {Z : Subgroup Y} (h : ⁅layer Y, Z⁆ ≠ ⊥) :
    ∃ J : Subgroup Y, IsComponent J ∧ ¬ Z ≤ centralizer (J : Set Y) := by
  by_contra hcon
  refine h (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sSup_le fun K hK => ?_))
  refine Subgroup.le_centralizer_iff.mp ?_
  by_contra hKc
  exact hcon ⟨K, hK, hKc⟩

section Finite

variable [Finite Y]

theorem isComponent_map_mk {p : ℕ} (hp : p.Prime) {J O : Subgroup Y} (hO : O.Normal)
    (hJ : IsComponent J) (hOp : IsPGroup p ↥O) : IsComponent (J.map (QuotientGroup.mk' O)) := by
  have hnle : ¬ J ≤ (QuotientGroup.mk' O).ker := by
    intro hle
    rw [QuotientGroup.ker_mk'] at hle
    exact not_quasisimple_of_pgroup hp hJ.1 (hOp.to_le hle)
  exact ⟨CFSG.LocalCores.isQuasisimple_map hJ.1 (QuotientGroup.mk' O) hnle,
    hJ.2.map (QuotientGroup.mk'_surjective O)⟩

theorem component_le_of_noncentral {K J X : Subgroup Y} (hK : K.Normal) (hJ : IsComponent J)
    (hX : X ≤ K) (hnc : ¬ X ≤ centralizer (J : Set Y)) : J ≤ K := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hJ hK.isSubnormal with h | h
  · exact h
  · refine absurd ?_ hnc
    refine hX.trans ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h

end Finite

theorem component_eq_commutator_of_le {K J : Subgroup Y} (_hK : K.Normal) (hJ : IsComponent J)
    (hJK : J ≤ K) (hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K)) : J = ⁅K, K⁆ := by
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1.1
  have hsub : (J.subgroupOf K).IsSubnormal := hJ.2.subgroupOf
  have hmap := hsub.map (f := QuotientGroup.mk' (center ↥K)) (QuotientGroup.mk'_surjective _)
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hmap with hbot | htop
  · exfalso
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have hcomm : ⁅J, J⁆ = ⊥ := by
      refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      have hxc : (⟨x, hJK hx⟩ : ↥K) ∈ center ↥K := hbot (Subgroup.mem_subgroupOf.mpr hx)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨y, hJK hy⟩).symm
    have hJbot : J = ⊥ := hperf ▸ hcomm
    have hnt : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    exact (Subgroup.nontrivial_iff_ne_bot J).mp hnt hJbot
  · have hsup : J.subgroupOf K ⊔ center ↥K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center ↥K)) (J.subgroupOf K)
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have key : ∀ a b z w : ↥K, z ∈ center ↥K → w ∈ center ↥K → ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
      intro a b z w hz hw
      have hz1 : ⁅z, b * w⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz (b * w)).symm
      have hw1 : ⁅a, w⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw a)
      rw [commutatorElement_mul_left_eq_conj_mul, hz1, commutatorElement_mul_right_eq_mul_conj,
        hw1]
      group
    refine le_antisymm ?_ ?_
    · calc J = ⁅J, J⁆ := hperf.symm
        _ ≤ ⁅K, K⁆ := Subgroup.commutator_mono hJK hJK
    · refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
      have h1 : (⟨g₁, hg₁⟩ : ↥K) ∈ J.subgroupOf K ⊔ center ↥K := hsup ▸ Subgroup.mem_top _
      have h2 : (⟨g₂, hg₂⟩ : ↥K) ∈ J.subgroupOf K ⊔ center ↥K := hsup ▸ Subgroup.mem_top _
      obtain ⟨a, ha, z, hz, haz⟩ := Subgroup.mem_sup_of_normal_right.mp h1
      obtain ⟨b, hb, w, hw, hbw⟩ := Subgroup.mem_sup_of_normal_right.mp h2
      have hab : ⁅a, b⁆ ∈ J.subgroupOf K := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
      have hc : ⁅(⟨g₁, hg₁⟩ : ↥K), (⟨g₂, hg₂⟩ : ↥K)⁆ = ⁅a, b⁆ := by
        rw [← haz, ← hbw]
        exact key a b z w hz hw
      have := Subgroup.mem_subgroupOf.mp hab
      rw [← hc] at this
      exact this

theorem mem_zpowers_of_involution_mul {j r z : Y} (hjr : j * r = r * j) (hr : Odd (orderOf r))
    (hz : z * z = 1) (hzjr : z = j * r) : r ∈ Subgroup.zpowers j := by
  obtain ⟨k, hk⟩ := hr
  have hsq : j * j * (r * r) = 1 := by
    have h1 : j * r * (j * r) = j * j * (r * r) := by
      calc j * r * (j * r) = j * (r * j) * r := by simp only [mul_assoc]
        _ = j * (j * r) * r := by rw [hjr]
        _ = j * j * (r * r) := by simp only [mul_assoc]
    rw [← h1, ← hzjr]
    exact hz
  have h2 : r ^ 2 = (j ^ 2)⁻¹ := by
    rw [pow_two, pow_two]
    exact eq_inv_of_mul_eq_one_right (by simpa [mul_assoc] using hsq)
  have h3 : r = (r ^ 2) ^ (k + 1) := by
    have hpow : r ^ orderOf r = 1 := pow_orderOf_eq_one r
    calc r = r ^ (orderOf r + 1) := by rw [pow_succ, hpow, one_mul]
      _ = (r ^ 2) ^ (k + 1) := by rw [← pow_mul]; congr 1; omega
  rw [h3, h2, inv_pow]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers j) 2) _)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
