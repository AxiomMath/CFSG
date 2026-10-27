module

public import Mathlib.GroupTheory.IsSubnormal

import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.GroupTheory

open Subgroup

variable {Ω : Type*} [Group Ω]

private lemma snm_sInf_le_normalizer {S : Set (Subgroup Ω)} {H : Subgroup Ω}
    (hS : ∀ N ∈ S, H ≤ normalizer (N : Set Ω)) :
    H ≤ normalizer ((sInf S : Subgroup Ω) : Set Ω) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_sInf, Subgroup.mem_sInf]
  exact ⟨fun hx N hN => (Subgroup.mem_normalizer_iff.mp (hS N hN hg) x).mp (hx N hN),
    fun hx N hN => (Subgroup.mem_normalizer_iff.mp (hS N hN hg) x).mpr (hx N hN)⟩

private lemma snm_normal_subgroupOf_subgroupOf {H K G : Subgroup Ω} (hHK : H ≤ K)
    (hKnorm : K ≤ normalizer (H : Set Ω)) :
    ((H.subgroupOf G).subgroupOf (K.subgroupOf G)).Normal := by
  have hle : H.subgroupOf G ≤ K.subgroupOf G := Subgroup.subgroupOf_mono G hHK
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hKnorm (Subgroup.mem_subgroupOf.mp hk)) (x : Ω)

theorem exists_isSubnormal_minimal [Finite Ω] {G X T : Subgroup Ω} (hXG : X ≤ G)
    (hTG : T ≤ normalizer (G : Set Ω)) :
    ∃ L : Subgroup Ω, X ≤ L ∧ L ≤ G ∧ (L.subgroupOf G).IsSubnormal ∧
      T ≤ normalizer (L : Set Ω) ∧
      ∀ N : Subgroup Ω, L ⊔ T ≤ normalizer (N : Set Ω) → X ≤ N → L ≤ N := by
  classical
  have key : ∀ n : ℕ, ∀ M : Subgroup Ω, Nat.card M = n → X ≤ M → M ≤ G →
      (M.subgroupOf G).IsSubnormal → T ≤ normalizer (M : Set Ω) →
      ∃ L : Subgroup Ω, X ≤ L ∧ L ≤ G ∧ (L.subgroupOf G).IsSubnormal ∧
        T ≤ normalizer (L : Set Ω) ∧
        ∀ N : Subgroup Ω, L ⊔ T ≤ normalizer (N : Set Ω) → X ≤ N → L ≤ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro M hcard hXM hMG hMsn hTM
      let S : Set (Subgroup Ω) := {N | X ≤ N ∧ M ⊔ T ≤ normalizer (N : Set Ω)}
      let M' : Subgroup Ω := sInf S
      have hM_mem : M ∈ S := ⟨hXM, sup_le M.le_normalizer hTM⟩
      have hM'M : M' ≤ M := sInf_le hM_mem
      have hXM' : X ≤ M' := fun x hx => Subgroup.mem_sInf.mpr fun N hN => hN.1 hx
      have hM'T : M ⊔ T ≤ normalizer (M' : Set Ω) :=
        snm_sInf_le_normalizer (S := S) fun N hN => hN.2
      by_cases hEq : M' = M
      · refine ⟨M, hXM, hMG, hMsn, hTM, fun N hN hXN => ?_⟩
        rw [← hEq]
        exact sInf_le (show N ∈ S from ⟨hXN, hN⟩)
      · have hlt : M' < M := lt_of_le_of_ne hM'M hEq
        have hM'sn : (M'.subgroupOf G).IsSubnormal := by
          have hle : M'.subgroupOf G ≤ M.subgroupOf G := Subgroup.subgroupOf_mono G hM'M
          have hN : ((M'.subgroupOf G).subgroupOf (M.subgroupOf G)).Normal :=
            snm_normal_subgroupOf_subgroupOf hM'M (le_sup_left.trans hM'T)
          exact Subgroup.IsSubnormal.trans hle hN.isSubnormal hMsn
        have hM'G : M' ≤ G := hM'M.trans hMG
        have hTM' : T ≤ normalizer (M' : Set Ω) := le_sup_right.trans hM'T
        exact ih (Nat.card M') (hcard ▸ Subgroup.card_lt_of_lt hlt) M' rfl hXM' hM'G hM'sn hTM'
  exact key (Nat.card G) G rfl hXG le_rfl (by simp) hTG

end CFSG.GroupTheory
