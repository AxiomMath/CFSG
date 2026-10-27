module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsChecks
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsPass

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier

private theorem natCard_subtype_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (p : G → Prop) :
    Nat.card {x : H // p (x : G)} = Nat.card {x : K // p (x : G) ∧ (x : G) ∈ H} := by
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨⟨x.1.1, h x.1.2⟩, x.2, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2.2⟩, y.2.1⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }

private theorem outerInvB_eq_true_iff
    (g : Equiv.Perm (Fin 26)) :
    outerInvB g = true ↔ g ^ 2 = 1 ∧ g ∉ QP.originalSubgroup := by
  rw [outerInvB, Bool.and_eq_true_iff, sqOneB_iff g, Bool.not_eq_true',
    ← Bool.eq_false_eq_not_eq_true, ← mem_iff_sift QP QP_ok g]

private theorem innerInvB_eq_true_iff
    (g : Equiv.Perm (Fin 26)) :
    innerInvB g = true ↔ (g ^ 2 = 1 ∧ g ≠ 1) ∧ g ∈ QP.originalSubgroup := by
  rw [innerInvB, Bool.and_eq_true_iff, Bool.and_eq_true_iff, sqOneB_iff g, Bool.not_eq_true',
    ← Bool.eq_false_eq_not_eq_true, isOneB_iff g, ← mem_iff_sift QP QP_ok g]

private theorem centB_eq_true_iff (g : Equiv.Perm (Fin 26)) :
    centB g = true ↔ g * modelK = modelK * g := by
  rw [centB, commB_iff, kTab_eq]

private theorem centPB_eq_true_iff
    (g : Equiv.Perm (Fin 26)) :
    centPB g = true ↔ (g * modelK = modelK * g) ∧ g ∈ QP.originalSubgroup := by
  simp only [centPB, Bool.and_eq_true_iff, commB_iff, kTab_eq, mem_iff_sift QP QP_ok g]

theorem card_model_inner_involutions :
    Nat.card {g : QP.originalSubgroup //
      (g : Equiv.Perm (Fin 26)) ^ 2 = 1 ∧ (g : Equiv.Perm (Fin 26)) ≠ 1} = 117 := by
  classical
  rw [natCard_subtype_le model_P_le_A (fun g : Equiv.Perm (Fin 26) => g ^ 2 = 1 ∧ g ≠ 1)]
  rw [card_filter QA QA_ok
    (fun g : Equiv.Perm (Fin 26) => (g ^ 2 = 1 ∧ g ≠ 1) ∧ g ∈ QP.originalSubgroup)]
  rw [← List.countP_eq_length_filter]
  trans (elemsT QA).countP innerInvB
  · apply List.countP_congr
    intro g _
    rw [decide_eq_true_iff]
    exact (innerInvB_eq_true_iff g).symm
  · exact countP_inner_total

theorem card_model_outer_involutions :
    Nat.card {g : QA.originalSubgroup //
      (g : Equiv.Perm (Fin 26)) ^ 2 = 1 ∧ (g : Equiv.Perm (Fin 26)) ∉ QP.originalSubgroup} =
      234 := by
  classical
  rw [card_filter QA QA_ok
    (fun g : Equiv.Perm (Fin 26) => g ^ 2 = 1 ∧ g ∉ QP.originalSubgroup)]
  rw [← List.countP_eq_length_filter]
  trans (elemsT QA).countP outerInvB
  · apply List.countP_congr
    intro g _
    rw [decide_eq_true_iff]
    exact (outerInvB_eq_true_iff g).symm
  · exact countP_outer_total

theorem card_model_centralizer_k :
    Nat.card {g : QA.originalSubgroup //
      (g : Equiv.Perm (Fin 26)) * modelK = modelK * (g : Equiv.Perm (Fin 26))} = 48 := by
  classical
  rw [card_filter QA QA_ok (fun g : Equiv.Perm (Fin 26) => g * modelK = modelK * g)]
  rw [← List.countP_eq_length_filter]
  trans (elemsT QA).countP centB
  · apply List.countP_congr
    intro g _
    rw [decide_eq_true_iff]
    exact (centB_eq_true_iff g).symm
  · exact countP_cent_total

theorem card_model_centralizer_k_inner :
    Nat.card {g : QP.originalSubgroup //
      (g : Equiv.Perm (Fin 26)) * modelK = modelK * (g : Equiv.Perm (Fin 26))} = 24 := by
  classical
  rw [natCard_subtype_le model_P_le_A
    (fun g : Equiv.Perm (Fin 26) => g * modelK = modelK * g)]
  rw [card_filter QA QA_ok
    (fun g : Equiv.Perm (Fin 26) => (g * modelK = modelK * g) ∧ g ∈ QP.originalSubgroup)]
  rw [← List.countP_eq_length_filter]
  trans (elemsT QA).countP centPB
  · apply List.countP_congr
    intro g _
    rw [decide_eq_true_iff]
    exact (centPB_eq_true_iff g).symm
  · exact countP_centP_total

end CFSG.OddStandard.SmallF3.L33
