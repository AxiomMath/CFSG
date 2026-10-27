module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def sec124Sigma : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

theorem sec124Sigma_mem : sec124Sigma ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold sec124Sigma
  decide

theorem permVec_sec124Sigma_twice (v : Fin 5 → ZMod 2) :
    permVec sec124Sigma (permVec sec124Sigma v) = v := by
  revert v
  unfold permVec sec124Sigma
  decide +kernel

theorem sec124_vectors : ∃ n₁ n₂ : Fin 5 → ZMod 2, IsEvenVec n₁ ∧ IsEvenVec n₂ ∧
    n₁ + permVec sec124Sigma n₁ ≠ 0 ∧ n₂ + permVec sec124Sigma n₂ ≠ 0 ∧
    n₁ + permVec sec124Sigma n₁ ≠ n₂ + permVec sec124Sigma n₂ ∧ permVec sec124Sigma n₁ ≠ n₁ := by
  refine ⟨![1, 0, 0, 0, 1], ![0, 0, 1, 0, 1], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (unfold IsEvenVec; decide +kernel)
    | (unfold permVec sec124Sigma; decide +kernel)

end CFSG.OddStandard.SmallF3.Omega
