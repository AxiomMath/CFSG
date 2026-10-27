module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QFC
public import Certificates.Data.Solomon75Sec5QInputs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.OddStandard.Solomon75.AhatData
  Certificates.Solomon75Sec5Q

open scoped commutatorElement

theorem rep_sigA (n : ℕ) [NeZero n] (hn : 8 ≤ n) : Rep n (sigA n) (sig0 n) := by
  refine rep_swapsA [(0, 1), (2, 3), (4, 5), (6, 7)] ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> omega

end CFSG.OddStandard.Solomon75
