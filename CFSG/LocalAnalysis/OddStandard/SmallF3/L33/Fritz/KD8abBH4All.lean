module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH41
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH42
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH43
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH44
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH45
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH46
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH47
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBH48

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8
open CFSG.ComponentClassification.HSFLit.Sec8

namespace MB
open CFSG.ComponentClassification.HSFLit.Sec8.MB

@[expose] def H4Zof : ℕ × ℕ → List ((MB × Bool × Bool) × List MB)
  | (0, 2) => H4Z1
  | (0, 10) => H4Z2
  | (1, 0) => H4Z3
  | (1, 8) => H4Z4
  | (2, 2) => H4Z5
  | (2, 10) => H4Z6
  | (3, 0) => H4Z7
  | (3, 8) => H4Z8
  | _ => []

theorem H4Z_eq_of : ∀ p ∈ goodIdx, H4Z p = H4Zof p := by
  intro p hp
  simp only [goodIdx, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [H4Z1_eq, H4Z2_eq, H4Z3_eq, H4Z4_eq, H4Z5_eq, H4Z6_eq, H4Z7_eq, H4Z8_eq]

theorem mem_H4Zof {p : ℕ × ℕ} (hp : p ∈ goodIdx) {τ : MB × Bool × Bool} (hτ : τ ∈ H4T) :
    (τ, H4elt p τ.1 τ.2.1 τ.2.2) ∈ H4Zof p := H4Z_eq_of p hp ▸ mem_H4Z p hτ

end MB

end Sec8

end CFSG.OddStandard.SmallF3.L33.KD
