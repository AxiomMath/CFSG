module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBT2Data

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8
open CFSG.ComponentClassification.HSFLit.Sec8

namespace MB
open CFSG.ComponentClassification.HSFLit.Sec8.MB

@[expose] def H4Z (p : ℕ × ℕ) : List ((MB × Bool × Bool) × List MB) :=
  H4T.map fun τ => (τ, H4elt p τ.1 τ.2.1 τ.2.2)

theorem mem_H4Z (p : ℕ × ℕ) {τ : MB × Bool × Bool} (hτ : τ ∈ H4T) :
    (τ, H4elt p τ.1 τ.2.1 τ.2.2) ∈ H4Z p :=
  List.mem_map_of_mem hτ

end MB

end Sec8

end CFSG.OddStandard.SmallF3.L33.KD
