module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2DataE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def supp (v : Fin 7 → ZMod 2) : List (Fin 7) := (List.finRange 7).filter fun i => v i = 1

@[expose] def pairUp : List (Fin 7) → List (Fin 7 × Fin 7)
  | x :: y :: t => (x, y) :: pairUp t
  | _ => []

theorem decomp_ok : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
    ((pairUp (supp v)).map fun q => ofVec (vecOf [q.1, q.2])).prod = ofVec v ∧
      ∀ q ∈ pairUp (supp v), ∃ t ∈ pairWords, t.1 = q.1 ∧ t.2.1 = q.2 := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
