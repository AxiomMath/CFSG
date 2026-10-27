module

public import CFSG.GH74.Generic.BProg.B2.GenLocG2
public import CFSG.GH74.Generic.BProg.B2.PuG2OddAux

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

section Main


theorem puG2Odd_of_shape {N : Type} [Group N] [Finite N] (H : Subgroup N) (t : N)
    (L : Subgroup N) (hs : ShapeInCent H t L) (hJ : PuG2 ↥H) : PuG2Odd ↥H := by
  obtain ⟨f, hf2, hmodel⟩ := hJ
  rcases Nat.even_or_odd f with hfe | hfo
  · exfalso
    exact PumpupTableExc.pumpupIn_g2 3 f Nat.prime_three (by norm_num) (by omega) N H t L hs
      (PuG2OddAux.mem_of_shape_g2_three_even hs (by omega) hfe hmodel) hmodel
  · refine ⟨f, ?_, hfo, hmodel⟩
    obtain ⟨m, hm⟩ := hfo
    omega

end Main

end CFSG.GH74.Generic.BProg.B2
