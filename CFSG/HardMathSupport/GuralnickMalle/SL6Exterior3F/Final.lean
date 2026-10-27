module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Assembly
public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.InvolutionRank

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.Open

theorem sl6Exterior3_mul_weight1Gen_lt (K : Type) [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : m < Nat.card K)
    (A : Subgroup ↥(StatedSL 6 K)) (hA : A ≠ ⊥) (hAel : IsElementaryAbelian 2 ↥A) :
    m * weight1Gen (sl6Exterior3Rep K) A < Nat.card (⋀[K]^3 (Fin 6 → K)) :=
  sl6Exterior3_mul_weight1Gen_lt_of_inv (finrank_fixSubGen_closure_add_two_mul_natRank_le K) hm
    A hA hAel

end CFSG.HardMathSupport.GuralnickMalle
