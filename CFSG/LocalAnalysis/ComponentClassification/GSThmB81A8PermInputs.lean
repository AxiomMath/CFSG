module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.CatFactsSmall.A8

local notation "P8" => Equiv.Perm (Fin 8)

@[expose] def n3Data : List (P8 × P8 × P8 × P8) := [
  (s8 * List.formPerm [2, 3], List.formPerm [5, 6, 7],
    List.formPerm [4, 5] * List.formPerm [6, 7], List.formPerm [4, 6] * List.formPerm [5, 7]),
  (s8 * List.formPerm [2, 4], List.formPerm [5, 6, 7],
    List.formPerm [3, 5] * List.formPerm [6, 7], List.formPerm [3, 6] * List.formPerm [5, 7]),
  (s8 * List.formPerm [2, 5], List.formPerm [4, 6, 7],
    List.formPerm [3, 4] * List.formPerm [6, 7], List.formPerm [3, 6] * List.formPerm [4, 7]),
  (s8 * List.formPerm [2, 6], List.formPerm [4, 5, 7],
    List.formPerm [3, 4] * List.formPerm [5, 7], List.formPerm [3, 5] * List.formPerm [4, 7]),
  (s8 * List.formPerm [2, 7], List.formPerm [4, 5, 6],
    List.formPerm [3, 4] * List.formPerm [5, 6], List.formPerm [3, 5] * List.formPerm [4, 6]),
  (s8 * List.formPerm [3, 4], List.formPerm [5, 6, 7],
    List.formPerm [2, 5] * List.formPerm [6, 7], List.formPerm [2, 6] * List.formPerm [5, 7]),
  (s8 * List.formPerm [3, 5], List.formPerm [4, 6, 7],
    List.formPerm [2, 4] * List.formPerm [6, 7], List.formPerm [2, 6] * List.formPerm [4, 7]),
  (s8 * List.formPerm [3, 6], List.formPerm [4, 5, 7],
    List.formPerm [2, 4] * List.formPerm [5, 7], List.formPerm [2, 5] * List.formPerm [4, 7]),
  (s8 * List.formPerm [3, 7], List.formPerm [4, 5, 6],
    List.formPerm [2, 4] * List.formPerm [5, 6], List.formPerm [2, 5] * List.formPerm [4, 6]),
  (s8 * List.formPerm [4, 5], List.formPerm [3, 6, 7],
    List.formPerm [2, 3] * List.formPerm [6, 7], List.formPerm [2, 6] * List.formPerm [3, 7]),
  (s8 * List.formPerm [4, 6], List.formPerm [3, 5, 7],
    List.formPerm [2, 3] * List.formPerm [5, 7], List.formPerm [2, 5] * List.formPerm [3, 7]),
  (s8 * List.formPerm [4, 7], List.formPerm [3, 5, 6],
    List.formPerm [2, 3] * List.formPerm [5, 6], List.formPerm [2, 5] * List.formPerm [3, 6]),
  (s8 * List.formPerm [5, 6], List.formPerm [3, 4, 7],
    List.formPerm [2, 3] * List.formPerm [4, 7], List.formPerm [2, 4] * List.formPerm [3, 7]),
  (s8 * List.formPerm [5, 7], List.formPerm [3, 4, 6],
    List.formPerm [2, 3] * List.formPerm [4, 6], List.formPerm [2, 4] * List.formPerm [3, 6]),
  (s8 * List.formPerm [6, 7], List.formPerm [3, 4, 5],
    List.formPerm [2, 3] * List.formPerm [4, 5], List.formPerm [2, 4] * List.formPerm [3, 5])]

@[expose] def t15 : List P8 := n3Data.map fun x => x.1

@[expose, noinline] def tauCheck (LA T : List P8) : Bool :=
  LA.all fun γ => !(decide (s8 * (γ⁻¹ * s8 * γ) * (s8 * (γ⁻¹ * s8 * γ)) = 1)) ||
    decide (s8 * (γ⁻¹ * s8 * γ) = 1) || T.any fun u => decide (u = s8 * (γ⁻¹ * s8 * γ))

@[expose] def four (e₁ e₂ : P8) : List P8 := [1, e₁, e₂, e₁ * e₂]

@[expose, noinline] def n3Check (LL : List P8) (QL : RawSchreierDatum 8)
    (N : List (P8 × P8 × P8 × P8)) : Bool :=
  N.all fun x =>
    QL.sift x.2.1 0 && QL.sift x.2.2.1 0 && QL.sift x.2.2.2 0 &&
    decide (x.2.1 * x.1 = x.1 * x.2.1) && decide (x.2.2.1 * x.1 = x.1 * x.2.2.1) &&
    decide (x.2.2.2 * x.1 = x.1 * x.2.2.2) &&
    decide (x.2.1 * x.2.2.1 * x.2.1⁻¹ = x.2.2.2) &&
    decide (x.2.1 * x.2.2.2 * x.2.1⁻¹ = x.2.2.1 * x.2.2.2) &&
    decide (x.2.2.1 * x.2.2.1 = 1) && decide (x.2.2.2 * x.2.2.2 = 1) &&
    decide (x.2.2.1 * x.2.2.2 = x.2.2.2 * x.2.2.1) && !decide (x.2.2.1 = 1) &&
    !decide (x.2.2.2 = 1) && !decide (x.2.2.1 = x.2.2.2) &&
    decide ((LL.filter fun c => decide (c * x.1 = x.1 * c)).length = 24) &&
    LL.all fun c => !decide (c * x.1 = x.1 * c) ||
      ((four x.2.2.1 x.2.2.2).any fun u => decide (c * x.2.2.1 * c⁻¹ = u)) &&
        ((four x.2.2.1 x.2.2.2).any fun u => decide (c * x.2.2.2 * c⁻¹ = u))

@[expose, noinline] def n4Check (LS LA T : List P8) : Bool :=
  (LS.filter fun p => (T.any fun t => decide (p * p = t)) && decide (s8 * p * s8 = p⁻¹)).all
    fun p => ((LS.filter fun θ => decide (θ * s8 = s8 * θ) && !decide (θ = 1) &&
        decide (θ ^ 315 = 1)).all fun θ => !decide (θ * p = p * θ)) ||
      LA.any fun π => decide (π * (p * p) * π⁻¹ = p * s8)

end CFSG.ComponentClassification.GSThmB.A8
