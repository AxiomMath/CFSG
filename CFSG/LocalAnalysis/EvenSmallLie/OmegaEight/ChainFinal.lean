module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainModule
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainAbel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainInvFix

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Stage1

variable {G : Type*} [Group G] {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G} {u : Fin 6 → G}

theorem l9_of_levelTwoKill [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x) (hS : Setup ε t L U Q P a ψ p)
    (hu : UData ε U Q ψ u) (hL2 : LevelTwoKill t Q P) : L9 t Q :=
  l9_of hG hnab hS (endF2 ε) (homEndZero hS.rad) (homEndModZero ε) (invFix hS) (hu.abelBound hS)
    hL2

end CFSG.EvenSmallLie.OmegaEight.Chain
