module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec510Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r ρ : G)
    (B A : Subgroup G) (φ : (Fin 6 → ZMod 2) → G) : Prop extends Sec5RCtx G t L S z r B A where
  syl : IsSylow2Of S (⊤ : Subgroup G)
  model : Sec5Model58 t L z ρ A φ
  nconj : ¬ ∃ h : G, h⁻¹ * t * h = t * z
  delta : conjClassIn (normalizer (A : Set G)) t = wclass φ 6 ∪ wclass φ 1
  tnz : ∀ g : G, g⁻¹ * z * g ≠ t
  zM : conjClassIn (normalizer (A : Set G)) z = wclass φ 3 ∪ wclass φ 4

end CFSG.OddStandard.SmallF3.Omega
