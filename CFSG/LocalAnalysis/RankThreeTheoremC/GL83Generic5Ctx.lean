module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

structure Gen5Global (G : Type) [Group G] [Finite G] : Prop where
  setting : Setting G
  d1 : TheoremD1 G
  d2 : TheoremD2 G
  u0 : FullCoreLocal G
  layer : GL83GenericLayer G

structure Gen5Local (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x : G) : Prop where
  sigma : p ∈ rankThreeSigmaA G
  core : IsCoreMaxLocal p P M
  fail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M
  larger : LargerPrimesUnique G p
  generic : IsGenericPoint p P M x

@[expose] def gen5L {G : Type} [Group G] [Finite G] (x : G) : Subgroup G :=
  rankThreeLayer (centralizer ({x} : Set G))

@[expose] def gen5U {G : Type} [Group G] [Finite G] (P : Subgroup G) (x : G) : Subgroup G :=
  P ⊓ gen5L x

end CFSG.LocalAnalysis.RankThreeTheoremC
