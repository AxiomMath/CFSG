module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListChains

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

@[expose] def twistedE6PosRoots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [(![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ), (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)]

@[expose] def e6RootA2 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)
@[expose] def e6RootA24 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)
@[expose] def e6RootA234 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ)
@[expose] def e6RootA245 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)
@[expose] def e6RootA2345 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)
@[expose] def e6RootD4High : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ)

@[expose] def twistedE6FrameReps : List (List (Fin TwistTag.E6.tag.rank → ℤ)) :=
  [[e6HighestRoot], [twistedE6ClassRootU, twistedE6ClassRootU'], [e6HighestRoot, e6CascR17],
    [twistedE6ClassRootA, twistedE6ClassRootA', twistedE6ClassRootB],
    [e6HighestRoot, e6CascR17, e6CascC],
    [e6RootA2, e6RootA3, e6RootA5, e6RootD4High],
    [e6HighestRoot, e6CascR17, e6CascC, e6RootA4]]

@[expose] def twistedE6FrameTable :
    List (List (Fin TwistTag.E6.tag.rank → ℤ) × List (Fin TwistTag.E6.foldedTag.rank) × ℕ) :=
  [([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)], ([] : List (Fin 4)), 0),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ)], ([3] : List (Fin 4)), 0),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ)], ([3, 2] : List (Fin 4)), 0),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ)], ([] : List (Fin 4)), 1),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ)], ([3, 2, 1] : List (Fin 4)), 0),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ)], ([3, 2] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ)], ([0] : List (Fin 4)), 1),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ)], ([1] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([3, 2, 1, 2] : List (Fin 4)), 0),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([3] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ)], ([0, 1] : List (Fin 4)), 1),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ)], ([] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1] : List (Fin 4)), 3),
  ([(![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([3, 2, 1, 2, 3] : List (Fin 4)), 0),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 3] : List (Fin 4)), 3),
  ([(![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ)], ([3, 2, 1, 0] : List (Fin 4)), 0),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ)], ([0, 3, 2] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ)], ([1, 0] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ)], ([0, 3, 2, 1] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ)], ([3, 2] : List (Fin 4)), 4),
  ([(![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2] : List (Fin 4)), 1),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ)], ([0, 2, 1, 2, 3] : List (Fin 4)), 5),
  ([(![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)], ([3, 2, 1, 0, 2] : List (Fin 4)), 0),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)], ([0, 3] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)], ([1, 0, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)], ([0, 3, 2, 1, 2] : List (Fin 4)), 2),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)], ([3] : List (Fin 4)), 4),
  ([(![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3, 2, 3] : List (Fin 4)), 5),
  ([(![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1] : List (Fin 4)), 1),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)], ([2, 1] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)], ([2, 1, 2] : List (Fin 4)), 3),
  ([(![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1] : List (Fin 4)), 3),
  ([(![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1, 2, 3] : List (Fin 4)), 5),
  ([(![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3, 2, 3] : List (Fin 4)), 5),
  ([(![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 3] : List (Fin 4)), 1),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 3] : List (Fin 4)), 3),
  ([(![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([0, 2, 1, 2] : List (Fin 4)), 5),
  ([(![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 3, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ)], ([0, 2, 1] : List (Fin 4)), 5),
  ([(![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0] : List (Fin 4)), 1),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 2, 1] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0, 2, 3] : List (Fin 4)), 5),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 2, 1, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0, 3, 2, 3] : List (Fin 4)), 5),
  ([(![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([3, 2, 1, 0, 2, 3] : List (Fin 4)), 0),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([0] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([1, 0, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 3] : List (Fin 4)), 3),
  ([(![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([0, 3, 2, 1, 2, 3] : List (Fin 4)), 2),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([] : List (Fin 4)), 4),
  ([(![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3, 2] : List (Fin 4)), 5),
  ([(![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 3, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3] : List (Fin 4)), 5),
  ([(![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1, 0] : List (Fin 4)), 3),
  ([(![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3] : List (Fin 4)), 1),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ)], ([2, 1, 3] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ)], ([2, 1, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1, 3] : List (Fin 4)), 3),
  ([(![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1, 3] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1, 2] : List (Fin 4)), 5),
  ([(![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1, 2, 3] : List (Fin 4)), 3),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3, 2] : List (Fin 4)), 5),
  ([(![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([3, 2, 1, 0, 2, 1] : List (Fin 4)), 0),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 1, 3] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 0, 2, 1] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 1] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 1, 3, 2, 1, 2] : List (Fin 4)), 2),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 3] : List (Fin 4)), 4),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3, 2, 1, 3] : List (Fin 4)), 5),
  ([(![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 1, 2, 1, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3, 2, 1, 3] : List (Fin 4)), 5),
  ([(![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 1, 3, 2, 1, 0, 2] : List (Fin 4)), 2),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 0, 3] : List (Fin 4)), 4),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3, 2, 1, 0, 3] : List (Fin 4)), 5),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 0, 3, 2, 1, 2] : List (Fin 4)), 4),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([3] : List (Fin 4)), 6),
  ([(![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 3, 2, 1, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 2] : List (Fin 4)), 5),
  ([(![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0, 3] : List (Fin 4)), 1),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 3] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 2, 1, 3] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0, 2] : List (Fin 4)), 5),
  ([(![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 2, 1, 2, 3] : List (Fin 4)), 3),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0, 3, 2] : List (Fin 4)), 5),
  ([(![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1, 0, 3] : List (Fin 4)), 3),
  ([(![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1, 0, 1, 3] : List (Fin 4)), 3),
  ([(![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)], ([2] : List (Fin 4)), 5),
  ([(![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3, 2] : List (Fin 4)), 1),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ)], ([2, 1, 3, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ)], ([2, 1, 3, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1, 3, 2] : List (Fin 4)), 3),
  ([(![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1, 3, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1] : List (Fin 4)), 5),
  ([(![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1, 3, 2, 3] : List (Fin 4)), 3),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3] : List (Fin 4)), 5),
  ([(![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([3, 2, 1, 0, 2, 1, 2] : List (Fin 4)), 0),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([0, 1, 3, 2] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([1, 0, 2, 1, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([0, 1, 3, 2, 1] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([1, 3, 2] : List (Fin 4)), 4),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 1, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3, 2, 1, 3, 2] : List (Fin 4)), 5),
  ([(![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 1, 2, 1] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3, 2, 1, 3, 2] : List (Fin 4)), 5),
  ([(![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([0, 1, 3, 2, 1, 0] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([1, 0, 3, 2] : List (Fin 4)), 4),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3, 2, 1, 0, 3, 2] : List (Fin 4)), 5),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([1, 0, 3, 2, 1] : List (Fin 4)), 4),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([3, 2] : List (Fin 4)), 6),
  ([(![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 3, 2, 1, 3, 2] : List (Fin 4)), 3),
  ([(![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ), (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 1] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)], ([0] : List (Fin 4)), 5),
  ([(![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([3, 2, 1, 0, 2, 1, 3] : List (Fin 4)), 0),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 1] : List (Fin 4)), 2),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 0, 2, 1, 3] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 1, 3] : List (Fin 4)), 3),
  ([(![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 1, 3, 2, 1, 2, 3] : List (Fin 4)), 2),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1] : List (Fin 4)), 4),
  ([(![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3, 2, 1] : List (Fin 4)), 5),
  ([(![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 3, 2, 1] : List (Fin 4)), 3),
  ([(![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 2, 3] : List (Fin 4)), 5),
  ([(![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 0, 1, 2, 1, 2, 3] : List (Fin 4)), 3),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3, 2, 1] : List (Fin 4)), 5),
  ([(![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1, 0, 1] : List (Fin 4)), 3),
  ([(![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 1, 3, 2, 1, 0, 2, 3] : List (Fin 4)), 2),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 0] : List (Fin 4)), 4),
  ([(![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([0, 2, 1, 3, 2, 1, 0] : List (Fin 4)), 5),
  ([(![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([1, 0, 3, 2, 1, 2, 3] : List (Fin 4)), 4),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([] : List (Fin 4)), 6),
  ([(![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)], ([2, 3] : List (Fin 4)), 5),
  ([(![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0, 3, 2] : List (Fin 4)), 1),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 3, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 3, 2, 3] : List (Fin 4)), 3),
  ([(![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 2, 1, 3, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0] : List (Fin 4)), 5),
  ([(![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([2, 1, 0, 2, 1, 3, 2, 3] : List (Fin 4)), 3),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([0, 1, 2, 1, 0, 3] : List (Fin 4)), 5),
  ([(![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1, 0, 3, 2] : List (Fin 4)), 3),
  ([(![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([1, 2, 1, 3, 2, 1, 0, 1, 3, 2] : List (Fin 4)), 3),
  ([(![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)], ([] : List (Fin 4)), 5),
  ([(![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([0, 1, 2, 1, 3, 2, 1] : List (Fin 4)), 1),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([2, 1, 3, 2, 1] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([2, 1, 3, 2, 1, 3] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([2, 1, 3, 2, 1, 3, 2] : List (Fin 4)), 3),
  ([(![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ), (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1, 3, 2, 1] : List (Fin 4)), 3),
  ([(![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ), (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([0, 1, 2] : List (Fin 4)), 5),
  ([(![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1, 3, 2, 1, 2] : List (Fin 4)), 3),
  ([(![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([0, 1] : List (Fin 4)), 5),
  ([(![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([1, 2, 1, 0, 2, 1, 3, 2, 1, 3] : List (Fin 4)), 3),
  ([(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ), (![0, 0, 0, 0, 0, 1] : Fin 6 → ℤ)], ([0, 1, 2, 3] : List (Fin 4)), 5)]

@[expose] def twistedE6FrameLeafB (F : List (Fin TwistTag.E6.tag.rank → ℤ)) : Bool :=
  F.isEmpty || !(F.all fun γ => F.contains (permLattice TwistTag.E6.perm γ)) ||
    twistedE6FrameTable.any fun e => e.1.isPerm F

@[expose] def twistedE6FrameSearch (acc : List (Fin TwistTag.E6.tag.rank → ℤ)) :
    List (Fin TwistTag.E6.tag.rank → ℤ) → Bool
  | [] => twistedE6FrameLeafB acc
  | γ :: rest => twistedE6FrameSearch acc rest &&
      (!(acc.all fun δ => iform γ δ == 0) || twistedE6FrameSearch (γ :: acc) rest)

theorem twistedE6FrameSearch_check : twistedE6FrameSearch [] twistedE6PosRoots = true := by
  decide +kernel

theorem twistedE6FrameTable_check : ∀ e ∈ twistedE6FrameTable, e.2.2 < 7 ∧
    (e.1.map (twistedE6RelAct e.2.1)).isPerm (twistedE6FrameReps.getD e.2.2 []) = true := by
  decide +kernel

theorem twistedE6FrameSearch_sound :
    ∀ (rest acc : List (Fin TwistTag.E6.tag.rank → ℤ)),
    twistedE6FrameSearch acc rest = true → ∀ S : List (Fin TwistTag.E6.tag.rank → ℤ),
      S.Sublist rest → (∀ γ ∈ S, ∀ δ ∈ acc, iform γ δ = 0) →
        S.Pairwise (fun γ δ => iform γ δ = 0) → twistedE6FrameLeafB (S.reverse ++ acc) = true := by
  intro rest
  induction rest with
  | nil =>
    intro acc h S hS _ _
    rw [List.sublist_nil.1 hS]
    exact h
  | cons γ rest ih =>
    intro acc h S hS hacc hpw
    simp only [twistedE6FrameSearch, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases List.sublist_cons_iff.1 hS with hS' | ⟨S', rfl, hS'⟩
    · exact ih acc h.1 S hS' hacc hpw
    · have hall : (acc.all fun δ => iform γ δ == 0) = true := by
        rw [List.all_eq_true]
        intro δ hδ
        rw [beq_iff_eq]
        exact hacc γ List.mem_cons_self δ hδ
      have h2 : twistedE6FrameSearch (γ :: acc) rest = true := by
        rcases h.2 with h' | h'
        · rw [hall] at h'
          exact absurd h' (by decide)
        · exact h'
      obtain ⟨hγS', hS'pw⟩ := List.pairwise_cons.1 hpw
      have := ih (γ :: acc) h2 S' hS' (fun x hx δ hδ => by
        rcases List.mem_cons.1 hδ with rfl | hδ
        · rw [iform_comm]
          exact hγS' x hx
        · exact hacc x (List.mem_cons_of_mem _ hx) δ hδ) hS'pw
      rw [List.reverse_cons, List.append_assoc, List.singleton_append]
      exact this

theorem mem_twistedE6PosRoots {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ) : γ ∈ twistedE6PosRoots := by
  rw [isRoot_iff_twistedE6TwoRootB] at hγ
  simp only [twistedE6TwoRootB, List.any_eq_true, List.mem_range, twistedE6TwoVecB_iff] at hγ
  obtain ⟨k, hk, rfl⟩ := hγ
  have h : ∀ k ∈ List.range TwistTag.E6.tag.rootCertificate.roots.length,
      0 < height (TwistTag.E6.tag.rootCertificate.root k) →
        TwistTag.E6.tag.rootCertificate.root k ∈ twistedE6PosRoots := by
    decide +kernel
  exact h k (List.mem_range.2 hk) hpos


theorem twistedE6_d4Frame_conj [CharP K 2] :
    (pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
        pinnedX TwistTag.E6.tag K e6RootA24 1 *
          pinnedX TwistTag.E6.tag K e6CascC 1) *
      (pinnedX TwistTag.E6.tag K e6RootA2 1 *
        pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1 *
          pinnedX TwistTag.E6.tag K e6RootD4High 1) *
      (pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
        pinnedX TwistTag.E6.tag K e6RootA24 1 *
          pinnedX TwistTag.E6.tag K e6CascC 1)⁻¹ =
      pinnedX TwistTag.E6.tag K e6RootA2 1 *
        pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1 := by
  have cj : ∀ {α β γ : Fin TwistTag.E6.tag.rank → ℤ},
      (twistedE6TwoRootB α && twistedE6TwoRootB β && twistedE6TwoRootB γ &&
        !twistedE6TwoVecB α β && twistedE6TwoVecB (α + β) γ) = true →
      pinnedX TwistTag.E6.tag K α 1 * pinnedX TwistTag.E6.tag K β 1 *
          (pinnedX TwistTag.E6.tag K α 1)⁻¹ =
        pinnedX TwistTag.E6.tag K γ 1 * pinnedX TwistTag.E6.tag K β 1 := fun h => by
    rw [twistedE6_conj_pinnedX_add h, one_mul]
  have cm : ∀ {α β : Fin TwistTag.E6.tag.rank → ℤ},
      (twistedE6TwoRootB α && twistedE6TwoRootB β && !twistedE6TwoVecB α β &&
        !twistedE6TwoVecB (α + β) 0 && !twistedE6TwoRootB (α + β)) = true →
      Commute (pinnedX TwistTag.E6.tag K α 1) (pinnedX TwistTag.E6.tag K β 1) := fun h =>
    twistedE6_commute_pinnedX h 1 1
  exact d4_conj_identity (xa := pinnedX TwistTag.E6.tag K e6RootA2 1)
    (xb := pinnedX TwistTag.E6.tag K e6RootA3 1) (xd := pinnedX TwistTag.E6.tag K e6RootA5 1)
    (xac := pinnedX TwistTag.E6.tag K e6RootA24 1)
    (xbc := pinnedX TwistTag.E6.tag K e6RootA34 1) (xcd := pinnedX TwistTag.E6.tag K e6RootA45 1)
    (xabc := pinnedX TwistTag.E6.tag K e6RootA234 1)
    (xacd := pinnedX TwistTag.E6.tag K e6RootA245 1)
    (xbcd := pinnedX TwistTag.E6.tag K e6CascC 1)
    (xabcd := pinnedX TwistTag.E6.tag K e6RootA2345 1)
    (xθ := pinnedX TwistTag.E6.tag K e6RootD4High 1)
    (cj (by decide)) (cm (by decide)) (cm (by decide)) (cm (by decide)) (cm (by decide))
    (cm (by decide)) (cj (by decide)) (cj (by decide)) (cm (by decide)) (cm (by decide))
    (cj (by decide)) (cm (by decide)) (cm (by decide)) (cj (by decide)) (cj (by decide))
    (cm (by decide)) (cm (by decide)) (cj (by decide)) (cj (by decide)) (cm (by decide))
    (cm (by decide)) (cm (by decide)) (cm (by decide)) (cm (by decide)) (cm (by decide))
    (cm (by decide)) (cm (by decide)) (cj (by decide)) (cm (by decide)) (cm (by decide))
    (cm (by decide)) (cm (by decide)) (twistedE6_pinnedX_one_mul_self _)
    (twistedE6_pinnedX_one_mul_self _) (twistedE6_pinnedX_one_mul_self _)
    (twistedE6_pinnedX_one_mul_self _) (twistedE6_pinnedX_one_mul_self _)

@[expose] def twistedE6WordW5 : List (Fin TwistTag.E6.foldedTag.rank) :=
  ([1, 2, 1, 3, 2, 1, 0, 1, 3, 2] : List (Fin 4))

theorem exists_conj_twistedE6D4Frame_eq_twistedE6ClassV [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * (pinnedX TwistTag.E6.tag K e6RootA2 1 *
        pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1 *
          pinnedX TwistTag.E6.tag K e6RootD4High 1) * g⁻¹ =
        twistedE6ClassV K := by
  have hpair : pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
    have h := twistedE6PairX_mem_graphFixedRootGroup hσσ
      (isRoot_iff_twistedE6TwoRootB.2 (by decide : twistedE6TwoRootB e6RootA45 = true)) (1 : K)
    rwa [twistedE6PairX, show permLattice TwistTag.E6.perm e6RootA45 = e6RootA34 by decide,
      map_one] at h
  have k : ∀ {β : Fin TwistTag.E6.tag.rank → ℤ}, twistedE6TwoRootB β = true →
      permLattice TwistTag.E6.perm β = β →
      pinnedX TwistTag.E6.tag K β 1 ∈ graphFixedRootGroup TwistTag.E6 K σ := fun hβ hρ =>
    pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_iff_twistedE6TwoRootB.2 hβ) hρ (map_one σ)
  have hg : pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
        pinnedX TwistTag.E6.tag K e6RootA24 1 *
          pinnedX TwistTag.E6.tag K e6CascC 1 ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    mul_mem (mul_mem hpair (k (by decide) (by decide))) (k (by decide) (by decide))
  have hw : MulAut.conj (twistedE6RelWeyl K twistedE6WordW5)
      (pinnedX TwistTag.E6.tag K e6RootA2 1 *
        pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1) =
      twistedE6ClassV K := by
    rw [map_mul, map_mul, twistedE6RelWeyl_mulAutConj _ (by decide),
      twistedE6RelWeyl_mulAutConj _ (by decide), twistedE6RelWeyl_mulAutConj _ (by decide),
      show twistedE6RelAct twistedE6WordW5 e6RootA2 =
        twistedE6ClassRootB by decide,
      show twistedE6RelAct twistedE6WordW5 e6RootA3 = twistedE6ClassRootA' by decide,
      show twistedE6RelAct twistedE6WordW5 e6RootA5 = twistedE6ClassRootA by decide]
    have h1 : Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1)
        (pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 *
          pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1) :=
      (twistedE6_commute_pinnedX (by decide) 1 1).mul_right (twistedE6_commute_pinnedX (by decide) 1 1)
    have h2 : Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
        (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1) := twistedE6_commute_pinnedX (by decide) 1 1
    rw [twistedE6ClassV, mul_assoc, h1.eq, h2.eq]
  refine ⟨twistedE6RelWeyl K twistedE6WordW5 *
      (pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
        pinnedX TwistTag.E6.tag K e6RootA24 1 *
          pinnedX TwistTag.E6.tag K e6CascC 1), mul_mem (twistedE6RelWeyl_mem σ _) hg, ?_⟩
  rw [← MulAut.conj_apply, twistedE6_mulAutConj_mul, MulAut.conj_apply (_ * _ * _ * _),
    twistedE6_d4Frame_conj, hw]

theorem twistedE6FrameReps_commute {k : ℕ} {γ δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : γ ∈ twistedE6FrameReps.getD k []) (hδ : δ ∈ twistedE6FrameReps.getD k [])
    (hne : γ ≠ δ) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K γ c) (pinnedX TwistTag.E6.tag K δ d) := by
  have h : ∀ k ∈ List.range 7, ∀ γ ∈ twistedE6FrameReps.getD k [],
      ∀ δ ∈ twistedE6FrameReps.getD k [], γ ≠ δ →
        (twistedE6TwoRootB γ && twistedE6TwoRootB δ && !twistedE6TwoVecB γ δ &&
          !twistedE6TwoVecB (γ + δ) 0 && !twistedE6TwoRootB (γ + δ)) = true := by
    decide +kernel
  by_cases hk : k < 7
  · exact twistedE6_commute_pinnedX (h k (List.mem_range.2 hk) γ hγ δ hδ hne) c d
  · rw [List.getD_eq_default _ _ (by simp [twistedE6FrameReps]; omega)] at hγ
    exact absurd hγ List.not_mem_nil

theorem exists_conj_mem_twistedE6Reps_of_frameRep [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {δ : K} (hδ : δ + σ δ = 1) {k : ℕ} (hk : k < 7) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * ((twistedE6FrameReps.getD k []).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod *
          g⁻¹ = pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∨
        g * ((twistedE6FrameReps.getD k []).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod *
          g⁻¹ = twistedE6ClassU K ∨
        g * ((twistedE6FrameReps.getD k []).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod *
          g⁻¹ = twistedE6ClassV K := by
  have one : ∀ y : ModGL TwistTag.E6.tag K, (1 : ModGL TwistTag.E6.tag K) * y * 1⁻¹ = y :=
    fun y => by rw [one_mul, inv_one, mul_one]
  interval_cases k <;>
    simp only [twistedE6FrameReps, List.getD_cons_zero, List.getD_cons_succ, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  · exact ⟨1, one_mem _, Or.inl (one _)⟩
  · exact ⟨1, one_mem _, Or.inr (Or.inl (one _))⟩
  · obtain ⟨g, hg, he⟩ := exists_conj_y1_eq_twistedE6ClassU hσσ hδ
    exact ⟨g, hg, Or.inr (Or.inl he)⟩
  · refine ⟨1, one_mem _, Or.inr (Or.inr ?_)⟩
    rw [one _, twistedE6ClassV, mul_assoc]
  · obtain ⟨g, hg, he⟩ := exists_conj_y2_eq_twistedE6ClassV hσσ hδ
    refine ⟨g, hg, Or.inr (Or.inr ?_)⟩
    rw [← he, mul_assoc (pinnedX TwistTag.E6.tag K e6HighestRoot 1)]
  · obtain ⟨g, hg, he⟩ := exists_conj_twistedE6D4Frame_eq_twistedE6ClassV (K := K) hσσ
    refine ⟨g, hg, Or.inr (Or.inr ?_)⟩
    rw [← he]
    simp only [mul_assoc]
  · obtain ⟨g, hg, he⟩ := exists_conj_y3_eq_twistedE6ClassV hσσ hδ
    refine ⟨g, hg, Or.inr (Or.inr ?_)⟩
    rw [← he]
    simp only [mul_assoc]

theorem exists_conj_mem_twistedE6Reps_of_frame [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {δ : K} (hδ : δ + σ δ = 1)
    {F : List (Fin TwistTag.E6.tag.rank → ℤ)} (hnd : F.Nodup)
    (hF : ∀ γ ∈ F, IsRoot TwistTag.E6.tag γ ∧ 0 < height γ ∧ permLattice TwistTag.E6.perm γ ∈ F)
    (horth : F.Pairwise fun γ δ => iform γ δ = 0) (hF0 : F ≠ []) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * (F.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * g⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∨
        g * (F.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * g⁻¹ = twistedE6ClassU K ∨
          g * (F.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * g⁻¹ = twistedE6ClassV K := by
  classical
  set S := twistedE6PosRoots.filter (fun γ => decide (γ ∈ F)) with hSdef
  have hPnd : twistedE6PosRoots.Nodup := by decide +kernel
  have hSF : S.Perm F := (List.perm_ext_iff_of_nodup (hPnd.filter _) hnd).2 fun γ => by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨mem_twistedE6PosRoots (hF γ h).1 (hF γ h).2.1, h⟩⟩
  have hFsym : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → iform a b = 0 := by
    clear hnd hF hF0 hSF hSdef
    induction F with
    | nil => intro a ha; exact absurd ha List.not_mem_nil
    | cons x l ih =>
      obtain ⟨hx, hl⟩ := List.pairwise_cons.1 horth
      intro a ha b hb hab
      rcases List.mem_cons.1 ha with rfl | ha'
      · rcases List.mem_cons.1 hb with rfl | hb'
        · exact absurd rfl hab
        · exact hx b hb'
      · rcases List.mem_cons.1 hb with rfl | hb'
        · rw [iform_comm]
          exact hx a ha'
        · exact ih hl a ha' b hb' hab
  have hSpw : S.Pairwise fun γ δ => iform γ δ = 0 :=
    (hPnd.filter _).pairwise_of_forall_ne fun a ha b hb hab =>
      hFsym a (hSF.subset ha) b (hSF.subset hb) hab
  have hleaf := twistedE6FrameSearch_sound _ [] twistedE6FrameSearch_check S
    (List.filter_sublist) (fun _ _ _ h => absurd h List.not_mem_nil) hSpw
  rw [List.append_nil] at hleaf
  have hRF : S.reverse.Perm F := (List.reverse_perm S).trans hSF
  have hne : S.reverse.isEmpty = false := by
    rw [List.isEmpty_eq_false_iff]
    intro h
    exact hF0 (List.Perm.eq_nil (h ▸ hRF).symm)
  have hclosed : (S.reverse.all fun γ => S.reverse.contains (permLattice TwistTag.E6.perm γ)) =
      true := by
    rw [List.all_eq_true]
    intro γ hγ
    rw [List.contains_iff_mem, hRF.mem_iff]
    exact (hF γ (hRF.subset hγ)).2.2
  simp only [twistedE6FrameLeafB, hne, hclosed, Bool.not_true, Bool.false_or] at hleaf
  obtain ⟨e, he, hperm⟩ := List.any_eq_true.1 hleaf
  obtain ⟨hk, hmap⟩ := twistedE6FrameTable_check e he
  have hFe : F.Perm e.1 := (hRF.symm.trans (List.isPerm_iff.1 hperm).symm)
  have hmapF : (F.map (twistedE6RelAct e.2.1)).Perm (twistedE6FrameReps.getD e.2.2 []) :=
    (hFe.map _).trans (List.isPerm_iff.1 hmap)
  have hFr : ∀ β ∈ F, IsRoot TwistTag.E6.tag β := fun β hβ => (hF β hβ).1
  obtain ⟨g, hg, hge⟩ := exists_conj_mem_twistedE6Reps_of_frameRep (K := K) hσσ hδ hk
  have hrnd : (twistedE6FrameReps.getD e.2.2 []).Nodup := by
    have h : ∀ k ∈ List.range 7, (twistedE6FrameReps.getD k []).Nodup := by decide +kernel
    exact h _ (List.mem_range.2 hk)
  have hprod : twistedE6RelWeyl K e.2.1 * (F.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod *
      (twistedE6RelWeyl K e.2.1)⁻¹ =
      ((twistedE6FrameReps.getD e.2.2 []).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod := by
    rw [twistedE6RelWeyl_conj_list_prod e.2.1 hFr fun _ => (1 : K)]
    have e1 : (F.map fun β => pinnedX TwistTag.E6.tag K (twistedE6RelAct e.2.1 β) 1) =
        ((F.map (twistedE6RelAct e.2.1)).map fun γ => pinnedX TwistTag.E6.tag K γ 1) := by
      rw [List.map_map]
      rfl
    rw [e1]
    refine (hmapF.map _).prod_eq' ?_
    exact List.pairwise_map.2 ((hmapF.nodup_iff.2 hrnd).pairwise_of_forall_ne
      fun γ hγ δ hδ hne => twistedE6FrameReps_commute (hmapF.subset hγ) (hmapF.subset hδ) hne 1 1)
  have e2 : g * twistedE6RelWeyl K e.2.1 * (F.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod *
      (g * twistedE6RelWeyl K e.2.1)⁻¹ =
      g * ((twistedE6FrameReps.getD e.2.2 []).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod *
        g⁻¹ := by
    rw [← hprod]
    group
  refine ⟨g * twistedE6RelWeyl K e.2.1, mul_mem hg (twistedE6RelWeyl_mem σ _), ?_⟩
  rw [e2]
  exact hge

@[expose] def twistedE6Unit (γ : Fin TwistTag.E6.tag.rank → ℤ) : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  if permLattice TwistTag.E6.perm γ = γ then [γ] else [γ, permLattice TwistTag.E6.perm γ]

variable (K) in
@[expose] noncomputable def twistedE6RelX (σ : K →+* K) (γ : Fin TwistTag.E6.tag.rank → ℤ)
    (c : K) : ModGL TwistTag.E6.tag K :=
  if permLattice TwistTag.E6.perm γ = γ then pinnedX TwistTag.E6.tag K γ c
  else twistedE6PairX σ γ c

theorem twistedE6RelX_one (σ : K →+* K) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    twistedE6RelX K σ γ 1 =
      ((twistedE6Unit γ).map fun β => pinnedX TwistTag.E6.tag K β 1).prod := by
  unfold twistedE6RelX twistedE6Unit
  split_ifs
  · simp
  · simp [twistedE6PairX, map_one]

theorem list_prod_twistedE6RelX_one (σ : K →+* K) (R : List (Fin TwistTag.E6.tag.rank → ℤ)) :
    (R.map fun γ => twistedE6RelX K σ γ 1).prod =
      ((R.flatMap twistedE6Unit).map fun β => pinnedX TwistTag.E6.tag K β 1).prod := by
  induction R with
  | nil => simp
  | cons γ R ih =>
    rw [List.map_cons, List.prod_cons, ih, List.flatMap_cons, List.map_append, List.prod_append,
      twistedE6RelX_one]

theorem twistedE6_cartanChar_mul {τ : Tag} (c c' : Fin τ.rank → Kˣ) :
    cartanChar (c * c') = cartanChar c * cartanChar c' := by
  funext l
  simp only [cartanChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem frameTorusElt_E6_eq_rootDiagUnit (γ : Fin TwistTag.E6.tag.rank → ℤ) (a : Kˣ) :
    frameTorusElt TwistTag.E6.tag K γ a =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag
        (cartanChar fun i => a ^ γ i) := by
  have hs : ∀ i : Fin TwistTag.E6.tag.rank, TwistTag.E6.tag.symmetrizer i i = 1 := by decide
  rw [← list_prod_torusElt_eq_rootDiagUnit, frameTorusElt]
  simp only [hs, one_mul]

theorem frameTorusElt_pair_mem_graphFixedRootGroup {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) (a : Kˣ) :
    frameTorusElt TwistTag.E6.tag K γ a *
        frameTorusElt TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ)
          (Units.map σ.toMonoidHom a) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hσa : Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a) = a :=
    Units.ext (hσσ (a : K))
  have hγi : ∀ i : Fin TwistTag.E6.tag.rank,
      permLattice TwistTag.E6.perm γ i = γ (TwistTag.E6.perm i) := fun i => by
    simp only [permLattice, Function.comp_apply, twistedE6_perm_symm_apply]
  set c : Fin TwistTag.E6.tag.rank → Kˣ := fun i =>
    a ^ γ i * Units.map σ.toMonoidHom a ^ permLattice TwistTag.E6.perm γ i with hcdef
  have hc : ∀ i : Fin TwistTag.E6.tag.rank,
      c (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (c i) := fun i => by
    simp only [hcdef, map_mul, map_zpow, hσa, hγi, twistedE6_perm_perm]
    exact mul_comm _ _
  obtain ⟨w, hw⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ) (b := c) hc
  have e : frameTorusElt TwistTag.E6.tag K γ a *
      frameTorusElt TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ)
        (Units.map σ.toMonoidHom a) =
      ((List.finRange TwistTag.E6.foldedTag.rank).map fun b =>
        (orbitH TwistTag.E6 K σ b (w b) : ModGL TwistTag.E6.tag K)).prod := by
    rw [list_prod_orbitH_eq_rootDiagUnit, hw, frameTorusElt_E6_eq_rootDiagUnit,
      frameTorusElt_E6_eq_rootDiagUnit, ← rootDiagUnit_mul, ← twistedE6_cartanChar_mul]
    rfl
  rw [e]
  exact list_prod_mem fun x hx => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup TwistTag.E6 σ b (w b)

theorem exists_twistedE6_unit_torus [Finite K] [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hpair : permLattice TwistTag.E6.perm γ ≠ γ → iform γ (permLattice TwistTag.E6.perm γ) = 0)
    {c : K} (hc : c ≠ 0) (hcσ : permLattice TwistTag.E6.perm γ = γ → σ c = c) :
    ∃ A ∈ graphFixedRootGroup TwistTag.E6 K σ,
      (∀ δ, IsRoot TwistTag.E6.tag δ → (∀ γ' ∈ twistedE6Unit γ, iform γ' δ = 0) → ∀ e : K,
        A * pinnedX TwistTag.E6.tag K δ e * A⁻¹ = pinnedX TwistTag.E6.tag K δ e) ∧
      A * twistedE6RelX K σ γ c * A⁻¹ = twistedE6RelX K σ γ 1 := by
  have hγγ : iform γ γ = 2 := classD4_iform_self (Or.inr (Or.inl rfl)) hγ
  have hcoef : ∀ {a : Kˣ}, a ^ 2 = (Units.mk0 c hc)⁻¹ → ((a ^ (2 : ℤ) : Kˣ) : K) * c = 1 := by
    intro a ha
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ha, Units.val_inv_eq_inv_val,
      Units.val_mk0, inv_mul_cancel₀ hc]
  by_cases hρ : permLattice TwistTag.E6.perm γ = γ
  ·
    obtain ⟨a, ha, haσ⟩ := exists_sq_eq_of_sigma_fixed σ (u := (Units.mk0 c hc)⁻¹)
      (Units.ext (by simp [hcσ hρ]))
    refine ⟨frameTorusElt TwistTag.E6.tag K γ a,
      frameTorusElt_mem_graphFixedRootGroup σ hρ haσ, fun δ hδ hδγ e => ?_, ?_⟩
    · have h0 : iform γ δ = 0 := hδγ γ (by simp [twistedE6Unit, hρ])
      rw [frameTorusElt_conj_pinnedX _ _ hδ, h0, zpow_zero, Units.val_one, one_mul]
    · unfold twistedE6RelX
      simp only [hρ, ↓reduceIte]
      rw [frameTorusElt_conj_pinnedX _ _ hγ, hγγ, hcoef ha]
  ·
    have hρr : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm γ) :=
      hγ.permLattice TwistTag.E6.cartan_perm
    have h0 := hpair hρ
    have h0' : iform (permLattice TwistTag.E6.perm γ) γ = 0 := by rw [iform_comm]; exact h0
    have hρρ : iform (permLattice TwistTag.E6.perm γ) (permLattice TwistTag.E6.perm γ) = 2 :=
      classD4_iform_self (Or.inr (Or.inl rfl)) hρr
    obtain ⟨a, ha⟩ := frameTorus_exists_sq_eq (Units.mk0 c hc)⁻¹
    set A₁ := frameTorusElt TwistTag.E6.tag K γ a
    set A₂ := frameTorusElt TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ)
      (Units.map σ.toMonoidHom a)
    have hA : ∀ δ, IsRoot TwistTag.E6.tag δ → ∀ e : K,
        (A₁ * A₂) * pinnedX TwistTag.E6.tag K δ e * (A₁ * A₂)⁻¹ =
          pinnedX TwistTag.E6.tag K δ (((a ^ iform γ δ : Kˣ) : K) *
            (((Units.map σ.toMonoidHom a ^ iform (permLattice TwistTag.E6.perm γ) δ : Kˣ) : K) *
              e)) := fun δ hδ e => by
      rw [show (A₁ * A₂) * pinnedX TwistTag.E6.tag K δ e * (A₁ * A₂)⁻¹ =
          A₁ * (A₂ * pinnedX TwistTag.E6.tag K δ e * A₂⁻¹) * A₁⁻¹ by group,
        frameTorusElt_conj_pinnedX _ _ hδ, frameTorusElt_conj_pinnedX _ _ hδ]
    refine ⟨A₁ * A₂, frameTorusElt_pair_mem_graphFixedRootGroup hσσ γ a,
      fun δ hδ hδγ e => ?_, ?_⟩
    · have h1 : iform γ δ = 0 := hδγ γ (by simp [twistedE6Unit, hρ])
      have h2 : iform (permLattice TwistTag.E6.perm γ) δ = 0 :=
        hδγ _ (by simp [twistedE6Unit, hρ])
      rw [hA δ hδ, h1, h2, zpow_zero, zpow_zero, Units.val_one, one_mul, one_mul]
    · unfold twistedE6RelX
      simp only [hρ, ↓reduceIte]
      rw [twistedE6PairX, twistedE6PairX]
      rw [show (A₁ * A₂) * (pinnedX TwistTag.E6.tag K γ c *
            pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c)) * (A₁ * A₂)⁻¹ =
          ((A₁ * A₂) * pinnedX TwistTag.E6.tag K γ c * (A₁ * A₂)⁻¹) *
            ((A₁ * A₂) * pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm γ) (σ c) *
              (A₁ * A₂)⁻¹) by group,
        hA γ hγ, hA _ hρr, hγγ, h0, h0', hρρ, zpow_zero, zpow_zero, Units.val_one, one_mul,
        one_mul, hcoef ha, map_one]
      congr 2
      have hσa : ((Units.map σ.toMonoidHom a ^ (2 : ℤ) : Kˣ) : K) * σ c =
          σ (((a ^ (2 : ℤ) : Kˣ) : K) * c) := by
        rw [map_mul, ← map_zpow, Units.coe_map]
        rfl
      rw [hσa, hcoef ha, map_one]

theorem exists_twistedE6_torus_conj_relX_prod [Finite K] [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {R : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : ∀ γ ∈ R, IsRoot TwistTag.E6.tag γ)
    (hpair : ∀ γ ∈ R, permLattice TwistTag.E6.perm γ ≠ γ →
      iform γ (permLattice TwistTag.E6.perm γ) = 0)
    (horth : R.Pairwise fun γ δ => ∀ γ' ∈ twistedE6Unit γ, ∀ δ' ∈ twistedE6Unit δ, iform γ' δ' = 0)
    (c : (Fin TwistTag.E6.tag.rank → ℤ) → K)
    (hc : ∀ γ ∈ R, c γ ≠ 0 ∧ (permLattice TwistTag.E6.perm γ = γ → σ (c γ) = c γ)) :
    ∃ h ∈ graphFixedRootGroup TwistTag.E6 K σ,
      h * (R.map fun γ => twistedE6RelX K σ γ (c γ)).prod * h⁻¹ =
        (R.map fun γ => twistedE6RelX K σ γ 1).prod := by
  suffices H : ∃ h ∈ graphFixedRootGroup TwistTag.E6 K σ,
      (∀ δ, IsRoot TwistTag.E6.tag δ → (∀ γ ∈ R, ∀ γ' ∈ twistedE6Unit γ, iform γ' δ = 0) →
        ∀ e : K, h * pinnedX TwistTag.E6.tag K δ e * h⁻¹ = pinnedX TwistTag.E6.tag K δ e) ∧
      h * (R.map fun γ => twistedE6RelX K σ γ (c γ)).prod * h⁻¹ =
        (R.map fun γ => twistedE6RelX K σ γ 1).prod by
    obtain ⟨h, hh, -, he⟩ := H
    exact ⟨h, hh, he⟩
  induction R with
  | nil => exact ⟨1, one_mem _, fun δ _ _ e => by rw [one_mul, inv_one, mul_one], by simp⟩
  | cons γ R ih =>
    obtain ⟨hγR, hRR⟩ := List.pairwise_cons.1 horth
    obtain ⟨h', hC', hfix', hprod'⟩ := ih (fun δ h => hR δ (List.mem_cons_of_mem _ h))
      (fun δ h => hpair δ (List.mem_cons_of_mem _ h)) hRR
      (fun δ h => hc δ (List.mem_cons_of_mem _ h))
    obtain ⟨A, hA, hfixA, hAe⟩ := exists_twistedE6_unit_torus hσσ (hR γ List.mem_cons_self)
      (hpair γ List.mem_cons_self) (hc γ List.mem_cons_self).1 (hc γ List.mem_cons_self).2
    have hfixRelX : ∀ {B : ModGL TwistTag.E6.tag K} {β : Fin TwistTag.E6.tag.rank → ℤ}
        (_ : IsRoot TwistTag.E6.tag β)
        (_ : ∀ δ, IsRoot TwistTag.E6.tag δ → δ ∈ twistedE6Unit β → ∀ e : K,
          B * pinnedX TwistTag.E6.tag K δ e * B⁻¹ = pinnedX TwistTag.E6.tag K δ e) (e : K),
        B * twistedE6RelX K σ β e * B⁻¹ = twistedE6RelX K σ β e := by
      intro B β hβ hB e
      unfold twistedE6RelX
      split_ifs with hρβ
      · exact hB β hβ (by simp [twistedE6Unit, hρβ]) e
      · rw [twistedE6PairX, show B * (pinnedX TwistTag.E6.tag K β e *
            pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) (σ e)) * B⁻¹ =
            (B * pinnedX TwistTag.E6.tag K β e * B⁻¹) *
              (B * pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) (σ e) * B⁻¹) by group,
          hB β hβ (by simp [twistedE6Unit, hρβ]) e,
          hB _ (hβ.permLattice TwistTag.E6.cartan_perm) (by simp [twistedE6Unit, hρβ]) (σ e)]
    refine ⟨A * h', mul_mem hA hC', fun δ hδ hδR e => ?_, ?_⟩
    · rw [show A * h' * pinnedX TwistTag.E6.tag K δ e * (A * h')⁻¹ =
          A * (h' * pinnedX TwistTag.E6.tag K δ e * h'⁻¹) * A⁻¹ by group,
        hfix' δ hδ (fun γ' h => hδR γ' (List.mem_cons_of_mem _ h)) e,
        hfixA δ hδ (hδR γ List.mem_cons_self) e]
    · rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        show A * h' * (twistedE6RelX K σ γ (c γ) *
            (R.map fun γ => twistedE6RelX K σ γ (c γ)).prod) * (A * h')⁻¹ =
          A * (h' * twistedE6RelX K σ γ (c γ) * h'⁻¹) * A⁻¹ *
            (A * (h' * (R.map fun γ => twistedE6RelX K σ γ (c γ)).prod * h'⁻¹) * A⁻¹) by group,
        hfixRelX (hR γ List.mem_cons_self) (fun δ hδ hδu e => hfix' δ hδ (fun β hβ β' hβ' => by
          rw [iform_comm]
          exact hγR β hβ δ hδu β' hβ') e) (c γ), hAe, hprod']
      congr 1
      refine frameTorus_conj_list_prod_of_forall A _ fun x hx => ?_
      obtain ⟨β, hβR, rfl⟩ := List.mem_map.1 hx
      exact hfixRelX (hR β (List.mem_cons_of_mem _ hβR)) (fun δ hδ hδu e =>
        hfixA δ hδ (fun γ' hγ' => hγR β hβR γ' hγ' δ hδu) e) 1

end CFSG.SeitzReduction
