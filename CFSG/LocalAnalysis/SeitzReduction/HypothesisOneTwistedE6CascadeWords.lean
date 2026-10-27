module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassKillBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListFrames

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

@[expose] def twistedE6CascPairE6 : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ)

@[expose] def twistedE6CascPairA5 : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 0, 1, 1, 1, 0] : Fin 6 → ℤ)

@[expose] def twistedE6CascJE6 : List (Fin TwistTag.E6.tag.rank) :=
  ([0, 1, 2, 3, 4, 5] : List (Fin 6))

@[expose] def twistedE6CascJA5 : List (Fin TwistTag.E6.tag.rank) := ([0, 2, 3, 4, 5] : List (Fin 6))

@[expose] def twistedE6CascJA3 : List (Fin TwistTag.E6.tag.rank) := ([2, 3, 4] : List (Fin 6))

@[expose] def twistedE6CascPosA5 : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  twistedE6PosRoots.filter fun δ : Fin 6 → ℤ => δ 1 == 0

@[expose] def twistedE6CascPosA3 : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  twistedE6PosRoots.filter fun δ : Fin 6 → ℤ => δ 0 == 0 && δ 1 == 0 && δ 5 == 0

@[expose] def twistedE6CascPosA3' : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  twistedE6PosRoots.filter fun δ => iform twistedE6CascPairE6 δ == 0 &&
    iform (permLattice TwistTag.E6.perm twistedE6CascPairE6) δ == 0

@[expose] def twistedE6CascWordE6 :
    Fin TwistTag.E6.tag.rank → List (Fin TwistTag.E6.foldedTag.rank) :=
  (![[0, 1, 2, 3, 1, 2, 1], [3, 2, 1, 2, 0, 1, 2], [0, 1, 2, 3, 1, 2, 0], [3, 2, 1, 2, 3, 0, 1],
    [0, 1, 2, 3, 0, 1, 2, 0], [0, 1, 2, 3, 0, 1, 2, 1]] : Fin 6 → List (Fin 4))

@[expose] def twistedE6CascWordA5 :
    Fin TwistTag.E6.tag.rank → List (Fin TwistTag.E6.foldedTag.rank) :=
  (![[1, 2, 1], [], [1, 2, 0], [0, 1], [0, 1, 2, 0], [0, 1, 2, 1]] : Fin 6 → List (Fin 4))

@[expose] def twistedE6CascWordA3 :
    Fin TwistTag.E6.tag.rank → List (Fin TwistTag.E6.foldedTag.rank) :=
  (![[], [], [2], [1], [1, 2], []] : Fin 6 → List (Fin 4))

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascE6_rho : ∀ j ∈ twistedE6CascJE6, TwistTag.E6.perm j ∈ twistedE6CascJE6 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascE6_word :
    ∀ i ∈ twistedE6CascJE6, ∀ a ∈ twistedE6CascWordE6 i, ∀ j ∈ TwistTag.E6.orbitWord a,
      j ∈ twistedE6CascJE6 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascE6_long :
    ∀ i ∈ twistedE6CascJE6, TwistTag.E6.perm i = i →
      twistedE6RelAct (twistedE6CascWordE6 i) (Pi.single i 1) = e6HighestRoot ∧
        ∀ δ ∈ twistedE6PosRoots,
          (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJE6 → δ l = 0) →
          classKillPair i δ = 0 →
            twistedE6RelAct (twistedE6CascWordE6 i) δ ∈ twistedE6CascPosA5 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascE6_short :
    ∀ i ∈ twistedE6CascJE6, TwistTag.E6.perm i ≠ i →
      twistedE6RelAct (twistedE6CascWordE6 i) (Pi.single i 1) = twistedE6CascPairE6 ∧
        twistedE6RelAct (twistedE6CascWordE6 i) (Pi.single (TwistTag.E6.perm i) 1) =
          permLattice TwistTag.E6.perm twistedE6CascPairE6 ∧
        ∀ δ ∈ twistedE6PosRoots,
          (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJE6 → δ l = 0) →
          classKillPair i δ = 0 → classKillPair (TwistTag.E6.perm i) δ = 0 →
            twistedE6RelAct (twistedE6CascWordE6 i) δ ∈ twistedE6CascPosA3' := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascA5_rho : ∀ j ∈ twistedE6CascJA5, TwistTag.E6.perm j ∈ twistedE6CascJA5 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascA5_word :
    ∀ i ∈ twistedE6CascJA5, ∀ a ∈ twistedE6CascWordA5 i, ∀ j ∈ TwistTag.E6.orbitWord a,
      j ∈ twistedE6CascJA5 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascA5_long :
    ∀ i ∈ twistedE6CascJA5, TwistTag.E6.perm i = i →
      twistedE6RelAct (twistedE6CascWordA5 i) (Pi.single i 1) = e6CascR17 ∧
        ∀ δ ∈ twistedE6PosRoots,
          (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA5 → δ l = 0) →
          classKillPair i δ = 0 →
            twistedE6RelAct (twistedE6CascWordA5 i) δ ∈ twistedE6CascPosA3 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascA5_short :
    ∀ i ∈ twistedE6CascJA5, TwistTag.E6.perm i ≠ i →
      twistedE6RelAct (twistedE6CascWordA5 i) (Pi.single i 1) = twistedE6CascPairA5 ∧
        twistedE6RelAct (twistedE6CascWordA5 i) (Pi.single (TwistTag.E6.perm i) 1) =
          permLattice TwistTag.E6.perm twistedE6CascPairA5 ∧
        ∀ δ ∈ twistedE6PosRoots,
          (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA5 → δ l = 0) →
          classKillPair i δ = 0 → classKillPair (TwistTag.E6.perm i) δ = 0 →
            twistedE6RelAct (twistedE6CascWordA5 i) δ ∈ [e6RootA4] := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascA3_rho : ∀ j ∈ twistedE6CascJA3, TwistTag.E6.perm j ∈ twistedE6CascJA3 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascA3_word :
    ∀ i ∈ twistedE6CascJA3, ∀ a ∈ twistedE6CascWordA3 i, ∀ j ∈ TwistTag.E6.orbitWord a,
      j ∈ twistedE6CascJA3 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascA3_long :
    ∀ i ∈ twistedE6CascJA3, TwistTag.E6.perm i = i →
      twistedE6RelAct (twistedE6CascWordA3 i) (Pi.single i 1) = e6CascC ∧
        ∀ δ ∈ twistedE6PosRoots,
          (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 → δ l = 0) →
          classKillPair i δ = 0 →
            twistedE6RelAct (twistedE6CascWordA3 i) δ ∈ [e6RootA4] := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem twistedE6CascA3_short :
    ∀ i ∈ twistedE6CascJA3, TwistTag.E6.perm i ≠ i →
      twistedE6RelAct (twistedE6CascWordA3 i) (Pi.single i 1) = e6RootA34 ∧
        twistedE6RelAct (twistedE6CascWordA3 i) (Pi.single (TwistTag.E6.perm i) 1) =
          permLattice TwistTag.E6.perm e6RootA34 ∧
        ∀ δ ∈ twistedE6PosRoots,
          (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 → δ l = 0) →
          classKillPair i δ = 0 → classKillPair (TwistTag.E6.perm i) δ = 0 →
            twistedE6RelAct (twistedE6CascWordA3 i) δ ∈
              ([] : List (Fin TwistTag.E6.tag.rank → ℤ)) := by
  decide +kernel

end CFSG.SeitzReduction
