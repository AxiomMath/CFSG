module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhUnions
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Finset

@[expose] def frameFanoData : List (List (Fin 8) × List (List (Fin 8) × List (Fin 2))) := [
  ([1, 2, 4], [
    ([1, 2, 4], []), ([1, 2, 5], [0, 0, 0, 0, 0, 0]),
    ([1, 2, 6], [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), ([1, 2, 7], [0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0]),
    ([1, 3, 4], [1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), ([1, 3, 5], [0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]),
    ([1, 3, 6], [1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]),
    ([1, 3, 7], [1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]), ([1, 4, 6], [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0]),
    ([1, 4, 7], [1, 0, 1, 0, 0, 0, 1, 0, 1]), ([1, 5, 6], [0, 1, 0, 0, 0, 0, 1, 0, 1, 0]),
    ([1, 5, 7], [0, 0, 0, 0, 0]), ([2, 3, 4], [0]), ([2, 3, 5], [1, 0, 0, 1, 0, 0, 1, 0, 1, 0]),
    ([2, 3, 6], [1, 0, 0, 1, 0, 0, 1, 0, 1]), ([2, 3, 7], [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0]),
    ([2, 4, 5], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), ([2, 4, 7], [1, 0, 0, 0, 0, 0, 1, 0, 0, 1]),
    ([2, 5, 6], [1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]),
    ([2, 6, 7], [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1]), ([3, 4, 5], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1]),
    ([3, 4, 6], [0, 0]), ([3, 5, 7], [1, 0, 0, 0, 0, 1, 0, 1, 0]), ([3, 6, 7], [0, 0, 0]),
    ([4, 5, 6], [1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0]), ([4, 5, 7], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0]),
    ([4, 6, 7], [0, 1, 0, 0, 1, 0, 0, 1, 0, 1]), ([5, 6, 7], [0, 0, 0, 0])]),
  ([0, 2, 4], [
    ([0, 2, 4], []), ([0, 2, 5], [1, 0, 1, 0, 1, 0, 0, 0, 1, 0]),
    ([0, 2, 6], [0, 1, 0, 0, 0, 0, 0, 0]), ([0, 2, 7], [0, 0, 1, 0, 1, 0, 0, 0, 0]),
    ([0, 3, 4], [1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), ([0, 3, 5], [0, 0, 1, 0, 0, 0, 1, 0, 0]),
    ([0, 3, 6], [0, 1, 0, 0, 1, 0, 0, 0, 0]), ([0, 3, 7], [1, 0, 0, 0, 0, 0, 1]),
    ([0, 4, 6], [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1]), ([0, 4, 7], [1, 0, 1, 0, 0, 1, 0, 0, 1, 0]),
    ([0, 5, 6], [1, 0, 0, 0, 0, 1]), ([0, 5, 7], [1, 0, 1, 0, 0, 0, 0, 1, 0]),
    ([2, 3, 4], [0, 0, 0, 1, 0, 0, 0, 0]), ([2, 3, 5], [0, 1, 0, 1, 0, 0, 0, 1, 0, 0]),
    ([2, 3, 6], [1, 0, 1]), ([2, 3, 7], [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1]),
    ([2, 4, 5], [0, 0, 0, 0, 1, 0, 1, 0, 1]), ([2, 4, 6], [0, 0, 0, 1, 0, 1, 0, 1, 0, 1]),
    ([2, 5, 7], [1, 0, 0, 0, 1]), ([2, 6, 7], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1]),
    ([3, 4, 5], [0, 1, 0, 1, 0, 0, 1, 0]), ([3, 4, 7], [0, 0, 0, 0, 1, 0, 1, 0, 0, 1]),
    ([3, 5, 6], [0, 0, 1, 0, 0, 1, 0]), ([3, 6, 7], [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]),
    ([4, 5, 6], [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0]), ([4, 5, 7], [0, 1, 0, 0, 0, 1, 0]),
    ([4, 6, 7], [1, 0, 0, 1]), ([5, 6, 7], [0, 0, 0, 0, 1, 0])]),
  ([0, 1, 4], [
    ([0, 1, 4], []), ([0, 1, 5], [0, 0, 1, 0, 0, 0, 0, 1, 0]),
    ([0, 1, 6], [0, 0, 1, 0, 1, 0, 0, 0, 1, 0]), ([0, 1, 7], [0, 0, 0, 0, 0, 1]),
    ([0, 3, 4], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1]), ([0, 3, 5], [0, 0, 1, 0, 1, 0, 1, 0, 0, 0]),
    ([0, 3, 6], [0, 0, 1, 0, 0, 1, 0, 0, 0]), ([0, 3, 7], [0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0]),
    ([0, 4, 5], [0, 1, 0, 1, 0, 0, 1, 0, 0, 1]), ([0, 4, 7], [0, 1, 0, 1, 0, 1, 0, 0, 0, 1]),
    ([0, 5, 6], [0, 1, 0, 1, 0, 0, 0, 0, 1]), ([0, 6, 7], [0, 1, 0, 1, 0, 0, 0, 0, 0, 0]),
    ([1, 3, 4], [0, 0, 1, 0, 0, 0, 1]), ([1, 3, 5], [0, 0, 1, 0, 1, 0, 1, 0, 1]),
    ([1, 3, 6], [0, 0, 1, 0, 0, 1, 0, 1]), ([1, 3, 7], [0, 0, 0, 1, 0, 0, 1]),
    ([1, 4, 5], [0, 0, 0, 0, 0, 0, 1, 0]), ([1, 4, 6], [1, 0, 0]),
    ([1, 5, 7], [0, 0, 0, 1, 0, 1, 0, 1]), ([1, 6, 7], [0, 0, 0, 0, 1, 0, 1]),
    ([3, 4, 6], [1, 0, 1, 0]), ([3, 4, 7], [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0]),
    ([3, 5, 6], [1, 0, 0, 1, 0, 0, 1, 0, 0]), ([3, 5, 7], [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0]),
    ([4, 5, 6], [1, 0, 0, 1, 0, 0]), ([4, 5, 7], [1, 0, 1, 0, 1, 0, 1, 0]),
    ([4, 6, 7], [0, 0, 0, 0, 1, 0, 0, 0]), ([5, 6, 7], [1, 0, 0, 1, 0, 1, 0])]),
  ([0, 1, 4], [
    ([0, 1, 4], []), ([0, 1, 5], [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0]),
    ([0, 1, 6], [0, 1, 0, 0, 0, 0, 1, 0, 1, 0]), ([0, 1, 7], [1, 0, 0, 0, 0, 0]),
    ([0, 2, 4], [1, 0, 0, 1, 0, 0, 0]), ([0, 2, 5], [1, 0, 0, 1, 0, 1, 0, 1, 0]),
    ([0, 2, 6], [1, 0, 0, 1, 0, 0, 1, 0]), ([0, 2, 7], [1, 0, 0, 0, 1, 0, 0]),
    ([0, 4, 5], [0, 1, 0, 1, 0, 0, 1, 0, 0, 1]), ([0, 4, 6], [0, 0, 1]),
    ([0, 5, 7], [1, 0, 0, 0, 1, 0, 1, 0]), ([0, 6, 7], [1, 0, 0, 0, 0, 1, 0]),
    ([1, 2, 4], [0, 0, 0, 0, 0, 1, 0, 1, 0]), ([1, 2, 5], [1, 0, 1, 0, 1, 0, 0, 0, 1, 0]),
    ([1, 2, 6], [0, 1, 0, 0, 0, 0, 0, 0]), ([1, 2, 7], [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]),
    ([1, 4, 5], [0, 0, 0, 0, 0, 0, 1, 0]), ([1, 4, 7], [0, 0, 0, 0, 0, 1, 0, 0]),
    ([1, 5, 6], [1, 0, 1, 0, 1, 0, 0, 0, 0]), ([1, 6, 7], [0, 1, 0, 0, 0, 0, 1, 0, 0]),
    ([2, 4, 6], [0, 1, 0, 1]), ([2, 4, 7], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0]),
    ([2, 5, 6], [0, 0, 1, 0, 0, 1, 0, 0, 1]), ([2, 5, 7], [0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]),
    ([4, 5, 6], [0, 0, 1, 0, 0, 1]), ([4, 5, 7], [0, 1, 0, 1, 0, 1, 0, 1]),
    ([4, 6, 7], [0, 0, 0, 0, 1, 0, 0, 0]), ([5, 6, 7], [0, 0, 1, 0, 1, 0, 1])]),
  ([0, 1, 2], [
    ([0, 1, 2], []), ([0, 1, 3], [1]), ([0, 1, 6], [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]),
    ([0, 1, 7], [0, 1, 0, 0, 1, 0, 0, 1, 0]), ([0, 2, 3], [1, 0, 0, 0, 1, 0, 0, 0, 0]),
    ([0, 2, 5], [1, 0, 1, 0, 0, 1, 0, 1]), ([0, 2, 7], [0, 0, 1, 0, 1, 0, 0, 0, 0, 0]),
    ([0, 3, 5], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0]),
    ([0, 3, 6], [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0]),
    ([0, 5, 6], [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0]), ([0, 5, 7], [1, 0, 0, 0, 0, 0, 1, 0, 0]),
    ([0, 6, 7], [1, 0, 0, 0, 1, 0, 0, 1, 0, 0]), ([1, 2, 3], [0, 0, 0, 1, 0, 0, 0, 0]),
    ([1, 2, 5], [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0]),
    ([1, 2, 6], [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0]), ([1, 3, 5], [0, 1, 0, 0, 1, 0, 1]),
    ([1, 3, 7], [0, 0, 0, 0, 0, 1, 0, 0, 1]), ([1, 5, 6], [0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0]),
    ([1, 5, 7], [0, 0, 0, 0, 0, 1, 0, 0]), ([1, 6, 7], [0, 0, 0, 1, 0, 0, 1, 0, 0]),
    ([2, 3, 6], [0, 1, 0]), ([2, 3, 7], [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]),
    ([2, 5, 6], [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), ([2, 5, 7], [1, 0, 1, 0, 0, 1, 0]),
    ([2, 6, 7], [0, 1, 0, 1]), ([3, 5, 6], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]),
    ([3, 5, 7], [0, 1, 0, 0, 1, 0]), ([3, 6, 7], [1, 0, 1, 0, 1])]),
  ([0, 1, 2], [
    ([0, 1, 2], []), ([0, 1, 3], [1]), ([0, 1, 6], [0, 1, 0, 1, 0, 0, 0, 0, 0]),
    ([0, 1, 7], [0, 1, 0, 0, 1, 0, 1, 0, 1, 0]), ([0, 2, 3], [1, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
    ([0, 2, 4], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0]), ([0, 2, 6], [0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0]),
    ([0, 3, 4], [1, 0, 0, 1, 0, 0, 0, 0, 0]), ([0, 3, 7], [0, 1, 0, 0, 1, 0, 0, 1]),
    ([0, 4, 6], [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]), ([0, 4, 7], [0, 1, 0, 0, 0, 1, 0, 0, 0]),
    ([0, 6, 7], [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1]), ([1, 2, 3], [0, 1, 0, 0, 0, 0, 0, 0, 1]),
    ([1, 2, 4], [0, 0, 1, 0, 0, 0, 0, 0]), ([1, 2, 7], [0, 0, 0, 1, 0, 1, 0, 1, 0]),
    ([1, 3, 4], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0]), ([1, 3, 6], [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0]),
    ([1, 4, 6], [1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]), ([1, 4, 7], [0, 0, 1, 0, 0, 0, 0, 0, 1]),
    ([1, 6, 7], [0, 1, 0, 1, 0, 0, 0, 0, 0, 1]), ([2, 3, 6], [0, 0, 1, 0, 0, 1, 0, 0, 0]),
    ([2, 3, 7], [0, 0, 0, 1, 0, 0, 1]), ([2, 4, 6], [0, 0, 0, 1, 0, 1, 0, 0, 1, 0]),
    ([2, 4, 7], [1, 0, 1, 0, 0, 1, 0, 0]), ([2, 6, 7], [1, 0, 0, 0, 1, 0, 0]),
    ([3, 4, 6], [1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0]), ([3, 4, 7], [0, 1, 0, 0, 1, 0, 0]),
    ([3, 6, 7], [0, 0, 0, 1, 0, 0])]),
  ([0, 1, 2], [
    ([0, 1, 2], []), ([0, 1, 3], [1]), ([0, 1, 4], [0, 1, 0, 0, 0, 1, 0, 1]),
    ([0, 1, 5], [0, 1, 0, 0, 1, 0, 1, 0, 1]), ([0, 2, 3], [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1]),
    ([0, 2, 5], [0, 0, 1, 0, 0, 0, 0, 1, 0]), ([0, 2, 7], [0, 1, 0, 0, 0, 0, 1]),
    ([0, 3, 4], [1, 0, 0, 1, 0, 0, 0, 0, 0]), ([0, 3, 7], [0, 1, 0, 0, 1, 0, 0, 1]),
    ([0, 4, 5], [1, 0, 1, 0, 0, 0, 1, 0]), ([0, 4, 7], [1, 0, 1, 0, 1, 0, 1, 0, 0, 0]),
    ([0, 5, 7], [1, 0, 0, 0, 0, 0, 1, 0, 0]), ([1, 2, 3], [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1]),
    ([1, 2, 4], [0, 0, 1, 0, 0, 0, 0, 0]), ([1, 2, 7], [1, 0, 1, 0, 0, 1, 0, 0, 1]),
    ([1, 3, 5], [0, 0, 1, 0, 0, 0, 1, 0, 0]), ([1, 3, 7], [1, 0, 1, 0, 0, 0, 0, 1]),
    ([1, 4, 5], [0, 1, 0, 0, 0, 1, 0]), ([1, 4, 7], [0, 1, 0, 1, 0, 1, 0, 0, 0]),
    ([1, 5, 7], [0, 0, 0, 0, 0, 1, 0, 0]), ([2, 3, 4], [0, 0, 0, 0, 0, 1, 0, 1, 0, 1]),
    ([2, 3, 5], [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0]), ([2, 4, 5], [0, 0, 0, 0, 0, 0, 1, 0]),
    ([2, 4, 7], [1, 0, 1, 0, 0, 1, 0, 0]), ([2, 5, 7], [0, 1, 0, 0, 0, 0]),
    ([3, 4, 5], [1, 0, 0, 0, 0, 0, 0, 1, 0]), ([3, 4, 7], [0, 1, 0, 0, 1, 0, 0]),
    ([3, 5, 7], [1, 0, 1, 0, 0, 0, 0])]),
  ([0, 1, 2], [
    ([0, 1, 2], []), ([0, 1, 3], [1]), ([0, 1, 4], [0, 1, 0, 1, 0, 0, 1, 0, 1]),
    ([0, 1, 5], [0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]), ([0, 2, 3], [1, 0, 0, 0, 1, 0, 0, 0, 0]),
    ([0, 2, 4], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]),
    ([0, 2, 6], [1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0]), ([0, 3, 5], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]),
    ([0, 3, 6], [0, 1, 0, 1, 0, 0, 0, 1]), ([0, 4, 5], [1, 0, 1, 0, 1, 0, 0, 1, 0]),
    ([0, 4, 6], [0, 1, 0, 0, 1, 0, 0, 0, 1, 0]), ([0, 5, 6], [1, 0, 0, 1, 0, 0, 1, 0]),
    ([1, 2, 3], [0, 0, 0, 1, 0, 0, 0, 0]), ([1, 2, 5], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0]),
    ([1, 2, 6], [0, 0, 1, 0, 0, 1, 0, 1]), ([1, 3, 4], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]),
    ([1, 3, 6], [0, 0, 1, 0, 1, 0, 0, 1, 0, 0]), ([1, 4, 5], [0, 1, 0, 1, 0, 0, 1, 0]),
    ([1, 4, 6], [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0]), ([1, 5, 6], [0, 0, 1, 0, 0, 1, 0]),
    ([2, 3, 4], [0, 0, 1, 0, 0, 0, 1]), ([2, 3, 5], [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0]),
    ([2, 4, 5], [1, 0, 0, 1, 0, 0, 0]), ([2, 4, 6], [0, 0, 0, 1, 0, 0, 0, 1, 0]),
    ([2, 5, 6], [1, 0, 1, 0, 1, 0, 0, 0]), ([3, 4, 5], [0, 0, 1, 0, 0, 0]),
    ([3, 4, 6], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), ([3, 5, 6], [0, 1, 0, 1, 0, 0, 0])])]

@[expose] def fanoBase (i : Fin 8) : Finset (Fin 8) := ((frameFanoData.getD i ([], [])).1).toFinset

@[expose] def fanoPairs (i : Fin 8) : List (List (Fin 8) × List (Fin 2)) :=
  (frameFanoData.getD i ([], [])).2

theorem fano_words : ∀ i : Fin 8, ∀ p ∈ fanoPairs i,
    frameWord p.2 i = i ∧ (fanoBase i).image (frameWord p.2) = p.1.toFinset := by
  decide +kernel

theorem fano_cover : ∀ i : Fin 8, ∀ T ∈ (univ.erase i).powersetCard 3,
    insert i T ∉ frameBlocks → ∃ p ∈ fanoPairs i, p.1.toFinset = T := by
  decide +kernel

theorem fano_card : ∀ i : Fin 8, 28 ≤ ((fanoPairs i).map fun p => p.1.toFinset).toFinset.card := by
  decide +kernel

theorem fano_lines : ∀ i : Fin 8,
    (((univ.erase i).powersetCard 3).filter fun T => insert i T ∈ frameBlocks).card = 7 := by
  decide +kernel

theorem frameBlocks_through : ∀ j : Fin 8, (frameBlocks.filter fun B => j ∈ B).card = 7 := by
  decide +kernel

theorem card_frameBlocks : frameBlocks.card = 14 := by decide +kernel

theorem card_of_mem_frameBlocks : ∀ B ∈ frameBlocks, B.card = 4 := by decide +kernel

@[expose] def optBlocks : Finset (Finset (Option (Fin 8))) :=
  frameBlocks.image (Finset.map Function.Embedding.some)

theorem card_optBlocks : optBlocks.card = 14 := by
  rw [optBlocks, card_image_of_injective _ (map_injective _), card_frameBlocks]

theorem mem_optBlocks {B : Finset (Option (Fin 8))} :
    B ∈ optBlocks ↔ ∃ B₀ ∈ frameBlocks, B₀.map Function.Embedding.some = B := mem_image

theorem props_of_mem_optBlocks {B : Finset (Option (Fin 8))} (hB : B ∈ optBlocks) :
    none ∉ B ∧ B.card = 4 := by
  obtain ⟨B₀, hB₀, rfl⟩ := mem_optBlocks.mp hB
  refine ⟨by simp, ?_⟩
  rw [card_map, card_of_mem_frameBlocks B₀ hB₀]

structure NineAction (N : Type*) [Group N] [MulAction N (Option (Fin 8))] : Prop where
  trans : ∀ i : Fin 8, ∃ n : N, n • (none : Option (Fin 8)) = some i
  up : ∀ n : N, n • (none : Option (Fin 8)) = none →
    ∃ σ ∈ frameAut, ∀ i, n • (some i : Option (Fin 8)) = some (σ i)
  gen : ∀ σ ∈ frameGens, ∃ n : N, n • (none : Option (Fin 8)) = none ∧
    ∀ i, n • (some i : Option (Fin 8)) = some (σ i)

@[expose] def nineRealized (N : Type*) [Group N] [MulAction N (Option (Fin 8))] :
    Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∃ n : N, n • (none : Option (Fin 8)) = none ∧
    ∀ i, n • (some i : Option (Fin 8)) = some (σ i)}
  mul_mem' := by
    rintro σ τ ⟨n, hn0, hn⟩ ⟨m, hm0, hm⟩
    exact ⟨n * m, by rw [mul_smul, hm0, hn0], fun i => by rw [mul_smul, hm, hn]; rfl⟩
  one_mem' := ⟨1, one_smul _ _, fun i => one_smul _ _⟩
  inv_mem' := by
    rintro σ ⟨n, hn0, hn⟩
    refine ⟨n⁻¹, by rw [inv_smul_eq_iff, hn0], fun i => ?_⟩
    rw [inv_smul_eq_iff, hn]
    simp

namespace NineAction

variable {N : Type*} [Group N] [MulAction N (Option (Fin 8))] (h : NineAction N)
include h

theorem exists_smul_none (p : Option (Fin 8)) : ∃ n : N, n • (none : Option (Fin 8)) = p := by
  cases p with
  | none => exact ⟨1, one_smul _ _⟩
  | some i => exact h.trans i

noncomputable def choice (p : Option (Fin 8)) : N := (h.exists_smul_none p).choose

theorem choice_spec (p : Option (Fin 8)) : h.choice p • (none : Option (Fin 8)) = p :=
  (h.exists_smul_none p).choose_spec

noncomputable def blocksAt (p : Option (Fin 8)) : Finset (Finset (Option (Fin 8))) :=
  optBlocks.image fun B => B.image (h.choice p • ·)

omit h in
theorem image_smul_injective (n : N) :
    Function.Injective fun B : Finset (Option (Fin 8)) => B.image (n • ·) :=
  image_injective (MulAction.injective n)

theorem image_optBlocks_of_fix {g : N} (hg : g • (none : Option (Fin 8)) = none) :
    (optBlocks.image fun B => B.image (g • ·)) = optBlocks := by
  obtain ⟨σ, hσ, hgσ⟩ := h.up g hg
  apply eq_of_subset_of_card_le
  · intro B hB
    obtain ⟨B₁, hB₁, rfl⟩ := mem_image.mp hB
    obtain ⟨B₀, hB₀, rfl⟩ := mem_optBlocks.mp hB₁
    refine mem_optBlocks.mpr ⟨B₀.map σ.toEmbedding, hσ B₀ hB₀, ?_⟩
    ext x
    simp only [mem_map, mem_image, Function.Embedding.some_apply, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨some b, ⟨b, hb, rfl⟩, by rw [hgσ]⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨σ b, ⟨b, hb, rfl⟩, by rw [hgσ]⟩
  · rw [card_image_of_injective _ (image_smul_injective g)]

theorem blocksAt_eq {n : N} {p : Option (Fin 8)} (hn : n • (none : Option (Fin 8)) = p) :
    h.blocksAt p = optBlocks.image fun B => B.image (n • ·) := by
  set m := h.choice p
  have hg : (m⁻¹ * n) • (none : Option (Fin 8)) = none := by
    rw [mul_smul, hn, ← h.choice_spec p, inv_smul_smul]
  have key : (optBlocks.image fun B => B.image (n • ·)) =
      (optBlocks.image fun B => B.image ((m⁻¹ * n) • ·)).image fun B => B.image (m • ·) := by
    rw [image_image]
    refine image_congr fun B _ => ?_
    simp only [Function.comp, image_image]
    refine image_congr fun x _ => ?_
    simp only [Function.comp, mul_smul, smul_inv_smul]
  rw [key, h.image_optBlocks_of_fix hg]
  rfl

theorem blocksAt_none : h.blocksAt none = optBlocks := by
  rw [h.blocksAt_eq (one_smul N none)]
  simp only [one_smul, image_id']

theorem mem_blocksAt_smul (g : N) (p : Option (Fin 8)) (B : Finset (Option (Fin 8))) :
    B.image (g • ·) ∈ h.blocksAt (g • p) ↔ B ∈ h.blocksAt p := by
  have hgp : (g * h.choice p) • (none : Option (Fin 8)) = g • p := by
    rw [mul_smul, h.choice_spec]
  have heq : h.blocksAt (g • p) = (h.blocksAt p).image fun B => B.image (g • ·) := by
    rw [h.blocksAt_eq hgp, blocksAt, image_image]
    refine image_congr fun B _ => ?_
    simp only [Function.comp, image_image]
    refine image_congr fun x _ => ?_
    simp only [Function.comp, mul_smul]
  rw [heq]
  exact (image_smul_injective g).mem_finset_image

theorem card_blocksAt (p : Option (Fin 8)) : (h.blocksAt p).card = 14 := by
  rw [blocksAt, card_image_of_injective _ (image_smul_injective _), card_optBlocks]

theorem props_of_mem_blocksAt {p : Option (Fin 8)} {B : Finset (Option (Fin 8))}
    (hB : B ∈ h.blocksAt p) : p ∉ B ∧ B.card = 4 := by
  obtain ⟨B₀, hB₀, rfl⟩ := mem_image.mp hB
  have h₀ := props_of_mem_optBlocks hB₀
  refine ⟨?_, ?_⟩
  · intro hp
    obtain ⟨x, hx, hxp⟩ := mem_image.mp hp
    have hx' : h.choice p • x = h.choice p • none := hxp.trans (h.choice_spec p).symm
    exact h₀.1 (MulAction.injective _ hx' ▸ hx)
  · rw [card_image_of_injective _ (MulAction.injective _), h₀.2]

theorem frameWord_mem_realized (w : List (Fin 2)) : frameWord w ∈ nineRealized N :=
  (Subgroup.closure_le (nineRealized N)).2 h.gen (frameWord_mem_closure w)

theorem insertNone_mem_blocksAt_iff (i : Fin 8) :
    ∀ T ∈ (univ.erase i).powersetCard 3,
      (insertNone T ∈ h.blocksAt (some i) ↔ insert i T ∈ frameBlocks) := by
  classical
  set A := ((univ.erase i).powersetCard 3).filter fun T => insertNone T ∈ h.blocksAt (some i)
  set L := ((univ.erase i).powersetCard 3).filter fun T => insert i T ∈ frameBlocks
  set m := h.choice (some i)
  have hm : m • (none : Option (Fin 8)) = some i := h.choice_spec _
  obtain ⟨j, hj⟩ : ∃ j, m⁻¹ • (none : Option (Fin 8)) = some j := by
    cases hq : m⁻¹ • (none : Option (Fin 8)) with
    | none =>
      exfalso
      have h' := congrArg (m • ·) hq
      simp only [smul_inv_smul, hm] at h'
      exact absurd h' (by simp)
    | some j => exact ⟨j, rfl⟩
  have hA : A.card = 7 := by
    have h1 : A.card = ((h.blocksAt (some i)).filter fun B => none ∈ B).card := by
      apply card_nbij' insertNone eraseNone
      · intro T hT
        simp only [A, coe_filter, Set.mem_ofPred_eq] at hT ⊢
        exact ⟨hT.2, none_mem_insertNone⟩
      · intro B hB
        simp only [A, coe_filter, Set.mem_ofPred_eq] at hB ⊢
        obtain ⟨hB1, hB2⟩ := hB
        have hpr := h.props_of_mem_blocksAt hB1
        refine ⟨mem_powersetCard.mpr ⟨fun x hx => ?_, ?_⟩, ?_⟩
        · rw [mem_eraseNone] at hx
          exact mem_erase.mpr ⟨fun hxi => hpr.1 (hxi ▸ hx), mem_univ _⟩
        · rw [card_eraseNone_of_mem hB2, hpr.2]
        · rw [insertNone_eraseNone, insert_eq_of_mem hB2]
          exact hB1
      · intro T _
        exact eraseNone_insertNone T
      · intro B hB
        simp only [coe_filter, Set.mem_ofPred_eq] at hB
        rw [insertNone_eraseNone, insert_eq_of_mem hB.2]
    have h2 : ((h.blocksAt (some i)).filter fun B => none ∈ B).card =
        (optBlocks.filter fun B => some j ∈ B).card := by
      rw [h.blocksAt_eq hm, filter_image, card_image_of_injective _ (image_smul_injective m)]
      refine congrArg card (filter_congr fun B _ => ?_)
      constructor
      · intro hB
        obtain ⟨x, hx, hmx⟩ := mem_image.mp hB
        have hx' : x = m⁻¹ • (none : Option (Fin 8)) := by rw [← hmx, inv_smul_smul]
        rwa [hx', hj] at hx
      · intro hjB
        exact mem_image.mpr ⟨some j, hjB, by rw [← hj, smul_inv_smul]⟩
    have h3 : (optBlocks.filter fun B => some j ∈ B).card =
        (frameBlocks.filter fun B => j ∈ B).card := by
      rw [optBlocks, filter_image, card_image_of_injective _ (map_injective _)]
      refine congrArg card (filter_congr fun B _ => ?_)
      simp
    rw [h1, h2, h3, frameBlocks_through j]
  have hinv : ∀ σ ∈ nineRealized N, σ i = i → ∀ T ∈ A, T.image σ ∈ A := by
    rintro σ ⟨g, hg0, hgσ⟩ hσi T hT
    simp only [A, mem_filter, mem_powersetCard] at hT ⊢
    obtain ⟨⟨hTsub, hTcard⟩, hTB⟩ := hT
    refine ⟨⟨fun x hx => ?_, ?_⟩, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      have hyi : y ≠ i := (mem_erase.mp (hTsub hy)).1
      exact mem_erase.mpr ⟨fun e => hyi (σ.injective (e.trans hσi.symm)), mem_univ _⟩
    · rw [card_image_of_injective _ σ.injective, hTcard]
    · have himg : (insertNone T).image (g • ·) = insertNone (T.image σ) := by
        ext x
        cases x with
        | none =>
          simp only [mem_image, none_mem_insertNone, iff_true]
          exact ⟨none, none_mem_insertNone, hg0⟩
        | some k =>
          simp only [mem_image, some_mem_insertNone]
          constructor
          · rintro ⟨y, hy, hyk⟩
            cases y with
            | none => rw [hg0] at hyk; exact absurd hyk (by simp)
            | some l =>
              rw [hgσ] at hyk
              exact ⟨l, some_mem_insertNone.mp hy, Option.some_injective _ hyk⟩
          · rintro ⟨l, hl, rfl⟩
            exact ⟨some l, some_mem_insertNone.mpr hl, hgσ l⟩
      rw [← himg]
      have h' := (h.mem_blocksAt_smul g (some i) (insertNone T)).mpr hTB
      rwa [hgσ, hσi] at h'
  have hsub : A ⊆ L := by
    intro T₁ hT₁
    by_contra hT₁L
    have hT₁' := (mem_filter.mp hT₁).1
    have hnl : insert i T₁ ∉ frameBlocks := fun hb => hT₁L (mem_filter.mpr ⟨hT₁', hb⟩)
    obtain ⟨p₁, hp₁, hp₁T⟩ := fano_cover i T₁ hT₁' hnl
    obtain ⟨hw₁i, hw₁T⟩ := fano_words i p₁ hp₁
    have hT₀ : fanoBase i ∈ A := by
      have hσi : (frameWord p₁.2)⁻¹ i = i := by
        rw [Equiv.Perm.inv_eq_iff_eq, hw₁i]
      have h' := hinv _ (inv_mem (h.frameWord_mem_realized _)) hσi T₁ hT₁
      have hback : ((fanoBase i).image (frameWord p₁.2)).image ⇑(frameWord p₁.2)⁻¹ =
          fanoBase i := by
        rw [image_image]
        simp [Function.comp_def]
      rwa [← hp₁T, ← hw₁T, hback] at h'
    have hall : ((fanoPairs i).map fun p => p.1.toFinset).toFinset ⊆ A := by
      intro T hT
      simp only [List.mem_toFinset, List.mem_map] at hT
      obtain ⟨p, hp, rfl⟩ := hT
      obtain ⟨hwi, hwT⟩ := fano_words i p hp
      rw [← hwT]
      exact hinv _ (h.frameWord_mem_realized _) hwi _ hT₀
    have h1 := card_le_card hall
    have h2 := fano_card i
    omega
  have hAL : A = L := eq_of_subset_of_card_le hsub (by rw [hA, fano_lines i])
  intro T hT
  have hA' : T ∈ A ↔ T ∈ L := by rw [hAL]
  simp only [A, L, mem_filter, hT, true_and] at hA'
  exact hA'

theorem mem_blocksAt_none_iff (i : Fin 8) {ℓ : Finset (Option (Fin 8))} (h0 : none ∉ ℓ)
    (hi : some i ∉ ℓ) (hℓ : ℓ.card = 3) :
    insert none ℓ ∈ h.blocksAt (some i) ↔ insert (some i) ℓ ∈ h.blocksAt none := by
  classical
  set T := eraseNone ℓ
  have hTℓ : T.map Function.Embedding.some = ℓ := by
    rw [map_some_eraseNone, erase_eq_of_notMem h0]
  have hT : T ∈ (univ.erase i).powersetCard 3 := by
    refine mem_powersetCard.mpr ⟨fun x hx => ?_, ?_⟩
    · rw [mem_eraseNone] at hx
      exact mem_erase.mpr ⟨fun hxi => hi (hxi ▸ hx), mem_univ _⟩
    · rw [card_eraseNone_of_not_mem h0, hℓ]
  have h1 : insert none ℓ = insertNone T := by rw [insertNone_eraseNone]
  rw [h1, h.insertNone_mem_blocksAt_iff i T hT, h.blocksAt_none, mem_optBlocks]
  constructor
  · intro hb
    refine ⟨insert i T, hb, ?_⟩
    rw [map_insert, hTℓ]
    rfl
  · rintro ⟨B₀, hB₀, hB₀ℓ⟩
    have : B₀ = insert i T := by
      apply map_injective Function.Embedding.some
      rw [hB₀ℓ, map_insert, hTℓ]
      rfl
    rwa [← this]

theorem mem_blocksAt_symm {p q : Option (Fin 8)} (hpq : p ≠ q) {ℓ : Finset (Option (Fin 8))}
    (hp : p ∉ ℓ) (hq : q ∉ ℓ) (hℓ : ℓ.card = 3) (hB : insert q ℓ ∈ h.blocksAt p) :
    insert p ℓ ∈ h.blocksAt q := by
  classical
  set m := h.choice q
  have hm : m • (none : Option (Fin 8)) = q := h.choice_spec q
  set ℓ' := ℓ.image (m⁻¹ • ·)
  have hmq : m⁻¹ • q = none := by rw [← hm, inv_smul_smul]
  obtain ⟨i, hi⟩ : ∃ i, m⁻¹ • p = some i := by
    cases hp' : m⁻¹ • p with
    | none =>
      exfalso
      exact hpq (by rw [← smul_inv_smul m p, hp', ← hmq, smul_inv_smul])
    | some i => exact ⟨i, rfl⟩
  have hinj := MulAction.injective (α := N) (β := Option (Fin 8)) m⁻¹
  have h0' : none ∉ ℓ' := by
    rw [← hmq]
    exact fun hx => hq ((hinj.mem_finset_image).mp hx)
  have hi' : some i ∉ ℓ' := by
    rw [← hi]
    exact fun hx => hp ((hinj.mem_finset_image).mp hx)
  have hℓ' : ℓ'.card = 3 := by rw [card_image_of_injective _ hinj, hℓ]
  have hB' : insert none ℓ' ∈ h.blocksAt (some i) := by
    rw [← hi, ← hmq, ← image_insert]
    exact (h.mem_blocksAt_smul m⁻¹ p _).mpr hB
  have hC := (h.mem_blocksAt_none_iff i h0' hi' hℓ').mp hB'
  have hC' := (h.mem_blocksAt_smul m none _).mpr hC
  have himg : (insert (some i) ℓ').image (m • ·) = insert p ℓ := by
    rw [image_insert, ← hi, smul_inv_smul, image_image]
    simp [Function.comp_def]
  rwa [hm, himg] at hC'

theorem false : False := by
  classical
  set S : Finset (Finset (Option (Fin 8))) :=
    univ.filter fun S => S.card = 5 ∧ ∀ r ∈ S, S.erase r ∈ h.blocksAt r
  have hfiber : ∀ r : Option (Fin 8), (S.filter fun T => r ∈ T).card = 14 := by
    intro r
    rw [← h.card_blocksAt r]
    apply card_nbij' (fun T => T.erase r) (fun B => insert r B)
    · intro T hT
      simp only [S, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hT
      exact hT.1.2 r hT.2
    · intro B hB
      have hpr := h.props_of_mem_blocksAt hB
      simp only [S, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨⟨by rw [card_insert_of_notMem hpr.1, hpr.2], fun r' hr' => ?_⟩,
        mem_insert_self _ _⟩
      rcases mem_insert.mp hr' with rfl | hr'B
      · rw [erase_insert hpr.1]
        exact hB
      · have hne : r ≠ r' := fun e => hpr.1 (e ▸ hr'B)
        rw [erase_insert_of_ne hne]
        have hℓ : (B.erase r').card = 3 := by rw [card_erase_of_mem hr'B, hpr.2]
        refine h.mem_blocksAt_symm hne (fun hx => hpr.1 (mem_of_mem_erase hx))
          (notMem_erase r' B) hℓ ?_
        rwa [insert_erase hr'B]
    · intro T hT
      simp only [S, coe_filter, mem_filter, Set.mem_ofPred_eq] at hT
      exact insert_erase hT.2
    · intro B hB
      exact erase_insert (h.props_of_mem_blocksAt hB).1
  have hcount := card_mul_eq_card_mul (fun T (x : Option (Fin 8)) => x ∈ T) (s := S)
    (t := univ) (m := 5) (n := 14) (fun T hT => ?_) (fun x _ => ?_)
  · rw [card_univ, Fintype.card_option, Fintype.card_fin] at hcount
    omega
  · simp only [S, mem_filter, mem_univ, true_and] at hT
    rw [← hT.1]
    simp [bipartiteAbove]
  · exact hfiber x

end NineAction

theorem not_nineAction {N : Type*} [Group N] [MulAction N (Option (Fin 8))] :
    ¬ NineAction N := fun h => h.false

theorem not_frame_orbit_nine {N : Type*} [Group N] [MulAction N FrameVec] (u : Fin 8 → FrameVec)
    (hu : Function.Injective u) (hzu : ∀ i, u i ≠ frameZ)
    (hperm : ∀ σ i, permVec σ (u i) = u (σ i))
    (horb : ∀ v, v ∈ MulAction.orbit N frameZ ↔ v = frameZ ∨ ∃ i, u i = v)
    (hup : ∀ n : N, n • frameZ = frameZ → ∃ σ ∈ frameAut, ∀ v, n • v = permVec σ v)
    (hgen : ∀ σ ∈ frameGens, ∃ n : N, ∀ v, n • v = permVec σ v) : False := by
  classical
  let pt : Option (Fin 8) → FrameVec := fun x => x.elim frameZ u
  let idx : FrameVec → Option (Fin 8) := fun v => if h : ∃ i, u i = v then some h.choose else none
  have idx_u : ∀ i, idx (u i) = some i := by
    intro i
    simp only [idx]
    split_ifs with h'
    · exact congrArg some (hu h'.choose_spec)
    · exact absurd ⟨i, rfl⟩ h'
  have idx_z : idx frameZ = none := by
    simp only [idx]
    split_ifs with h'
    · obtain ⟨j, hj⟩ := h'
      exact absurd hj (hzu j)
    · rfl
  have idx_pt : ∀ x, idx (pt x) = x := by
    intro x
    cases x with
    | none => exact idx_z
    | some i => exact idx_u i
  have hptmem : ∀ x, pt x ∈ MulAction.orbit N frameZ := by
    intro x
    cases x with
    | none => exact MulAction.mem_orbit_self _
    | some i => exact (horb _).mpr (Or.inr ⟨i, rfl⟩)
  have pt_idx : ∀ v ∈ MulAction.orbit N frameZ, pt (idx v) = v := by
    intro v hv
    rcases (horb v).mp hv with rfl | ⟨i, rfl⟩
    · rw [idx_z]
      rfl
    · rw [idx_u]
      rfl
  have hsmem : ∀ (n : N) (x : Option (Fin 8)), n • pt x ∈ MulAction.orbit N frameZ := by
    intro n x
    obtain ⟨m, hm⟩ := hptmem x
    change m • frameZ = pt x at hm
    exact ⟨n * m, by change (n * m) • frameZ = n • pt x; rw [mul_smul, hm]⟩
  let _ : MulAction N (Option (Fin 8)) :=
    { smul := fun n x => idx (n • pt x)
      one_smul := fun x => by
        change idx ((1 : N) • pt x) = x
        rw [one_smul, idx_pt]
      mul_smul := fun n m x => by
        change idx ((n * m) • pt x) = idx (n • pt (idx (m • pt x)))
        rw [pt_idx _ (hsmem m x), mul_smul] }
  have hsmul : ∀ (n : N) (x : Option (Fin 8)), n • x = idx (n • pt x) := fun _ _ => rfl
  refine not_nineAction (N := N) ⟨fun i => ?_, fun n hn => ?_, fun σ hσ => ?_⟩
  · obtain ⟨n, hn⟩ := (horb (u i)).mpr (Or.inr ⟨i, rfl⟩)
    change n • frameZ = u i at hn
    exact ⟨n, by rw [hsmul]; change idx (n • frameZ) = _; rw [hn, idx_u]⟩
  · have hz : n • frameZ = frameZ := by
      have h1 := pt_idx _ (hsmem n none)
      rw [← hsmul, hn] at h1
      exact h1.symm
    obtain ⟨σ, hσ, hnσ⟩ := hup n hz
    exact ⟨σ, hσ, fun i => by rw [hsmul]; change idx (n • u i) = _; rw [hnσ, hperm, idx_u]⟩
  · obtain ⟨n, hn⟩ := hgen σ hσ
    refine ⟨n, ?_, fun i => ?_⟩
    · rw [hsmul]
      change idx (n • frameZ) = _
      rw [hn, permVec_frameZ, idx_z]
    · rw [hsmul]
      change idx (n • u i) = _
      rw [hn, hperm, idx_u]

theorem frameNine_iff : ∀ n < 256, (frameClass n = 1 ∨ frameClass n = 9) ↔
    (frameDecode n = frameZ ∨ ∃ i, frameE i = frameDecode n) := by
  decide +kernel

theorem frameNine'_iff : ∀ n < 256, (frameClass n = 8 ∨ frameClass n = 9) ↔
    (frameDecode n = frameZ ∨ ∃ i, frameZ + frameE i = frameDecode n) := by
  decide +kernel

theorem frameE_injective : Function.Injective frameE := by
  have key : ∀ i j : Fin 8, frameE i = frameE j → i = j := by decide
  exact fun i j h => key i j h

theorem frameE_ne_frameZ : ∀ i, frameE i ≠ frameZ := by decide

theorem orbit_ne_frameNine {N : Type*} [Group N] [MulAction N FrameVec]
    (hup : ∀ n : N, n • frameZ = frameZ → ∃ σ ∈ frameAut, ∀ v, n • v = permVec σ v)
    (hgen : ∀ σ ∈ frameGens, ∃ n : N, ∀ v, n • v = permVec σ v) :
    MulAction.orbit N frameZ ≠ frameNine := by
  intro horb
  refine not_frame_orbit_nine frameE frameE_injective frameE_ne_frameZ permVec_frameE
    (fun v => ?_) hup hgen
  rw [horb, frameNine, Set.mem_ofPred_eq, frameCls, ← frameDecode_frameEncode v]
  rw [frameEncode_frameDecode _ (frameEncode_lt v)]
  exact frameNine_iff _ (frameEncode_lt v)

theorem orbit_ne_frameNine' {N : Type*} [Group N] [MulAction N FrameVec]
    (hup : ∀ n : N, n • frameZ = frameZ → ∃ σ ∈ frameAut, ∀ v, n • v = permVec σ v)
    (hgen : ∀ σ ∈ frameGens, ∃ n : N, ∀ v, n • v = permVec σ v) :
    MulAction.orbit N frameZ ≠ frameNine' := by
  intro horb
  refine not_frame_orbit_nine (fun i => frameZ + frameE i)
    (fun i j h => frameE_injective (add_left_cancel h)) (fun i h => ?_)
    (fun σ i => by rw [permVec_add, permVec_frameZ, permVec_frameE]) (fun v => ?_) hup hgen
  · have h' : frameE i = 0 := by
      have := congrArg (· - frameZ) h
      simpa using this
    have := congrFun h' i
    simp only [frameE, ite_true, Pi.zero_apply] at this
    exact absurd this (by decide)
  · rw [horb, frameNine', Set.mem_ofPred_eq, frameCls, ← frameDecode_frameEncode v]
    rw [frameEncode_frameDecode _ (frameEncode_lt v)]
    exact frameNine'_iff _ (frameEncode_lt v)

end CFSG.EvenSmallLie.OmegaEight
