module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8Basic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassCascade
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEClasses

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def classListE8CascPos : List ℕ := [238, 192, 116, 57, 6, 1, 2, 4]

@[expose] def classListE8RepPos : ℕ → List ℕ
  | 0 => [238]
  | 1 => [225, 224]
  | 2 => [206, 207, 208]
  | _ => [192, 193, 195, 194]

@[expose] def classListE8Patterns : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(192, 116, 7, 6, 238),
    (192, 57, 35, 4, 238),
    (192, 1, 63, 2, 238),
    (116, 57, 85, 1, 238),
    (116, 2, 113, 4, 238),
    (57, 6, 139, 2, 238),
    (6, 1, 161, 4, 238),
    (116, 57, 0, 2, 192),
    (116, 1, 24, 4, 192),
    (57, 6, 54, 1, 192),
    (6, 2, 83, 4, 192),
    (57, 6, 5, 4, 116),
    (6, 1, 31, 2, 116),
    (1, 2, 3, 4, 57)]

@[expose] def classListE8Words : List (List ℕ × List ℕ × ℕ) :=
  [([238], [], 0),
    ([192], [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7], 0),
    ([238, 192], [7, 6, 5, 4, 3, 1], 1),
    ([116], [7, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7], 0),
    ([238, 116], [7, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0], 1),
    ([192, 116], [7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 1, 3, 2, 1, 0], 1),
    ([238, 192, 116], [7, 6, 5, 0, 2, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([57], [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7], 0),
    ([238, 57], [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0], 1),
    ([192, 57], [5, 6, 7, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 1, 3, 2, 1, 0], 1),
    ([238, 192, 57], [5, 6, 7, 4, 5, 6, 5, 0, 2, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([116, 57], [0, 2, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 2, 1, 3,
      2, 1, 0], 1),
    ([238, 116, 57], [0, 2, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 5, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([192, 116, 57], [7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 0, 2, 1, 3, 4, 5, 6, 4, 2, 3, 0, 2, 0],
      2),
    ([238, 192, 116, 57], [7, 5, 6, 0, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 0, 2, 0], 3),
    ([6], [7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7], 0),
    ([238, 6], [7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0], 1),
    ([192, 6], [7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 1, 3, 2,
      1, 0], 1),
    ([238, 192, 6], [7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 0, 2, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([116, 6], [7, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0,
      2, 1, 3, 4, 2, 1, 3, 2, 1, 0], 1),
    ([238, 116, 6], [7, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 0, 2, 3, 4, 3, 2, 1,
      3, 0, 2, 0], 2),
    ([192, 116, 6], [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4,
      5, 6, 5, 0, 2, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([57, 6], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2,
      3, 4, 1, 3, 2, 0], 1),
    ([238, 57, 6], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 0],
      2),
    ([192, 57, 6], [7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6,
      2, 3, 4, 0], 2),
    ([238, 192, 57, 6], [7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 0],
      3),
    ([116, 57, 6], [7, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0,
      2, 1, 3, 4, 5, 6, 3, 2], 2),
    ([238, 116, 57, 6], [7, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 2, 3, 4, 1,
      3, 1, 0], 3),
    ([192, 116, 57, 6], [7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2,
      1, 3, 4, 3, 2, 1, 3, 2, 1], 3),
    ([1], [3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7], 0),
    ([238, 1], [3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0], 1),
    ([192, 1], [3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 1, 3, 2,
      1, 0], 1),
    ([238, 192, 1], [3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 5, 0, 2, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([116, 1], [0, 2, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4,
      2, 1, 3, 2, 1, 0], 1),
    ([238, 116, 1], [0, 2, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 3, 2, 1, 3, 0, 2, 0],
      2),
    ([192, 116, 1], [7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 4, 2,
      3, 0, 2, 0], 2),
    ([238, 192, 116, 1], [3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 0],
      3),
    ([57, 1], [0, 2, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5,
      0, 2, 3, 4, 2, 1, 3, 2, 1, 0], 1),
    ([238, 57, 1], [0, 2, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 3, 2, 1,
      3, 0, 2, 0], 2),
    ([192, 57, 1], [7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4,
      5, 6, 4, 2, 3, 0, 2, 0], 2),
    ([238, 192, 57, 1], [5, 6, 7, 0, 2, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 1, 3, 0,
      2, 1, 0], 3),
    ([116, 57, 1], [0, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2,
      3, 0, 2, 1, 3, 4, 5, 6, 4, 2, 3, 0, 2, 0], 2),
    ([192, 116, 57, 1], [0, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 1, 3, 4, 5, 3, 2,
      1, 3, 4, 3, 2, 1, 3, 2, 1], 3),
    ([6, 1], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3,
      4, 5, 0, 2, 3, 4, 1, 3, 2, 0], 1),
    ([238, 6, 1], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1,
      3, 4, 0], 2),
    ([192, 6, 1], [7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3,
      4, 5, 6, 2, 3, 4, 0], 2),
    ([238, 192, 6, 1], [7, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0,
      2, 1, 0], 3),
    ([116, 6, 1], [7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 1, 3, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2], 2),
    ([238, 116, 6, 1], [7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 2, 1,
      3, 4, 2, 1, 3, 1, 0], 3),
    ([192, 116, 6, 1], [7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 2,
      3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 2, 1], 3),
    ([57, 6, 1], [7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1,
      3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2], 2),
    ([238, 57, 6, 1], [0, 2, 3, 4, 5, 6, 7, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 5,
      2, 1, 3, 4, 2, 1, 3, 1, 0], 3),
    ([116, 57, 6, 1], [0, 2, 3, 4, 5, 6, 7, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2,
      1, 3, 4, 5, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 1], 3),
    ([2], [3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7], 0),
    ([238, 2], [3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0], 1),
    ([192, 2], [3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 1, 3, 2,
      1, 0], 1),
    ([238, 192, 2], [3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 5, 0, 2, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([116, 2], [3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4,
      2, 1, 3, 2, 1, 0], 1),
    ([238, 116, 2], [3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 5, 3, 4, 3, 2, 1, 3, 0, 2, 0],
      2),
    ([192, 116, 2], [7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 2,
      3, 0, 2, 0], 2),
    ([238, 192, 116, 2], [3, 4, 5, 6, 7, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 1, 0],
      3),
    ([57, 2], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5,
      0, 2, 3, 4, 2, 1, 3, 2, 1, 0], 1),
    ([238, 57, 2], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 3, 4, 3, 2, 1,
      3, 0, 2, 0], 2),
    ([192, 57, 2], [7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4,
      5, 6, 4, 2, 3, 0, 2, 0], 2),
    ([238, 192, 57, 2], [5, 6, 7, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 3, 4, 1, 3, 0,
      2, 1, 0], 3),
    ([116, 57, 2], [7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2,
      3, 0, 2, 1, 3, 4, 5, 6, 4, 2, 3, 0, 2, 0], 2),
    ([238, 116, 57, 2], [0, 2, 3, 4, 5, 6, 7, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3,
      4, 3, 2, 1, 3, 0, 2, 1, 0], 3),
    ([6, 2], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3,
      4, 5, 0, 2, 3, 4, 1, 3, 2, 0], 1),
    ([238, 6, 2], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1,
      3, 4, 0], 2),
    ([192, 6, 2], [7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3,
      4, 5, 6, 2, 3, 4, 0], 2),
    ([238, 192, 6, 2], [7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0,
      2, 1, 0], 3),
    ([116, 6, 2], [7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2], 2),
    ([238, 116, 6, 2], [7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 2,
      3, 4, 2, 1, 3, 1, 0], 3),
    ([192, 116, 6, 2], [7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2,
      3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 2, 1], 3),
    ([57, 6, 2], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1,
      3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2], 2),
    ([192, 57, 6, 2], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4,
      5, 2, 1, 3, 4, 2, 1, 3, 1], 3),
    ([116, 57, 6, 2], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2,
      1, 3, 4, 5, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 1], 3),
    ([1, 2], [3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3,
      4, 5, 0, 2, 3, 4, 1, 3, 2, 0], 1),
    ([238, 1, 2], [3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1,
      3, 4, 0], 2),
    ([192, 1, 2], [3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 0], 2),
    ([116, 1, 2], [7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3,
      0, 2, 1, 3, 4, 5, 6], 2),
    ([238, 116, 1, 2], [3, 4, 5, 6, 7, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4,
      3, 1, 0], 3),
    ([192, 116, 1, 2], [3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 1, 3, 4, 2, 3, 0, 2, 1, 3,
      4, 5, 1, 3, 4, 2, 3, 2, 1], 3),
    ([57, 1, 2], [5, 6, 7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5,
      3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6], 2),
    ([238, 57, 1, 2], [3, 4, 5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6,
      5, 3, 4, 2, 3, 1, 0], 3),
    ([192, 57, 1, 2], [3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3, 2, 1], 3),
    ([116, 57, 1, 2], [0, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 1, 3, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 1], 3),
    ([6, 1, 2], [7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 2, 3, 4,
      5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6], 2),
    ([238, 6, 1, 2], [3, 4, 5, 6, 7, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4,
      5, 1, 3, 4, 2, 3, 1, 0], 3),
    ([192, 6, 1, 2], [3, 4, 5, 6, 7, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 3, 2, 1, 3, 4, 0, 2, 3, 2, 1], 3),
    ([57, 6, 1, 2], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 2, 3,
      0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1], 3),
    ([4], [5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7], 0),
    ([238, 4], [5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0], 1),
    ([192, 4], [5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 1, 3, 2,
      1, 0], 1),
    ([238, 192, 4], [5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 5, 0, 2, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([116, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4,
      2, 1, 3, 2, 1, 0], 1),
    ([238, 116, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 3, 2, 1, 3, 0, 2, 0],
      2),
    ([192, 116, 4], [7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 2,
      3, 0, 2, 0], 2),
    ([238, 192, 116, 4], [5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 0],
      3),
    ([57, 4], [5, 6, 7, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5,
      0, 2, 3, 4, 2, 1, 3, 2, 1, 0], 1),
    ([238, 57, 4], [5, 6, 7, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 3, 2, 1,
      3, 0, 2, 0], 2),
    ([192, 57, 4], [5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 6, 5, 3, 4, 3, 2, 1, 3, 0, 2, 0], 2),
    ([116, 57, 4], [7, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0,
      2, 1, 3, 4, 5, 6, 3, 2], 2),
    ([238, 116, 57, 4], [5, 6, 7, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 1,
      3, 1, 0], 3),
    ([192, 116, 57, 4], [5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2,
      1, 3, 4, 3, 2, 1, 3, 2, 1], 3),
    ([6, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3,
      4, 5, 0, 2, 3, 4, 1, 3, 2, 0], 1),
    ([238, 6, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1,
      3, 4, 0], 2),
    ([192, 6, 4], [7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 4, 2, 3, 0, 2, 1, 3,
      4, 5, 6, 2, 3, 4, 0], 2),
    ([238, 192, 6, 4], [7, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0,
      2, 1, 0], 3),
    ([116, 6, 4], [7, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 4, 5, 1, 3, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2], 2),
    ([238, 116, 6, 4], [7, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 5, 2, 1,
      3, 4, 2, 1, 3, 1, 0], 3),
    ([192, 116, 6, 4], [7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2,
      3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 2, 1], 3),
    ([57, 6, 4], [7, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 2, 3, 4, 5, 1,
      3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2], 2),
    ([238, 57, 6, 4], [5, 6, 7, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 5,
      2, 1, 3, 4, 2, 1, 3, 1, 0], 3),
    ([192, 57, 6, 4], [5, 6, 7, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 2, 3, 0, 2, 1, 3, 4,
      5, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 2, 1], 3),
    ([1, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3,
      4, 5, 0, 2, 3, 4, 1, 3, 2, 0], 1),
    ([238, 1, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1,
      3, 4, 0], 2),
    ([192, 1, 4], [7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3,
      4, 5, 6, 2, 3, 4, 0], 2),
    ([238, 192, 1, 4], [5, 6, 7, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 4, 3, 0,
      2, 1, 0], 3),
    ([116, 1, 4], [7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 0], 2),
    ([238, 116, 1, 4], [0, 2, 3, 4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5,
      1, 3, 4, 2, 3, 0, 2, 1, 0], 3),
    ([57, 1, 4], [5, 6, 7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 1,
      3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6], 2),
    ([238, 57, 1, 4], [5, 6, 7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5,
      1, 3, 4, 2, 3, 1, 0], 3),
    ([192, 57, 1, 4], [5, 6, 7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3, 2, 1], 3),
    ([116, 57, 1, 4], [0, 2, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 1], 3),
    ([6, 1, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4,
      5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6], 2),
    ([192, 6, 1, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3,
      4, 5, 1, 3, 4, 2, 3, 1], 3),
    ([116, 6, 1, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 2, 3, 0,
      2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 0, 2, 3, 1], 3),
    ([57, 6, 1, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3,
      0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1], 3),
    ([2, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3,
      4, 5, 0, 2, 3, 4, 1, 3, 2, 0], 1),
    ([238, 2, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1,
      3, 4, 0], 2),
    ([192, 2, 4], [7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3,
      4, 5, 6, 2, 3, 4, 0], 2),
    ([238, 192, 2, 4], [5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0,
      2, 1, 0], 3),
    ([116, 2, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 0], 2),
    ([192, 116, 2, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 4, 3, 0, 2, 1, 3,
      4, 5, 1, 3, 4, 2, 3, 2, 1], 3),
    ([57, 2, 4], [5, 6, 7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5,
      3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6], 2),
    ([238, 57, 2, 4], [5, 6, 7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4,
      5, 3, 4, 2, 3, 1, 0], 3),
    ([192, 57, 2, 4], [5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 3, 2, 1, 3, 4, 0, 2, 3, 2, 1], 3),
    ([116, 57, 2, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 4, 2, 3, 0, 2, 1,
      3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 1], 3),
    ([6, 2, 4], [7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4,
      5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6], 2),
    ([238, 6, 2, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4,
      5, 1, 3, 4, 2, 3, 1, 0], 3),
    ([116, 6, 2, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0,
      2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 0, 2, 3, 1], 3),
    ([57, 6, 2, 4], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3,
      0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1], 3),
    ([1, 2, 4], [5, 6, 7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 4,
      5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6], 2),
    ([238, 1, 2, 4], [3, 4, 5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4,
      5, 1, 3, 4, 2, 3, 1, 0], 3),
    ([192, 1, 2, 4], [3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 3, 2, 1, 3, 4, 0, 2, 3, 2, 1], 3),
    ([116, 1, 2, 4], [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 2, 3, 0, 2,
      1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 1], 3),
    ([6, 1, 2, 4], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4,
      2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1], 3)]

@[expose] def classListE8TableNat : ℕ :=
  0xedefefefefefefefeceeeeeeeeeeeeeeefebededededededeeeaececececececebede9ebebebebebeaece8eaeaeaeaeae9e9ebe7e9e9e9e9e8e8eae6e8e8e8e8e7e7e7e9e5e7e7e7e6e6e6e8e4e6e6e6e5e5e5e5e7e2e3e5e4e4e4e4e6e0e1e4e3e3e3e3e3dee5e3e2e2e2e2e2e5dedfe1e1e1e1e1dce4e1e0e0e0e0e0e4dcdddfdfdfdfdfdfdbe2dededededae3e2dbddddddddddddd9e0dcdcdcdcd8e1e0d9dbdbdbdbd7dbdfdedadadad6dedadad7d9d9d9d9d5d9dddcd8d8d8d4dcd8d8d5d7d7d7d2dbd3d7dad6d6d1dad6d6d6d2d5d5d5cfd9d0d5d8d4d4ced8d4d4d4cfd3d3d3cdd3d7d3d3d2d2ccd7d2cdd2d6d1cbd6d1d1d1d1ccd0d0d0cad0d5d0d0cfcfc9d5cfcacfd4cec8d4cecececec9cdcdc6d3c7d2cdcdccc5d2ccccc6ccd1c4d1cbcbcbcbcbc5cacac2d0c3cfcacac9c1cfc9c9c2c9cec0cec8c8c8c8c8c1c7c7bec7cdc7bfc7c6bdcdc6beccc6c6bcccc5c5c5bdc5cbcbc4c4c4c4c4c4bcc3c3bac3cac3bbc3c2b9cac2bac9c2c2b8c9c1c1c1b9c1c8c8c0c0c0c0c0c0b8bfbfb7bfbfbfc7bfbeb5c7b6c6beb7beb4c6bdbdb5c5bdbdc5bcbcbcbcb4bcc4bbbbb3bbbbbbc3bbbab1c3b2c2bab3bab0c2b9b9b1c1b9b9c1b8b8b8b8b0b8c0b7aebfafb7b7beb7b6adb6beb6b6afb6acbeb5adbdb5aeb5bdb4b4b4acbcb4b4b3aabbabb3b3bab3b2a9b2bab2b2abb2a8bab1a9b9b1aab1b9b0b0b0a8b8b0b0afa6afb7a7afb6afa5b7aea6aeaeb5aea3b6a4b5adada6adb5acaca3b4aca5acaba1abb3a2abb2aba0b3aaa1aaaab1aa9eb29fb1a9a9a1a9b1a8a89eb0a8a0a8a79ca7a7af9da7a79aaf9bae9ca6ada6aea5a59aa5a5aca599a4ada4a4a49ba4ada399aca3a39aa3a296a2a2ab97a2a294ab95aa96a1a9a1aaa0a094a0a0a8a0939fa99f9f9f959fa99e93a89e9e949e9d929d9d9da79d9890a7919ca6929c9c8f9ba69b919ba49ba69a8fa5909aa39aa48ea39999998f99988c98989898989d978b979797a2978d89a28a96a18b96968895a1958a959f95a19488a089949e949f879e9393938893859d8692929c928c83919c849b8691919c9083909a8590909b829a8f838f998f8e998e8e8e8e828e8d818d8d8d8d8d977f98808c8c8c8c927d977e8b8b968b817b8a967c957e8a8a96897b89947d8989957a94887b8893888793878787877a877886927986918680928578858590857f7784849184798484917690778f788383828f828276828e82748d75818181818b72808c73808080868c7f727f7f7f7f85707e8b717e8a7e758b7d707d7d897d746f7c7c8a7c717c7c8a6e896f88707b7b7a887a7a6e7a877a6c7979866d847973866b856c78837872846a7783776c77777683766a826b7676687581697575757e817468747474747d667373806773737980657f66727272786371717e647c71697e627d63707b70687c616f7b6f636f6f6e7b6e617a626e6e5f6d6d6d796d6067795e6c785f776c666b786b5e6b766b656a775d766a5e6a6a5a6969755b6969717559745a686868705767676773585c6d735666725766666c657265566565656b546464647164555b71536370546f635a62706253626e6259616f526e615361615160606060606d5c6d505f5f6c5f51575e6c4f6b506a5e565d5d6a5d5d4f5d5d4c5c5c5c5c4e67604a5b5b5b694b4d6469495a684a5a5a6359685949595959624858585858674e586747575766484c5f566646654756565e455555555555644d644454546354454a536343624461534952526152524352526042515151515f4c505f41505e5042474f4f5e4f415d4f463e4e4e4e405c584e3d4d4d4d4d3f5b555c3c4c4c4c3e57513b4b4b4b4b5b3f4b5b3a4a4a5a3b3d54495a39593a4949535838484848573e484757374756383c50464656463746464f553645454545543d445435445344363a4343534335524339425134424242503c414150334f413437304040324e4040402f3f3f3f314d4b3f4e2e3e3e304c483e4d2d3d3d3d2f4a453c4c2c3c3c2e47424b2b3b3b3b4a2f3b3a4a2a3a492b2d44393949392a3939433848293838472e383737472846292c41364527363636442d353544264335272a343442253434412c33333341333325282232244032323232213131233f313131402030223e3030303f1f2f2f213d3b2f2e3e1e2e203c382e2d3d1d2d2d1f3a362c2c3c1c2c1e37342b3b1b2b2b3a1f2b2a2a3a1a391b1d352929381929371e292828283728191c33272736182727351d262626352626181a252525341725331c141632242424242413231531232323233212143022222222311121132f212121203010122e2020201f2f0f1f112d2b1f1e1e2e0e102c291e1d1d2d0d1d0f2a271c1c1c2c0c0e28251b1b2b0b1b2a0f1b1a1a1a2a1a0b0d26191919290a280e19181818270918260d171717172508170c07241616161616160607231515151515240622141414141423050621131313131222052012121212112104051f111111101020041e1010100f0f1f03041d1b0f0e0e0e1e031c190e0d0d0d1d02031a180c0c0c0c1c020c170b0b0b1b011a030b0a0a0a0a190a010a09090909180009020808080808170800161507070707070715141306060606060513121105050505040411100f0404040303030f0e0d0b03020202020d0c0209010101010b010a010000000000090008

@[expose] def classListE8Iform (x y : Fin Tag.E8.rank → ℤ) : ℤ :=
  ((List.finRange Tag.E8.rank).map fun i =>
    ((List.finRange Tag.E8.rank).map fun j => x i * Tag.E8.cartan i j * y j).sum).sum

@[expose] def classListE8FrameB : List ℕ → Bool
  | [] => true
  | k :: L => (L.all fun k' => classListE8Iform (Tag.E8.rootCertificate.root k)
      (Tag.E8.rootCertificate.root k') == 0) && classListE8FrameB L

@[expose] def classListE8PosB (L : List ℕ) : Bool :=
  L.all fun k => decide (k < Tag.E8.rootCertificate.roots.length)

@[expose] def classListE8Image (k i : ℕ) : ℕ :=
  classListE8TableNat / 2 ^ (64 * k + 8 * i) % 256

@[expose] def classListE8WordPos (ω : List ℕ) (k : ℕ) : ℕ :=
  ω.foldl classListE8Image k

@[expose] def classListE8TableB : Bool :=
  (List.range Tag.E8.rootCertificate.roots.length).all fun k =>
    (List.finRange Tag.E8.rank).all fun i =>
      classListE8Image k i == Tag.E8.rootCertificate.image k i

@[expose] def classListE8PatternVecB (a b c d θ : Fin Tag.E8.rank → ℤ) : Bool :=
  classListE8Iform a c == -1 && classListE8Iform b c == -1 && classListE8Iform d c == -1 &&
    classListE8Iform a b == 0 && classListE8Iform a d == 0 && classListE8Iform b d == 0 &&
    List.ofFn (a + b + 2 • c + d) == List.ofFn θ

@[expose] def classListE8PatternB (p : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  classListE8PosB [p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2] &&
    classListE8PatternVecB (Tag.E8.rootCertificate.root p.1) (Tag.E8.rootCertificate.root p.2.1)
      (Tag.E8.rootCertificate.root p.2.2.1) (Tag.E8.rootCertificate.root p.2.2.2.1)
      (Tag.E8.rootCertificate.root p.2.2.2.2) &&
    p.1 != p.2.2.2.2 && p.2.1 != p.2.2.2.2 && p.2.2.2.1 != p.2.2.2.2 && p.1 != p.2.1 &&
    p.1 != p.2.2.2.1 && p.2.1 != p.2.2.2.1

@[expose] def classListE8PatternIn (S : List ℕ) (p : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  S.contains p.1 && S.contains p.2.1 && S.contains p.2.2.2.1 && S.contains p.2.2.2.2

@[expose] def classListE8WordB (e : List ℕ × List ℕ × ℕ) : Bool :=
  classListE8PosB e.1 && (e.2.1.all fun i => decide (i < 8)) && decide (e.2.2 < 4) &&
    (e.1.map (classListE8WordPos e.2.1)).isPerm (classListE8RepPos e.2.2)

@[expose] def classListE8Check : Bool :=
  classListE8TableB && classListE8PosB classListE8CascPos &&
    classListE8FrameB classListE8CascPos &&
    ((List.range 4).all fun k =>
      classListE8PosB (classListE8RepPos k) && classListE8FrameB (classListE8RepPos k)) &&
    classListE8Patterns.all classListE8PatternB && classListE8Words.all classListE8WordB &&
    classListE8CascPos.sublists.all fun S => S.isEmpty ||
      classListE8Patterns.any (classListE8PatternIn S) ||
        (classListE8Words.map Prod.fst).contains S

theorem classListE8Check_eq_true : classListE8Check = true := by
  decide +kernel

theorem classListE8CascPos_map_root :
    classListE8CascPos.map Tag.E8.rootCertificate.root = cascadeRoots .E8 := by
  have h : (classListE8CascPos.map fun k => List.ofFn (Tag.E8.rootCertificate.root k)) =
      (cascadeRoots .E8).map List.ofFn := by
    decide +kernel
  refine List.map_injective_iff.2 List.ofFn_injective ?_
  rw [List.map_map]
  exact h

theorem classListE8RepPos_map_root :
    (classListE8RepPos 0).map Tag.E8.rootCertificate.root = [highRoot .E8] ∧
      (classListE8RepPos 1).map Tag.E8.rootCertificate.root = oddDerivE8YFrame ∧
      (classListE8RepPos 2).map Tag.E8.rootCertificate.root = oddDerivE8ZFrame ∧
      (classListE8RepPos 3).map Tag.E8.rootCertificate.root = oddDerivE8UFrame := by
  have key : ∀ {L : List ℕ} {F : List (Fin Tag.E8.rank → ℤ)},
      (L.map fun k => List.ofFn (Tag.E8.rootCertificate.root k)) = F.map List.ofFn →
        L.map Tag.E8.rootCertificate.root = F :=
    fun h => List.map_injective_iff.2 List.ofFn_injective (by rw [List.map_map]; exact h)
  exact ⟨key (by decide +kernel), key (by decide +kernel), key (by decide +kernel),
    key (by decide +kernel)⟩

theorem classListE8Iform_eq (x y : Fin Tag.E8.rank → ℤ) : classListE8Iform x y = iform x y := by
  have hS : Tag.E8.symmetrizedCartan = Tag.E8.cartan := by
    simp [Tag.symmetrizedCartan, Tag.symmetrizer]
  rw [classListE8Iform, iform, hS]
  simp only [Fin.sum_univ_def]

theorem classListE8FrameB_pairwise : ∀ {L : List ℕ}, classListE8FrameB L = true →
    L.Pairwise fun k k' =>
      iform (Tag.E8.rootCertificate.root k) (Tag.E8.rootCertificate.root k') = 0
  | [], _ => List.Pairwise.nil
  | k :: L, h => by
    simp only [classListE8FrameB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    refine List.pairwise_cons.2 ⟨fun k' hk' => ?_, classListE8FrameB_pairwise h.2⟩
    rw [← classListE8Iform_eq]
    exact h.1 k' hk'

theorem classListE8PosB_sound {L : List ℕ} (h : classListE8PosB L = true) :
    ∀ k ∈ L, k < Tag.E8.rootCertificate.roots.length := by
  simpa only [classListE8PosB, List.all_eq_true, decide_eq_true_eq] using h

theorem classListE8TableB_sound (h : classListE8TableB = true) {k : ℕ}
    (hk : k < Tag.E8.rootCertificate.roots.length) (i : Fin Tag.E8.rank) :
    classListE8Image k i = Tag.E8.rootCertificate.image k i := by
  simp only [classListE8TableB, List.all_eq_true, List.mem_range, List.mem_finRange,
    beq_iff_eq, forall_const] at h
  exact h k hk i

theorem classListE8WordPos_eq (hT : classListE8TableB = true) :
    ∀ (ω : List ℕ), (∀ i ∈ ω, i < 8) → ∀ {k : ℕ}, k < Tag.E8.rootCertificate.roots.length →
      classListE8WordPos ω k = wordPos Tag.E8.rootCertificate ω k
  | [], _, _, _ => rfl
  | j :: ω, hω, k, hk => by
    have hj : j < 8 := hω j List.mem_cons_self
    have hidx : Tag.E8.idx j = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
    have h1 : classListE8Image k j = Tag.E8.rootCertificate.image k (Tag.E8.idx j) := by
      rw [hidx]
      exact classListE8TableB_sound hT hk ⟨j, hj⟩
    have h2 := (image_spec_of_check (Tag.rootCertificate_check .E8) hk (Tag.E8.idx j)).1
    show classListE8WordPos ω (classListE8Image k j) =
      wordPos Tag.E8.rootCertificate ω (Tag.E8.rootCertificate.image k (Tag.E8.idx j))
    rw [h1]
    exact classListE8WordPos_eq hT ω (fun i hi => hω i (List.mem_cons_of_mem _ hi)) h2

theorem classListE8WordB_sound (hT : classListE8TableB = true)
    {e : List ℕ × List ℕ × ℕ} (h : classListE8WordB e = true) :
    e.2.2 < 4 ∧
      (e.1.map (wordPos Tag.E8.rootCertificate e.2.1)).Perm (classListE8RepPos e.2.2) := by
  simp only [classListE8WordB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hpos, hlet⟩, hk⟩, hperm⟩ := h
  have hpos' := classListE8PosB_sound hpos
  refine ⟨hk, ?_⟩
  rw [← List.map_congr_left fun k hk' => classListE8WordPos_eq hT e.2.1 hlet (hpos' k hk')]
  exact List.isPerm_iff.1 hperm

theorem classListE8PatternVecB_sound {a b c d θ : Fin Tag.E8.rank → ℤ}
    (h : classListE8PatternVecB a b c d θ = true) :
    (iform a c = -1 ∧ iform b c = -1 ∧ iform d c = -1 ∧ iform a b = 0 ∧ iform a d = 0 ∧
      iform b d = 0) ∧ a + b + 2 • c + d = θ := by
  simp only [classListE8PatternVecB, Bool.and_eq_true, beq_iff_eq, classListE8Iform_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hac, hbc⟩, hdc⟩, hab⟩, had⟩, hbd⟩, hθ⟩ := h
  exact ⟨⟨hac, hbc, hdc, hab, had, hbd⟩, List.ofFn_injective hθ⟩

theorem classListE8PatternB_sound {a b c d θ : ℕ}
    (h : classListE8PatternB (a, b, c, d, θ) = true) :
    IsD4Pattern .E8 (Tag.E8.rootCertificate.root a) (Tag.E8.rootCertificate.root b)
        (Tag.E8.rootCertificate.root c) (Tag.E8.rootCertificate.root d) ∧
      Tag.E8.rootCertificate.root a + Tag.E8.rootCertificate.root b +
          2 • Tag.E8.rootCertificate.root c + Tag.E8.rootCertificate.root d =
        Tag.E8.rootCertificate.root θ ∧
      a ≠ θ ∧ b ≠ θ ∧ d ≠ θ ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d := by
  simp only [classListE8PatternB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hpos, hvec⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  obtain ⟨⟨hac, hbc, hdc, hab, had, hbd⟩, hθ⟩ := classListE8PatternVecB_sound hvec
  have hp := classListE8PosB_sound hpos
  have hr : ∀ k ∈ [a, b, c, d, θ], IsRoot .E8 (Tag.E8.rootCertificate.root k) := fun k hk =>
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E8) k (hp k hk)
  exact ⟨⟨hr a (by simp), hr b (by simp), hr c (by simp), hr d (by simp), hac, hbc, hdc, hab,
    had, hbd⟩, hθ, h1, h2, h3, h4, h5, h6⟩

theorem classListE8Check_facts :
    (∀ k ∈ classListE8CascPos, k < Tag.E8.rootCertificate.roots.length) ∧
      classListE8CascPos.Pairwise (fun k k' =>
        iform (Tag.E8.rootCertificate.root k) (Tag.E8.rootCertificate.root k') = 0) ∧
      (∀ k < 4, (∀ p ∈ classListE8RepPos k, p < Tag.E8.rootCertificate.roots.length) ∧
        (classListE8RepPos k).Pairwise fun p p' =>
          iform (Tag.E8.rootCertificate.root p) (Tag.E8.rootCertificate.root p') = 0) ∧
      (∀ a b c d θ : ℕ, (a, b, c, d, θ) ∈ classListE8Patterns →
        IsD4Pattern .E8 (Tag.E8.rootCertificate.root a) (Tag.E8.rootCertificate.root b)
            (Tag.E8.rootCertificate.root c) (Tag.E8.rootCertificate.root d) ∧
          Tag.E8.rootCertificate.root a + Tag.E8.rootCertificate.root b +
              2 • Tag.E8.rootCertificate.root c + Tag.E8.rootCertificate.root d =
            Tag.E8.rootCertificate.root θ ∧
          a ≠ θ ∧ b ≠ θ ∧ d ≠ θ ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d) ∧
      (∀ e ∈ classListE8Words, e.2.2 < 4 ∧
        (e.1.map (wordPos Tag.E8.rootCertificate e.2.1)).Perm (classListE8RepPos e.2.2)) ∧
      (∀ S : List ℕ, S.Sublist classListE8CascPos → S = [] ∨
        (∃ a b c d θ : ℕ, (a, b, c, d, θ) ∈ classListE8Patterns ∧ a ∈ S ∧ b ∈ S ∧ d ∈ S ∧
          θ ∈ S) ∨ ∃ e ∈ classListE8Words, e.1 = S) := by
  have h := classListE8Check_eq_true
  simp only [classListE8Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT, hcp⟩, hco⟩, hrep⟩, hpat⟩, hword⟩, hcov⟩ := h
  simp only [List.all_eq_true] at hrep hpat hword hcov
  refine ⟨classListE8PosB_sound hcp, classListE8FrameB_pairwise hco, fun k hk => ?_,
    fun a b c d θ hp => classListE8PatternB_sound (hpat _ hp),
    fun e he => classListE8WordB_sound hT (hword e he), fun S hS => ?_⟩
  · have h := hrep k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true] at h
    exact ⟨classListE8PosB_sound h.1, classListE8FrameB_pairwise h.2⟩
  · have h := hcov S (List.mem_sublists.2 hS)
    simp only [Bool.or_eq_true, List.isEmpty_iff, List.any_eq_true, List.contains_iff_mem,
      List.mem_map] at h
    rcases h with (h | ⟨⟨a, b, c, d, θ⟩, hp, hin⟩) | ⟨e, he, heS⟩
    · exact Or.inl h
    · simp only [classListE8PatternIn, Bool.and_eq_true, List.contains_iff_mem] at hin
      exact Or.inr (Or.inl ⟨a, b, c, d, θ, hp, hin.1.1.1, hin.1.1.2, hin.1.2, hin.2⟩)
    · exact Or.inr (Or.inr ⟨e, he, heS⟩)

variable {K : Type} [Field K]


theorem classListE8_exists_conj_repPos [CharP K 2] {S : List ℕ}
    (hS : S.Sublist classListE8CascPos) (hne : S ≠ []) :
    ∃ g ∈ adjointGroup .E8 K, ∃ k < 4,
      g * (S.map fun p => pinnedX .E8 K (Tag.E8.rootCertificate.root p) 1).prod * g⁻¹ =
        ((classListE8RepPos k).map fun p =>
          pinnedX .E8 K (Tag.E8.rootCertificate.root p) 1).prod := by
  obtain ⟨hcp, hco, hrep, hpat, hword, hcov⟩ := classListE8Check_facts
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  induction hn : S.length using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    have hSpos : ∀ p ∈ S, p < Tag.E8.rootCertificate.roots.length := fun p hp =>
      hcp p (hS.subset hp)
    have hSorth := hco.sublist hS
    rcases hcov S hS with h0 | ⟨a, b, c, d, θ, hp, ha, hb, hd, hθ⟩ | ⟨e, he, heS⟩
    · exact absurd h0 hne
    ·
      obtain ⟨hpat', hθ', haθ, hbθ, hdθ, hab, had, hbd⟩ := hpat a b c d θ hp
      obtain ⟨g₁, hg₁, he₁⟩ := classListE8_exists_conj_posProd_erase (K := K) hτ hpat' hθ'
        hSpos hSorth ha hb hd hθ haθ hbθ hdθ hab had hbd
      have hlt : (S.erase θ).length < n := by
        rw [List.length_erase_of_mem hθ, ← hn]
        exact Nat.sub_lt (List.length_pos_of_mem hθ) one_pos
      obtain ⟨g₂, hg₂, k, hk, he₂⟩ := ih _ hlt (List.erase_sublist.trans hS)
        (List.ne_nil_of_mem ((List.mem_erase_of_ne haθ).2 ha)) rfl
      refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, k, hk, ?_⟩
      rw [← he₂, ← he₁]
      group
    ·
      obtain ⟨hk, hperm⟩ := hword e he
      rw [heS] at hperm
      obtain ⟨hrp, hro⟩ := hrep e.2.2 hk
      refine ⟨classListE8WordElt .E8 K e.2.1, classListE8WordElt_mem_adjointGroup _, e.2.2, hk,
        ?_⟩
      rw [classListE8_wordElt_conj_posProd _ hSpos]
      exact (classListE8_posProd_perm hτ hrp hro hperm.symm).symm

theorem classListE8_exists_conj_cascade_prod_mem [CharP K 2] {S : List (Fin Tag.E8.rank → ℤ)}
    (hS : S.Sublist (cascadeRoots .E8)) (hne : S ≠ []) :
    ∃ g ∈ adjointGroup .E8 K, ∃ s ∈ innerRepsE8 K,
      g * (S.map fun σ => pinnedX .E8 K σ 1).prod * g⁻¹ = (s : ModGL .E8 K) := by
  rw [← classListE8CascPos_map_root] at hS
  obtain ⟨S₀, hS₀, rfl⟩ := List.sublist_map_iff.1 hS
  obtain ⟨g, hg, k, hk, he⟩ := classListE8_exists_conj_repPos (K := K) hS₀
    (by rintro rfl; exact hne rfl)
  obtain ⟨h0, h1, h2, h3⟩ := classListE8RepPos_map_root
  refine ⟨g, hg, ?_⟩
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [he]
  have hprod : ∀ k, ((classListE8RepPos k).map fun p =>
      pinnedX .E8 K (Tag.E8.rootCertificate.root p) 1).prod =
      (((classListE8RepPos k).map Tag.E8.rootCertificate.root).map fun σ =>
        pinnedX .E8 K σ 1).prod := fun k => by
    rw [List.map_map]
    rfl
  rw [hprod]
  interval_cases k
  · rw [h0]
    exact ⟨_, Set.mem_insert _ _, by simp⟩
  · rw [h1]
    exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert _ _), rfl⟩
  · rw [h2]
    exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), rfl⟩
  · rw [h3]
    exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _))), rfl⟩

theorem classListE8_exists_conj_mem_innerRepsE8 [Finite K] [CharP K 2]
    {t : adjointGroup .E8 K} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ g : adjointGroup .E8 K, g * t * g⁻¹ ∈ innerRepsE8 K := by
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨g₁, S, hS, c, hc, he₁⟩ := exists_conj_eq_cascade_prod hτ ht
  obtain ⟨hcp, hco, -⟩ := classListE8Check_facts
  have hcasc : (cascadeRoots .E8).Pairwise fun σ σ' => iform σ σ' = 0 := by
    rw [← classListE8CascPos_map_root]
    exact List.pairwise_map.2 hco
  have hroots : ∀ σ ∈ cascadeRoots .E8, IsRoot .E8 σ := by
    rw [← classListE8CascPos_map_root]
    exact classListE8_forall_isRoot hcp
  obtain ⟨h, hhC, -, -, hh⟩ := exists_torus_conj_frame_prod (classD4_noG2 hτ)
    (fun σ hσ => hroots σ (hS.subset hσ)) (hcasc.sublist hS) c hc
  have hne : S ≠ [] := by
    rintro rfl
    apply ht1
    have h1 : g₁ * t * g₁⁻¹ = 1 := Subtype.ext (by simpa using he₁)
    calc t = g₁⁻¹ * (g₁ * t * g₁⁻¹) * g₁ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨g₂, hg₂, s, hs, he₂⟩ := classListE8_exists_conj_cascade_prod_mem (K := K) hS hne
  refine ⟨⟨g₂, hg₂⟩ * ⟨h, hhC⟩ * g₁, ?_⟩
  have he : ⟨g₂, hg₂⟩ * ⟨h, hhC⟩ * g₁ * t * (⟨g₂, hg₂⟩ * ⟨h, hhC⟩ * g₁)⁻¹ = s := by
    apply Subtype.ext
    have e : ((⟨g₂, hg₂⟩ * ⟨h, hhC⟩ * g₁ * t * (⟨g₂, hg₂⟩ * ⟨h, hhC⟩ * g₁)⁻¹ :
        adjointGroup .E8 K) : ModGL .E8 K) =
        g₂ * (h * ((g₁ * t * g₁⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) * h⁻¹) * g₂⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      group
    rw [e, he₁, hh, he₂]
  rw [he]
  exact hs

theorem classListE8_hrep [Finite K] [CharP K 2] (t : adjointGroup .E8 K)
    (ht : orderOf (MulAut.conj t) = 2) :
    ∃ ψ : MulAut (adjointGroup .E8 K), ∃ s ∈ innerRepsE8 K, ψ s = t := by
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) := by
    intro x y hxy
    have hz : y⁻¹ * x ∈ Subgroup.center (adjointGroup .E8 K) :=
      Subgroup.mem_center_iff.2 fun w => by
        have h1 := congrArg (fun α : MulAut (adjointGroup .E8 K) => α w) hxy
        simp only [MulAut.conj_apply] at h1
        calc w * (y⁻¹ * x) = y⁻¹ * (y * w * y⁻¹) * x := by group
          _ = y⁻¹ * (x * w * x⁻¹) * x := by rw [h1]
          _ = y⁻¹ * x * w := by group
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
    calc x = y * (y⁻¹ * x) := by group
      _ = y := by rw [hz, mul_one]
  have ht2 : t ^ 2 = 1 := hinj (by rw [map_pow, map_one, ← ht, pow_orderOf_eq_one])
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨g, hg⟩ := classListE8_exists_conj_mem_innerRepsE8 ht2 ht1
  refine ⟨MulAut.conj g⁻¹, _, hg, ?_⟩
  rw [MulAut.conj_apply]
  group

theorem innerInvolutionInput_E8 [Finite K] [CharP K 2] :
    InnerInvolutionInput (adjointGroup .E8 K) :=
  innerInvolutionInput_E8_of_classes classListE8_hrep

theorem innerInvolutionInput_E8' {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    InnerInvolutionInput (adjointGroup .E8 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact innerInvolutionInput_E8

end CFSG.SeitzReduction
