module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NodeTab
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.SmallCheck

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

@[expose] def e6n0W : List (List (Fin 6)) :=
  ([[],
    [0],
    [2],
    [0, 2],
    [2, 0],
    [3, 2],
    [0, 2, 0],
    [1, 3, 2],
    [3, 0, 2],
    [3, 2, 0],
    [4, 3, 2],
    [1, 3, 0, 2],
    [1, 3, 2, 0],
    [2, 3, 0, 2],
    [3, 0, 2, 0],
    [4, 1, 3, 2],
    [4, 3, 0, 2],
    [4, 3, 2, 0],
    [5, 4, 3, 2],
    [1, 3, 0, 2, 0],
    [2, 1, 3, 0, 2],
    [2, 3, 0, 2, 0],
    [3, 4, 1, 3, 2],
    [4, 1, 3, 0, 2],
    [4, 1, 3, 2, 0],
    [4, 2, 3, 0, 2],
    [4, 3, 0, 2, 0],
    [5, 4, 1, 3, 2],
    [5, 4, 3, 0, 2],
    [5, 4, 3, 2, 0],
    [2, 1, 3, 0, 2, 0],
    [2, 3, 4, 1, 3, 2],
    [3, 2, 1, 3, 0, 2],
    [3, 4, 1, 3, 0, 2],
    [3, 4, 1, 3, 2, 0],
    [3, 4, 2, 3, 0, 2],
    [4, 1, 3, 0, 2, 0],
    [4, 2, 1, 3, 0, 2],
    [4, 2, 3, 0, 2, 0],
    [5, 3, 4, 1, 3, 2],
    [5, 4, 1, 3, 0, 2],
    [5, 4, 1, 3, 2, 0],
    [5, 4, 2, 3, 0, 2],
    [5, 4, 3, 0, 2, 0],
    [2, 3, 4, 1, 3, 2, 0],
    [3, 2, 1, 3, 0, 2, 0],
    [3, 4, 1, 3, 0, 2, 0],
    [3, 4, 2, 3, 0, 2, 0],
    [4, 2, 1, 3, 0, 2, 0],
    [4, 5, 3, 4, 1, 3, 2],
    [5, 2, 3, 4, 1, 3, 2],
    [5, 3, 4, 1, 3, 0, 2],
    [5, 3, 4, 1, 3, 2, 0],
    [5, 3, 4, 2, 3, 0, 2],
    [5, 4, 1, 3, 0, 2, 0],
    [5, 4, 2, 1, 3, 0, 2],
    [5, 4, 2, 3, 0, 2, 0],
    [4, 5, 2, 3, 4, 1, 3, 2],
    [4, 5, 3, 4, 1, 3, 0, 2],
    [4, 5, 3, 4, 1, 3, 2, 0],
    [4, 5, 3, 4, 2, 3, 0, 2],
    [5, 2, 3, 4, 1, 3, 2, 0],
    [5, 3, 4, 1, 3, 0, 2, 0],
    [5, 3, 4, 2, 3, 0, 2, 0],
    [5, 4, 2, 1, 3, 0, 2, 0],
    [3, 4, 5, 2, 3, 4, 1, 3, 2],
    [4, 5, 2, 3, 4, 1, 3, 2, 0],
    [4, 5, 3, 4, 1, 3, 0, 2, 0],
    [4, 5, 3, 4, 2, 3, 0, 2, 0],
    [1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [3, 4, 5, 2, 3, 4, 1, 3, 2, 0],
    [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]] : List (List (Fin 6)))
@[expose] def e6n0U : List (List (Fin 6)) :=
  ([[],
    [2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    [5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    [4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    [3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    [1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]] : List (List (Fin 6)))
@[expose] def e6n0X : List (List ℤ) := [[-1, -1, 1, 0, 0, 0], [-1, 0, 0, 0, 0, 1], [-1, 0, 0, 0, 1, -1], [-1, 0, 0, 1, -1, 0], [-1, 0, 1, 0, 0, 0], [-1, 1, 1, -1, 0, 0], [0, -1, -1, 1, 0, 0], [0, -1, 0, 0, 1, 0], [0, -1, 0, 1, -1, 1], [0, -1, 0, 1, 0, -1], [0, 0, -1, 1, 0, 0], [0, 0, 0, -1, 1, 0], [0, 0, 0, 0, -1, 1], [0, 0, 0, 0, 0, -1], [0, 0, 1, -1, 0, 1], [0, 0, 1, -1, 1, -1], [0, 0, 1, 0, -1, 0], [0, 1, -1, 0, 0, 0], [0, 1, 0, -1, 1, 0], [0, 1, 0, 0, -1, 1], [0, 1, 0, 0, 0, -1], [1, -1, 0, 0, 0, 0], [1, 0, -1, 0, 0, 1], [1, 0, -1, 0, 1, -1], [1, 0, -1, 1, -1, 0], [1, 0, 0, 0, 0, 0], [1, 1, 0, -1, 0, 0]]
@[expose] def e6n0V : List ℤ := [4, 3, 5, 6, 4, 2]
theorem e6n0_hv0len : e6n0V.length = Tag.rank .E6 := by decide
theorem e6n0_hv0 : ∀ j : N6, j ≠ ⟨0, by decide⟩ → reflectL6 j e6n0V = e6n0V := by decide +kernel
theorem e6n0_hU1 : ∀ j : Fin 6, (e6n0U.getD j []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)) =
    List.ofFn (alphaF ⟨0, by decide⟩) := by decide +kernel
theorem e6n0_hU2 : ∀ j : Fin 6, (e6n0U.getD j []).foldr reflectL6
    (List.ofFn (Pi.single ⟨0, by decide⟩ (1 : ℤ) : N6 → ℤ)) = List.ofFn (Pi.single ⟨0, by decide⟩ (1 : ℤ) : N6 → ℤ) := by
  decide +kernel
theorem e6n0_hdist : ∀ j j' : Fin 6, j ≠ j' →
    (e6n0U.getD j []).foldr reflectL6 e6n0V ≠ (e6n0U.getD j' []).foldr reflectL6 e6n0V := by decide +kernel
theorem e6n0_hY : ∀ j j' : Fin 6, j ≠ j' →
    (e6n0U.getD j []).foldr refEL (List.ofFn (omegaF ⟨0, by decide⟩)) ≠
      (e6n0U.getD j' []).foldr refEL (List.ofFn (omegaF ⟨0, by decide⟩)) := by decide +kernel
theorem e6n0_hxorb : ∀ x ∈ e6n0X, ∀ y ∈ e6n0X, x ≠ y → 1 ≤ contentL (subL x y) ∧ contentL (subL x y) ≤ 2 := by
  decide +kernel
theorem e6n0_hβ : ∀ i i' : Fin 72, i ≠ i' →
    1 ≤ contentL (subL (((e6n0W).getD i []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)))
      (((e6n0W).getD i' []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)))) ∧
    contentL (subL (((e6n0W).getD i []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)))
      (((e6n0W).getD i' []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)))) ≤ 2 := by decide +kernel
theorem e6n0_hbdβ : ∀ i : Fin 72, ∀ c ∈ ((e6n0W).getD i []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)), |c| ≤ 2 := by
  decide +kernel
theorem e6n0_hbdX : ∀ (i : Fin 72) (j : Fin 6), ∀ c ∈ ((e6n0W).getD i []).foldr refEL
    ((e6n0U.getD j []).foldr refEL (List.ofFn (omegaF ⟨0, by decide⟩))), |c| ≤ 2 := by decide +kernel
theorem e6n0_hmem : ∀ (i : Fin 72) (j : Fin 6), ((e6n0W).getD i []).foldr refEL
    ((e6n0U.getD j []).foldr refEL (List.ofFn (omegaF ⟨0, by decide⟩))) ∈ e6n0X := by decide +kernel
@[expose] def e6n0Tab : NodeTab ⟨0, by decide⟩ where
  A := 72
  B := 6
  wTab := e6n0W
  uTab := e6n0U
  v0 := e6n0V
  xorb := e6n0X
  hv0len := e6n0_hv0len
  hv0 := e6n0_hv0
  hU1 := e6n0_hU1
  hU2 := e6n0_hU2
  hdist := e6n0_hdist
  hβ := e6n0_hβ
  hbdβ := e6n0_hbdβ
  hY := e6n0_hY
  hbdX := e6n0_hbdX
  hmem := e6n0_hmem
  hxorb := e6n0_hxorb
theorem e6n0S_hβ : ∀ i i' : Fin 14, i ≠ i' →
    1 ≤ contentL (subL (((e6n0W.take 14).getD i []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)))
      (((e6n0W.take 14).getD i' []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)))) ∧
    contentL (subL (((e6n0W.take 14).getD i []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)))
      (((e6n0W.take 14).getD i' []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)))) ≤ 2 := by decide +kernel
theorem e6n0S_hbdβ : ∀ i : Fin 14, ∀ c ∈ ((e6n0W.take 14).getD i []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩)), |c| ≤ 2 := by
  decide +kernel
theorem e6n0S_hbdX : ∀ (i : Fin 14) (j : Fin 6), ∀ c ∈ ((e6n0W.take 14).getD i []).foldr refEL
    ((e6n0U.getD j []).foldr refEL (List.ofFn (omegaF ⟨0, by decide⟩))), |c| ≤ 2 := by decide +kernel
theorem e6n0S_hmem : ∀ (i : Fin 14) (j : Fin 6), ((e6n0W.take 14).getD i []).foldr refEL
    ((e6n0U.getD j []).foldr refEL (List.ofFn (omegaF ⟨0, by decide⟩))) ∈ e6n0X := by decide +kernel
@[expose] def e6n0STab : NodeTab ⟨0, by decide⟩ where
  A := 14
  B := 6
  wTab := e6n0W.take 14
  uTab := e6n0U
  v0 := e6n0V
  xorb := e6n0X
  hv0len := e6n0_hv0len
  hv0 := e6n0_hv0
  hU1 := e6n0_hU1
  hU2 := e6n0_hU2
  hdist := e6n0_hdist
  hβ := e6n0S_hβ
  hbdβ := e6n0S_hbdβ
  hY := e6n0_hY
  hbdX := e6n0S_hbdX
  hmem := e6n0S_hmem
  hxorb := e6n0_hxorb
theorem e6n0_small : smallCheck ⟨0, by decide⟩ (e6n0W.take 14) e6n0U 14 6 = true := by decide +kernel
theorem e6n0_prim : ∀ i : Fin 72, contentL (((e6n0W).getD i []).foldr refEL (List.ofFn (alphaF ⟨0, by decide⟩))) = 1 := by
  decide +kernel
@[expose] def e6n5W : List (List (Fin 6)) :=
  ([[],
    [4],
    [5],
    [3, 4],
    [4, 5],
    [5, 4],
    [1, 3, 4],
    [2, 3, 4],
    [3, 4, 5],
    [4, 5, 4],
    [5, 3, 4],
    [0, 2, 3, 4],
    [1, 3, 4, 5],
    [2, 1, 3, 4],
    [2, 3, 4, 5],
    [3, 4, 5, 4],
    [4, 5, 3, 4],
    [5, 1, 3, 4],
    [5, 2, 3, 4],
    [0, 2, 1, 3, 4],
    [0, 2, 3, 4, 5],
    [1, 3, 4, 5, 4],
    [2, 1, 3, 4, 5],
    [2, 3, 4, 5, 4],
    [3, 2, 1, 3, 4],
    [3, 4, 5, 3, 4],
    [4, 5, 1, 3, 4],
    [4, 5, 2, 3, 4],
    [5, 0, 2, 3, 4],
    [5, 2, 1, 3, 4],
    [0, 2, 1, 3, 4, 5],
    [0, 2, 3, 4, 5, 4],
    [1, 3, 4, 5, 3, 4],
    [2, 1, 3, 4, 5, 4],
    [2, 3, 4, 5, 3, 4],
    [3, 0, 2, 1, 3, 4],
    [3, 2, 1, 3, 4, 5],
    [3, 4, 5, 1, 3, 4],
    [3, 4, 5, 2, 3, 4],
    [4, 3, 2, 1, 3, 4],
    [4, 5, 0, 2, 3, 4],
    [4, 5, 2, 1, 3, 4],
    [5, 0, 2, 1, 3, 4],
    [5, 3, 2, 1, 3, 4],
    [0, 2, 1, 3, 4, 5, 4],
    [0, 2, 3, 4, 5, 3, 4],
    [1, 3, 4, 5, 1, 3, 4],
    [2, 1, 3, 4, 5, 3, 4],
    [2, 3, 0, 2, 1, 3, 4],
    [2, 3, 4, 5, 2, 3, 4],
    [3, 0, 2, 1, 3, 4, 5],
    [3, 2, 1, 3, 4, 5, 4],
    [3, 4, 5, 0, 2, 3, 4],
    [4, 3, 0, 2, 1, 3, 4],
    [4, 3, 2, 1, 3, 4, 5],
    [4, 5, 0, 2, 1, 3, 4],
    [5, 3, 0, 2, 1, 3, 4],
    [0, 2, 1, 3, 4, 5, 3, 4],
    [0, 2, 3, 4, 5, 2, 3, 4],
    [2, 3, 0, 2, 1, 3, 4, 5],
    [2, 3, 4, 5, 0, 2, 3, 4],
    [3, 0, 2, 1, 3, 4, 5, 4],
    [4, 2, 3, 0, 2, 1, 3, 4],
    [4, 3, 0, 2, 1, 3, 4, 5],
    [5, 2, 3, 0, 2, 1, 3, 4],
    [0, 2, 3, 4, 5, 0, 2, 3, 4],
    [2, 3, 0, 2, 1, 3, 4, 5, 4],
    [3, 4, 2, 3, 0, 2, 1, 3, 4],
    [4, 2, 3, 0, 2, 1, 3, 4, 5],
    [1, 3, 4, 2, 3, 0, 2, 1, 3, 4],
    [3, 4, 2, 3, 0, 2, 1, 3, 4, 5],
    [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]] : List (List (Fin 6)))
@[expose] def e6n5U : List (List (Fin 6)) :=
  ([[],
    [4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4],
    [4, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4],
    [4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4],
    [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4],
    [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4]] : List (List (Fin 6)))
@[expose] def e6n5X : List (List ℤ) := [[-1, -1, 0, 1, 0, 0], [-1, 0, 0, 0, 0, 0], [-1, 0, 1, -1, 1, 0], [-1, 0, 1, 0, -1, 1], [-1, 0, 1, 0, 0, -1], [-1, 1, 0, 0, 0, 0], [0, -1, 0, 0, 0, 1], [0, -1, 0, 0, 1, -1], [0, -1, 0, 1, -1, 0], [0, -1, 1, 0, 0, 0], [0, 0, -1, 0, 1, 0], [0, 0, -1, 1, -1, 1], [0, 0, -1, 1, 0, -1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, -1], [0, 0, 0, 1, -1, 0], [0, 0, 1, -1, 0, 0], [0, 1, 0, -1, 0, 1], [0, 1, 0, -1, 1, -1], [0, 1, 0, 0, -1, 0], [0, 1, 1, -1, 0, 0], [1, -1, -1, 1, 0, 0], [1, 0, -1, 0, 0, 0], [1, 0, 0, -1, 1, 0], [1, 0, 0, 0, -1, 1], [1, 0, 0, 0, 0, -1], [1, 1, -1, 0, 0, 0]]
@[expose] def e6n5V : List ℤ := [2, 3, 4, 6, 5, 4]
theorem e6n5_hv0len : e6n5V.length = Tag.rank .E6 := by decide
theorem e6n5_hv0 : ∀ j : N6, j ≠ ⟨5, by decide⟩ → reflectL6 j e6n5V = e6n5V := by decide +kernel
theorem e6n5_hU1 : ∀ j : Fin 6, (e6n5U.getD j []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)) =
    List.ofFn (alphaF ⟨5, by decide⟩) := by decide +kernel
theorem e6n5_hU2 : ∀ j : Fin 6, (e6n5U.getD j []).foldr reflectL6
    (List.ofFn (Pi.single ⟨5, by decide⟩ (1 : ℤ) : N6 → ℤ)) = List.ofFn (Pi.single ⟨5, by decide⟩ (1 : ℤ) : N6 → ℤ) := by
  decide +kernel
theorem e6n5_hdist : ∀ j j' : Fin 6, j ≠ j' →
    (e6n5U.getD j []).foldr reflectL6 e6n5V ≠ (e6n5U.getD j' []).foldr reflectL6 e6n5V := by decide +kernel
theorem e6n5_hY : ∀ j j' : Fin 6, j ≠ j' →
    (e6n5U.getD j []).foldr refEL (List.ofFn (omegaF ⟨5, by decide⟩)) ≠
      (e6n5U.getD j' []).foldr refEL (List.ofFn (omegaF ⟨5, by decide⟩)) := by decide +kernel
theorem e6n5_hxorb : ∀ x ∈ e6n5X, ∀ y ∈ e6n5X, x ≠ y → 1 ≤ contentL (subL x y) ∧ contentL (subL x y) ≤ 2 := by
  decide +kernel
theorem e6n5_hβ : ∀ i i' : Fin 72, i ≠ i' →
    1 ≤ contentL (subL (((e6n5W).getD i []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)))
      (((e6n5W).getD i' []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)))) ∧
    contentL (subL (((e6n5W).getD i []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)))
      (((e6n5W).getD i' []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)))) ≤ 2 := by decide +kernel
theorem e6n5_hbdβ : ∀ i : Fin 72, ∀ c ∈ ((e6n5W).getD i []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)), |c| ≤ 2 := by
  decide +kernel
theorem e6n5_hbdX : ∀ (i : Fin 72) (j : Fin 6), ∀ c ∈ ((e6n5W).getD i []).foldr refEL
    ((e6n5U.getD j []).foldr refEL (List.ofFn (omegaF ⟨5, by decide⟩))), |c| ≤ 2 := by decide +kernel
theorem e6n5_hmem : ∀ (i : Fin 72) (j : Fin 6), ((e6n5W).getD i []).foldr refEL
    ((e6n5U.getD j []).foldr refEL (List.ofFn (omegaF ⟨5, by decide⟩))) ∈ e6n5X := by decide +kernel
@[expose] def e6n5Tab : NodeTab ⟨5, by decide⟩ where
  A := 72
  B := 6
  wTab := e6n5W
  uTab := e6n5U
  v0 := e6n5V
  xorb := e6n5X
  hv0len := e6n5_hv0len
  hv0 := e6n5_hv0
  hU1 := e6n5_hU1
  hU2 := e6n5_hU2
  hdist := e6n5_hdist
  hβ := e6n5_hβ
  hbdβ := e6n5_hbdβ
  hY := e6n5_hY
  hbdX := e6n5_hbdX
  hmem := e6n5_hmem
  hxorb := e6n5_hxorb
theorem e6n5S_hβ : ∀ i i' : Fin 14, i ≠ i' →
    1 ≤ contentL (subL (((e6n5W.take 14).getD i []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)))
      (((e6n5W.take 14).getD i' []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)))) ∧
    contentL (subL (((e6n5W.take 14).getD i []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)))
      (((e6n5W.take 14).getD i' []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)))) ≤ 2 := by decide +kernel
theorem e6n5S_hbdβ : ∀ i : Fin 14, ∀ c ∈ ((e6n5W.take 14).getD i []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩)), |c| ≤ 2 := by
  decide +kernel
theorem e6n5S_hbdX : ∀ (i : Fin 14) (j : Fin 6), ∀ c ∈ ((e6n5W.take 14).getD i []).foldr refEL
    ((e6n5U.getD j []).foldr refEL (List.ofFn (omegaF ⟨5, by decide⟩))), |c| ≤ 2 := by decide +kernel
theorem e6n5S_hmem : ∀ (i : Fin 14) (j : Fin 6), ((e6n5W.take 14).getD i []).foldr refEL
    ((e6n5U.getD j []).foldr refEL (List.ofFn (omegaF ⟨5, by decide⟩))) ∈ e6n5X := by decide +kernel
@[expose] def e6n5STab : NodeTab ⟨5, by decide⟩ where
  A := 14
  B := 6
  wTab := e6n5W.take 14
  uTab := e6n5U
  v0 := e6n5V
  xorb := e6n5X
  hv0len := e6n5_hv0len
  hv0 := e6n5_hv0
  hU1 := e6n5_hU1
  hU2 := e6n5_hU2
  hdist := e6n5_hdist
  hβ := e6n5S_hβ
  hbdβ := e6n5S_hbdβ
  hY := e6n5_hY
  hbdX := e6n5S_hbdX
  hmem := e6n5S_hmem
  hxorb := e6n5_hxorb
theorem e6n5_small : smallCheck ⟨5, by decide⟩ (e6n5W.take 14) e6n5U 14 6 = true := by decide +kernel
theorem e6n5_prim : ∀ i : Fin 72, contentL (((e6n5W).getD i []).foldr refEL (List.ofFn (alphaF ⟨5, by decide⟩))) = 1 := by
  decide +kernel
@[expose] def e6n1W : List (List (Fin 6)) :=
  ([[],
    [1],
    [3],
    [1, 3],
    [2, 3],
    [3, 1],
    [4, 3],
    [0, 2, 3],
    [1, 3, 1],
    [2, 1, 3],
    [2, 3, 1],
    [4, 1, 3],
    [4, 2, 3],
    [4, 3, 1],
    [5, 4, 3],
    [0, 2, 1, 3],
    [0, 2, 3, 1],
    [2, 1, 3, 1],
    [3, 2, 1, 3],
    [3, 4, 1, 3],
    [3, 4, 2, 3],
    [4, 0, 2, 3],
    [4, 1, 3, 1],
    [4, 2, 1, 3],
    [4, 2, 3, 1],
    [5, 4, 1, 3],
    [5, 4, 2, 3],
    [5, 4, 3, 1],
    [0, 2, 1, 3, 1],
    [3, 0, 2, 1, 3],
    [3, 2, 1, 3, 1],
    [3, 4, 0, 2, 3],
    [3, 4, 1, 3, 1],
    [3, 4, 2, 3, 1],
    [4, 0, 2, 1, 3],
    [4, 0, 2, 3, 1],
    [4, 2, 1, 3, 1],
    [5, 3, 4, 1, 3],
    [5, 3, 4, 2, 3],
    [5, 4, 0, 2, 3],
    [5, 4, 1, 3, 1],
    [5, 4, 2, 1, 3],
    [5, 4, 2, 3, 1],
    [2, 3, 0, 2, 1, 3],
    [2, 3, 4, 0, 2, 3],
    [3, 0, 2, 1, 3, 1],
    [3, 4, 0, 2, 3, 1],
    [4, 0, 2, 1, 3, 1],
    [4, 5, 3, 4, 1, 3],
    [4, 5, 3, 4, 2, 3],
    [5, 3, 4, 0, 2, 3],
    [5, 3, 4, 1, 3, 1],
    [5, 3, 4, 2, 3, 1],
    [5, 4, 0, 2, 1, 3],
    [5, 4, 0, 2, 3, 1],
    [5, 4, 2, 1, 3, 1],
    [2, 3, 0, 2, 1, 3, 1],
    [2, 3, 4, 0, 2, 3, 1],
    [4, 5, 3, 4, 0, 2, 3],
    [4, 5, 3, 4, 1, 3, 1],
    [4, 5, 3, 4, 2, 3, 1],
    [5, 2, 3, 4, 0, 2, 3],
    [5, 3, 4, 0, 2, 3, 1],
    [5, 4, 0, 2, 1, 3, 1],
    [4, 5, 2, 3, 4, 0, 2, 3],
    [4, 5, 3, 4, 0, 2, 3, 1],
    [5, 2, 3, 4, 0, 2, 3, 1],
    [3, 4, 5, 2, 3, 4, 0, 2, 3],
    [4, 5, 2, 3, 4, 0, 2, 3, 1],
    [1, 3, 4, 5, 2, 3, 4, 0, 2, 3],
    [3, 4, 5, 2, 3, 4, 0, 2, 3, 1],
    [1, 3, 4, 5, 2, 3, 4, 0, 2, 3, 1]] : List (List (Fin 6)))
@[expose] def e6n1U : List (List (Fin 6)) :=
  ([[],
    [3, 2, 1, 3, 4, 3, 2, 1, 3],
    [3, 0, 2, 1, 3, 4, 3, 2, 1, 3],
    [5, 3, 2, 1, 3, 4, 3, 2, 1, 3],
    [2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3],
    [4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3],
    [5, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3],
    [4, 5, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3],
    [5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3],
    [4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3],
    [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3],
    [3, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3],
    [4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3],
    [3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3],
    [4, 3, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3],
    [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3],
    [4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3],
    [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3],
    [5, 4, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3],
    [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]] : List (List (Fin 6)))
@[expose] def e6n1X : List (List ℤ) := [[-2, 0, 1, 0, 0, 0], [-1, -1, 0, 0, 1, 0], [-1, -1, 0, 1, -1, 1], [-1, -1, 0, 1, 0, -1], [-1, -1, 1, 0, 0, 1], [-1, -1, 1, 0, 1, -1], [-1, -1, 1, 1, -1, 0], [-1, 0, -1, 1, 0, 0], [-1, 0, 0, 0, 1, 0], [-1, 0, 0, 1, -1, 1], [-1, 0, 0, 1, 0, -1], [-1, 0, 1, -1, 0, 1], [-1, 0, 1, -1, 1, -1], [-1, 0, 1, 0, -1, 0], [-1, 0, 2, -1, 0, 0], [-1, 1, 0, -1, 1, 0], [-1, 1, 0, 0, -1, 1], [-1, 1, 0, 0, 0, -1], [-1, 1, 1, -1, 0, 1], [-1, 1, 1, -1, 1, -1], [-1, 1, 1, 0, -1, 0], [0, -2, 0, 1, 0, 0], [0, -1, -1, 1, 0, 1], [0, -1, -1, 1, 1, -1], [0, -1, -1, 2, -1, 0], [0, -1, 0, 0, 0, 0], [0, -1, 0, 1, 0, 0], [0, -1, 1, -1, 1, 0], [0, -1, 1, 0, -1, 1], [0, -1, 1, 0, 0, -1], [0, 0, -1, 0, 0, 1], [0, 0, -1, 0, 1, -1], [0, 0, -1, 1, -1, 0], [0, 0, 0, -1, 1, 1], [0, 0, 0, -1, 2, -1], [0, 0, 0, 0, -1, 2], [0, 0, 0, 0, 1, -2], [0, 0, 0, 1, -2, 1], [0, 0, 0, 1, -1, -1], [0, 0, 1, -1, 1, 0], [0, 0, 1, 0, -1, 1], [0, 0, 1, 0, 0, -1], [0, 1, -1, 0, 0, 1], [0, 1, -1, 0, 1, -1], [0, 1, -1, 1, -1, 0], [0, 1, 0, -1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 1, 1, -2, 1, 0], [0, 1, 1, -1, -1, 1], [0, 1, 1, -1, 0, -1], [0, 2, 0, -1, 0, 0], [1, -1, -1, 0, 1, 0], [1, -1, -1, 1, -1, 1], [1, -1, -1, 1, 0, -1], [1, -1, 0, 0, 0, 1], [1, -1, 0, 0, 1, -1], [1, -1, 0, 1, -1, 0], [1, 0, -2, 1, 0, 0], [1, 0, -1, 0, 1, 0], [1, 0, -1, 1, -1, 1], [1, 0, -1, 1, 0, -1], [1, 0, 0, -1, 0, 1], [1, 0, 0, -1, 1, -1], [1, 0, 0, 0, -1, 0], [1, 0, 1, -1, 0, 0], [1, 1, -1, -1, 1, 0], [1, 1, -1, 0, -1, 1], [1, 1, -1, 0, 0, -1], [1, 1, 0, -1, 0, 1], [1, 1, 0, -1, 1, -1], [1, 1, 0, 0, -1, 0], [2, 0, -1, 0, 0, 0]]
@[expose] def e6n1V : List ℤ := [3, 6, 6, 9, 6, 3]
theorem e6n1_hv0len : e6n1V.length = Tag.rank .E6 := by decide
theorem e6n1_hv0 : ∀ j : N6, j ≠ ⟨1, by decide⟩ → reflectL6 j e6n1V = e6n1V := by decide +kernel
theorem e6n1_hU1 : ∀ j : Fin 20, (e6n1U.getD j []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)) =
    List.ofFn (alphaF ⟨1, by decide⟩) := by decide +kernel
theorem e6n1_hU2 : ∀ j : Fin 20, (e6n1U.getD j []).foldr reflectL6
    (List.ofFn (Pi.single ⟨1, by decide⟩ (1 : ℤ) : N6 → ℤ)) = List.ofFn (Pi.single ⟨1, by decide⟩ (1 : ℤ) : N6 → ℤ) := by
  decide +kernel
theorem e6n1_hdist : ∀ j j' : Fin 20, j ≠ j' →
    (e6n1U.getD j []).foldr reflectL6 e6n1V ≠ (e6n1U.getD j' []).foldr reflectL6 e6n1V := by decide +kernel
theorem e6n1_hY : ∀ j j' : Fin 20, j ≠ j' →
    (e6n1U.getD j []).foldr refEL (List.ofFn (omegaF ⟨1, by decide⟩)) ≠
      (e6n1U.getD j' []).foldr refEL (List.ofFn (omegaF ⟨1, by decide⟩)) := by decide +kernel
theorem e6n1_hxorb : ∀ x ∈ e6n1X, ∀ y ∈ e6n1X, x ≠ y → 1 ≤ contentL (subL x y) ∧ contentL (subL x y) ≤ 2 := by
  decide +kernel
theorem e6n1_hβ : ∀ i i' : Fin 72, i ≠ i' →
    1 ≤ contentL (subL (((e6n1W).getD i []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)))
      (((e6n1W).getD i' []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)))) ∧
    contentL (subL (((e6n1W).getD i []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)))
      (((e6n1W).getD i' []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)))) ≤ 2 := by decide +kernel
theorem e6n1_hbdβ : ∀ i : Fin 72, ∀ c ∈ ((e6n1W).getD i []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)), |c| ≤ 2 := by
  decide +kernel
theorem e6n1_hbdX : ∀ (i : Fin 72) (j : Fin 20), ∀ c ∈ ((e6n1W).getD i []).foldr refEL
    ((e6n1U.getD j []).foldr refEL (List.ofFn (omegaF ⟨1, by decide⟩))), |c| ≤ 2 := by decide +kernel
theorem e6n1_hmem : ∀ (i : Fin 72) (j : Fin 20), ((e6n1W).getD i []).foldr refEL
    ((e6n1U.getD j []).foldr refEL (List.ofFn (omegaF ⟨1, by decide⟩))) ∈ e6n1X := by decide +kernel
@[expose] def e6n1Tab : NodeTab ⟨1, by decide⟩ where
  A := 72
  B := 20
  wTab := e6n1W
  uTab := e6n1U
  v0 := e6n1V
  xorb := e6n1X
  hv0len := e6n1_hv0len
  hv0 := e6n1_hv0
  hU1 := e6n1_hU1
  hU2 := e6n1_hU2
  hdist := e6n1_hdist
  hβ := e6n1_hβ
  hbdβ := e6n1_hbdβ
  hY := e6n1_hY
  hbdX := e6n1_hbdX
  hmem := e6n1_hmem
  hxorb := e6n1_hxorb
theorem e6n1S_hβ : ∀ i i' : Fin 4, i ≠ i' →
    1 ≤ contentL (subL (((e6n1W.take 4).getD i []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)))
      (((e6n1W.take 4).getD i' []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)))) ∧
    contentL (subL (((e6n1W.take 4).getD i []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)))
      (((e6n1W.take 4).getD i' []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)))) ≤ 2 := by decide +kernel
theorem e6n1S_hbdβ : ∀ i : Fin 4, ∀ c ∈ ((e6n1W.take 4).getD i []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩)), |c| ≤ 2 := by
  decide +kernel
theorem e6n1S_hbdX : ∀ (i : Fin 4) (j : Fin 20), ∀ c ∈ ((e6n1W.take 4).getD i []).foldr refEL
    ((e6n1U.getD j []).foldr refEL (List.ofFn (omegaF ⟨1, by decide⟩))), |c| ≤ 2 := by decide +kernel
theorem e6n1S_hmem : ∀ (i : Fin 4) (j : Fin 20), ((e6n1W.take 4).getD i []).foldr refEL
    ((e6n1U.getD j []).foldr refEL (List.ofFn (omegaF ⟨1, by decide⟩))) ∈ e6n1X := by decide +kernel
@[expose] def e6n1STab : NodeTab ⟨1, by decide⟩ where
  A := 4
  B := 20
  wTab := e6n1W.take 4
  uTab := e6n1U
  v0 := e6n1V
  xorb := e6n1X
  hv0len := e6n1_hv0len
  hv0 := e6n1_hv0
  hU1 := e6n1_hU1
  hU2 := e6n1_hU2
  hdist := e6n1_hdist
  hβ := e6n1S_hβ
  hbdβ := e6n1S_hbdβ
  hY := e6n1_hY
  hbdX := e6n1S_hbdX
  hmem := e6n1S_hmem
  hxorb := e6n1_hxorb
theorem e6n1_small : smallCheck ⟨1, by decide⟩ (e6n1W.take 4) e6n1U 4 20 = true := by decide +kernel
theorem e6n1_prim : ∀ i : Fin 72, contentL (((e6n1W).getD i []).foldr refEL (List.ofFn (alphaF ⟨1, by decide⟩))) = 1 := by
  decide +kernel

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
