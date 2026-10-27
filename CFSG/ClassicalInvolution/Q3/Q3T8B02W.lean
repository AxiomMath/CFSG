module

public import CFSG.ClassicalInvolution.Asc77.AscP1Thompson3T
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonCox
public import CFSG.ClassicalInvolution.Asc77.AscMuTabWyl
public import CFSG.Mathlib.Decide.Nodup
public import CFSG.ClassicalInvolution.Asc77.AscMuTabGroup

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

namespace Wyl4

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Cox
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.Star3T

def tabOf (σ : Equiv.Perm (Fin 8)) : List ℕ := (List.finRange 8).map fun i => (σ i).val

def tcomp (a b : List ℕ) : List ℕ := b.map fun j => a.getD j 0

def tid : List ℕ := List.range 8

theorem getD_tabOf (σ : Equiv.Perm (Fin 8)) (k : Fin 8) : (tabOf σ).getD k.val 0 = (σ k).val := by
  simp [tabOf, List.getD_eq_getElem?_getD]

theorem tabOf_mul (σ τ : Equiv.Perm (Fin 8)) : tabOf (σ * τ) = tcomp (tabOf σ) (tabOf τ) := by
  simp only [tabOf, tcomp, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp

theorem tabOf_one : tabOf 1 = tid := by decide

theorem tabOf_injective : Function.Injective tabOf := by
  intro σ τ h
  ext k
  have h1 := getD_tabOf σ k
  have h2 := getD_tabOf τ k
  rw [h] at h1
  exact h1.symm.trans h2

def words : List (List (Fin 4)) :=
  [[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 0], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1],
    [0, 1, 0], [0, 1, 2], [0, 1, 3], [0, 2, 1], [0, 2, 3], [0, 3, 1], [1, 0, 2], [1, 0, 3],
    [1, 2, 1], [1, 2, 3], [1, 3, 1], [2, 1, 0], [2, 1, 3], [2, 3, 1], [3, 1, 0], [3, 1, 2],
    [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 2, 1], [0, 1, 2, 3], [0, 1, 3, 1], [0, 2, 1, 0],
    [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 0], [0, 3, 1, 2], [1, 0, 2, 1], [1, 0, 2, 3],
    [1, 0, 3, 1], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 3, 1], [1, 3, 1, 0], [1, 3, 1, 2],
    [2, 1, 0, 3], [2, 1, 3, 1], [2, 3, 1, 0], [2, 3, 1, 2], [3, 1, 0, 2], [0, 1, 0, 2, 1],
    [0, 1, 0, 2, 3], [0, 1, 0, 3, 1], [0, 1, 2, 1, 0], [0, 1, 2, 1, 3], [0, 1, 2, 3, 1],
    [0, 1, 3, 1, 0], [0, 1, 3, 1, 2], [0, 2, 1, 0, 3], [0, 2, 1, 3, 1], [0, 2, 3, 1, 0],
    [0, 2, 3, 1, 2], [0, 3, 1, 0, 2], [1, 0, 2, 1, 0], [1, 0, 2, 1, 3], [1, 0, 2, 3, 1],
    [1, 0, 3, 1, 0], [1, 0, 3, 1, 2], [1, 2, 1, 0, 3], [1, 2, 1, 3, 1], [1, 2, 3, 1, 0],
    [1, 2, 3, 1, 2], [1, 3, 1, 0, 2], [2, 1, 0, 3, 1], [2, 1, 3, 1, 0], [2, 1, 3, 1, 2],
    [2, 3, 1, 0, 2], [3, 1, 0, 2, 1], [0, 1, 0, 2, 1, 0], [0, 1, 0, 2, 1, 3], [0, 1, 0, 2, 3, 1],
    [0, 1, 0, 3, 1, 0], [0, 1, 0, 3, 1, 2], [0, 1, 2, 1, 0, 3], [0, 1, 2, 1, 3, 1],
    [0, 1, 2, 3, 1, 0], [0, 1, 2, 3, 1, 2], [0, 1, 3, 1, 0, 2], [0, 2, 1, 0, 3, 1],
    [0, 2, 1, 3, 1, 0], [0, 2, 1, 3, 1, 2], [0, 2, 3, 1, 0, 2], [0, 3, 1, 0, 2, 1],
    [1, 0, 2, 1, 0, 3], [1, 0, 2, 1, 3, 1], [1, 0, 2, 3, 1, 0], [1, 0, 2, 3, 1, 2],
    [1, 0, 3, 1, 0, 2], [1, 2, 1, 0, 3, 1], [1, 2, 1, 3, 1, 0], [1, 2, 1, 3, 1, 2],
    [1, 2, 3, 1, 0, 2], [1, 3, 1, 0, 2, 1], [2, 1, 0, 3, 1, 0], [2, 1, 0, 3, 1, 2],
    [2, 1, 3, 1, 0, 2], [2, 3, 1, 0, 2, 1], [3, 1, 0, 2, 1, 3], [0, 1, 0, 2, 1, 0, 3],
    [0, 1, 0, 2, 1, 3, 1], [0, 1, 0, 2, 3, 1, 0], [0, 1, 0, 2, 3, 1, 2], [0, 1, 0, 3, 1, 0, 2],
    [0, 1, 2, 1, 0, 3, 1], [0, 1, 2, 1, 3, 1, 0], [0, 1, 2, 1, 3, 1, 2], [0, 1, 2, 3, 1, 0, 2],
    [0, 1, 3, 1, 0, 2, 1], [0, 2, 1, 0, 3, 1, 0], [0, 2, 1, 0, 3, 1, 2], [0, 2, 1, 3, 1, 0, 2],
    [0, 2, 3, 1, 0, 2, 1], [0, 3, 1, 0, 2, 1, 3], [1, 0, 2, 1, 0, 3, 1], [1, 0, 2, 1, 3, 1, 0],
    [1, 0, 2, 1, 3, 1, 2], [1, 0, 2, 3, 1, 0, 2], [1, 0, 3, 1, 0, 2, 1], [1, 2, 1, 0, 3, 1, 0],
    [1, 2, 1, 0, 3, 1, 2], [1, 2, 1, 3, 1, 0, 2], [1, 2, 3, 1, 0, 2, 1], [1, 3, 1, 0, 2, 1, 3],
    [2, 1, 0, 3, 1, 0, 2], [2, 1, 3, 1, 0, 2, 1], [2, 3, 1, 0, 2, 1, 3], [0, 1, 0, 2, 1, 0, 3, 1],
    [0, 1, 0, 2, 1, 3, 1, 0], [0, 1, 0, 2, 1, 3, 1, 2], [0, 1, 0, 2, 3, 1, 0, 2],
    [0, 1, 0, 3, 1, 0, 2, 1], [0, 1, 2, 1, 0, 3, 1, 0], [0, 1, 2, 1, 0, 3, 1, 2],
    [0, 1, 2, 1, 3, 1, 0, 2], [0, 1, 2, 3, 1, 0, 2, 1], [0, 1, 3, 1, 0, 2, 1, 3],
    [0, 2, 1, 0, 3, 1, 0, 2], [0, 2, 1, 3, 1, 0, 2, 1], [0, 2, 3, 1, 0, 2, 1, 3],
    [1, 0, 2, 1, 0, 3, 1, 0], [1, 0, 2, 1, 0, 3, 1, 2], [1, 0, 2, 1, 3, 1, 0, 2],
    [1, 0, 2, 3, 1, 0, 2, 1], [1, 0, 3, 1, 0, 2, 1, 3], [1, 2, 1, 0, 3, 1, 0, 2],
    [1, 2, 1, 3, 1, 0, 2, 1], [1, 2, 3, 1, 0, 2, 1, 3], [2, 1, 0, 3, 1, 0, 2, 1],
    [2, 1, 3, 1, 0, 2, 1, 3], [0, 1, 0, 2, 1, 0, 3, 1, 0], [0, 1, 0, 2, 1, 0, 3, 1, 2],
    [0, 1, 0, 2, 1, 3, 1, 0, 2], [0, 1, 0, 2, 3, 1, 0, 2, 1], [0, 1, 0, 3, 1, 0, 2, 1, 3],
    [0, 1, 2, 1, 0, 3, 1, 0, 2], [0, 1, 2, 1, 3, 1, 0, 2, 1], [0, 1, 2, 3, 1, 0, 2, 1, 3],
    [0, 2, 1, 0, 3, 1, 0, 2, 1], [0, 2, 1, 3, 1, 0, 2, 1, 3], [1, 0, 2, 1, 0, 3, 1, 0, 2],
    [1, 0, 2, 1, 3, 1, 0, 2, 1], [1, 0, 2, 3, 1, 0, 2, 1, 3], [1, 2, 1, 0, 3, 1, 0, 2, 1],
    [1, 2, 1, 3, 1, 0, 2, 1, 3], [2, 1, 0, 3, 1, 0, 2, 1, 3], [0, 1, 0, 2, 1, 0, 3, 1, 0, 2],
    [0, 1, 0, 2, 1, 3, 1, 0, 2, 1], [0, 1, 0, 2, 3, 1, 0, 2, 1, 3], [0, 1, 2, 1, 0, 3, 1, 0, 2, 1],
    [0, 1, 2, 1, 3, 1, 0, 2, 1, 3], [0, 2, 1, 0, 3, 1, 0, 2, 1, 3], [1, 0, 2, 1, 0, 3, 1, 0, 2, 1],
    [1, 0, 2, 1, 3, 1, 0, 2, 1, 3], [1, 2, 1, 0, 3, 1, 0, 2, 1, 3],
    [0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1], [0, 1, 0, 2, 1, 3, 1, 0, 2, 1, 3],
    [0, 1, 2, 1, 0, 3, 1, 0, 2, 1, 3], [1, 0, 2, 1, 0, 3, 1, 0, 2, 1, 3],
    [0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 1, 3]]

def elts : List (Equiv.Perm (Fin 8)) := words.map (wp wylPerm)

def wtab (w : List (Fin 4)) : List ℕ := tabOf (wp wylPerm w)

def eltsT : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7], [1, 0, 2, 3, 5, 4, 6, 7], [0, 2, 1, 3, 4, 6, 5, 7],
    [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 7, 6, 4, 5, 3, 2], [1, 2, 0, 3, 5, 6, 4, 7],
    [1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 7, 6, 5, 4, 3, 2], [2, 0, 1, 3, 6, 4, 5, 7],
    [0, 2, 3, 1, 4, 6, 7, 5], [0, 2, 7, 5, 4, 6, 3, 1], [0, 3, 1, 2, 4, 7, 5, 6],
    [0, 1, 6, 7, 4, 5, 2, 3], [0, 7, 1, 6, 4, 3, 5, 2], [2, 1, 0, 3, 6, 5, 4, 7],
    [1, 2, 3, 0, 5, 6, 7, 4], [1, 2, 7, 4, 5, 6, 3, 0], [1, 3, 0, 2, 5, 7, 4, 6],
    [1, 0, 6, 7, 5, 4, 2, 3], [1, 7, 0, 6, 5, 3, 4, 2], [2, 0, 3, 1, 6, 4, 7, 5],
    [2, 0, 7, 5, 6, 4, 3, 1], [0, 3, 2, 1, 4, 7, 6, 5], [0, 2, 5, 7, 4, 6, 1, 3],
    [0, 7, 2, 5, 4, 3, 6, 1], [3, 0, 1, 2, 7, 4, 5, 6], [0, 3, 6, 5, 4, 7, 2, 1],
    [0, 6, 1, 7, 4, 2, 5, 3], [7, 0, 1, 6, 3, 4, 5, 2], [0, 7, 6, 1, 4, 3, 2, 5],
    [2, 1, 3, 0, 6, 5, 7, 4], [2, 1, 7, 4, 6, 5, 3, 0], [1, 3, 2, 0, 5, 7, 6, 4],
    [1, 2, 4, 7, 5, 6, 0, 3], [1, 7, 2, 4, 5, 3, 6, 0], [3, 1, 0, 2, 7, 5, 4, 6],
    [1, 3, 6, 4, 5, 7, 2, 0], [1, 6, 0, 7, 5, 2, 4, 3], [7, 1, 0, 6, 3, 5, 4, 2],
    [1, 7, 6, 0, 5, 3, 2, 4], [2, 3, 0, 1, 6, 7, 4, 5], [2, 0, 5, 7, 6, 4, 1, 3],
    [2, 7, 0, 5, 6, 3, 4, 1], [3, 0, 2, 1, 7, 4, 6, 5], [0, 3, 5, 6, 4, 7, 1, 2],
    [0, 5, 2, 7, 4, 1, 6, 3], [7, 0, 2, 5, 3, 4, 6, 1], [0, 7, 5, 2, 4, 3, 1, 6],
    [3, 0, 6, 5, 7, 4, 2, 1], [0, 6, 3, 5, 4, 2, 7, 1], [6, 0, 1, 7, 2, 4, 5, 3],
    [0, 6, 7, 1, 4, 2, 3, 5], [7, 0, 6, 1, 3, 4, 2, 5], [2, 3, 1, 0, 6, 7, 5, 4],
    [2, 1, 4, 7, 6, 5, 0, 3], [2, 7, 1, 4, 6, 3, 5, 0], [3, 1, 2, 0, 7, 5, 6, 4],
    [1, 3, 4, 6, 5, 7, 0, 2], [1, 4, 2, 7, 5, 0, 6, 3], [7, 1, 2, 4, 3, 5, 6, 0],
    [1, 7, 4, 2, 5, 3, 0, 6], [3, 1, 6, 4, 7, 5, 2, 0], [1, 6, 3, 4, 5, 2, 7, 0],
    [6, 1, 0, 7, 2, 5, 4, 3], [1, 6, 7, 0, 5, 2, 3, 4], [7, 1, 6, 0, 3, 5, 2, 4],
    [3, 2, 0, 1, 7, 6, 4, 5], [2, 3, 5, 4, 6, 7, 1, 0], [2, 5, 0, 7, 6, 1, 4, 3],
    [7, 2, 0, 5, 3, 6, 4, 1], [2, 7, 5, 0, 6, 3, 1, 4], [3, 0, 5, 6, 7, 4, 1, 2],
    [0, 5, 3, 6, 4, 1, 7, 2], [5, 0, 2, 7, 1, 4, 6, 3], [0, 5, 7, 2, 4, 1, 3, 6],
    [7, 0, 5, 2, 3, 4, 1, 6], [3, 6, 0, 5, 7, 2, 4, 1], [6, 0, 3, 5, 2, 4, 7, 1],
    [0, 6, 5, 3, 4, 2, 1, 7], [6, 0, 7, 1, 2, 4, 3, 5], [7, 6, 0, 1, 3, 2, 4, 5],
    [3, 2, 1, 0, 7, 6, 5, 4], [2, 3, 4, 5, 6, 7, 0, 1], [2, 4, 1, 7, 6, 0, 5, 3],
    [7, 2, 1, 4, 3, 6, 5, 0], [2, 7, 4, 1, 6, 3, 0, 5], [3, 1, 4, 6, 7, 5, 0, 2],
    [1, 4, 3, 6, 5, 0, 7, 2], [4, 1, 2, 7, 0, 5, 6, 3], [1, 4, 7, 2, 5, 0, 3, 6],
    [7, 1, 4, 2, 3, 5, 0, 6], [3, 6, 1, 4, 7, 2, 5, 0], [6, 1, 3, 4, 2, 5, 7, 0],
    [1, 6, 4, 3, 5, 2, 0, 7], [6, 1, 7, 0, 2, 5, 3, 4], [7, 6, 1, 0, 3, 2, 5, 4],
    [3, 2, 5, 4, 7, 6, 1, 0], [2, 5, 3, 4, 6, 1, 7, 0], [5, 2, 0, 7, 1, 6, 4, 3],
    [2, 5, 7, 0, 6, 1, 3, 4], [7, 2, 5, 0, 3, 6, 1, 4], [3, 5, 0, 6, 7, 1, 4, 2],
    [5, 0, 3, 6, 1, 4, 7, 2], [0, 5, 6, 3, 4, 1, 2, 7], [5, 0, 7, 2, 1, 4, 3, 6],
    [7, 5, 0, 2, 3, 1, 4, 6], [6, 3, 0, 5, 2, 7, 4, 1], [3, 6, 5, 0, 7, 2, 1, 4],
    [6, 0, 5, 3, 2, 4, 1, 7], [6, 7, 0, 1, 2, 3, 4, 5], [7, 6, 5, 4, 3, 2, 1, 0],
    [3, 2, 4, 5, 7, 6, 0, 1], [2, 4, 3, 5, 6, 0, 7, 1], [4, 2, 1, 7, 0, 6, 5, 3],
    [2, 4, 7, 1, 6, 0, 3, 5], [7, 2, 4, 1, 3, 6, 0, 5], [3, 4, 1, 6, 7, 0, 5, 2],
    [4, 1, 3, 6, 0, 5, 7, 2], [1, 4, 6, 3, 5, 0, 2, 7], [4, 1, 7, 2, 0, 5, 3, 6],
    [7, 4, 1, 2, 3, 0, 5, 6], [6, 3, 1, 4, 2, 7, 5, 0], [3, 6, 4, 1, 7, 2, 0, 5],
    [6, 1, 4, 3, 2, 5, 0, 7], [6, 7, 1, 0, 2, 3, 5, 4], [7, 6, 4, 5, 3, 2, 0, 1],
    [3, 5, 2, 4, 7, 1, 6, 0], [5, 2, 3, 4, 1, 6, 7, 0], [2, 5, 4, 3, 6, 1, 0, 7],
    [5, 2, 7, 0, 1, 6, 3, 4], [7, 5, 2, 0, 3, 1, 6, 4], [5, 3, 0, 6, 1, 7, 4, 2],
    [3, 5, 6, 0, 7, 1, 2, 4], [5, 0, 6, 3, 1, 4, 2, 7], [5, 7, 0, 2, 1, 3, 4, 6],
    [7, 5, 6, 4, 3, 1, 2, 0], [6, 3, 5, 0, 2, 7, 1, 4], [6, 5, 0, 3, 2, 1, 4, 7],
    [6, 7, 5, 4, 2, 3, 1, 0], [3, 4, 2, 5, 7, 0, 6, 1], [4, 2, 3, 5, 0, 6, 7, 1],
    [2, 4, 5, 3, 6, 0, 1, 7], [4, 2, 7, 1, 0, 6, 3, 5], [7, 4, 2, 1, 3, 0, 6, 5],
    [4, 3, 1, 6, 0, 7, 5, 2], [3, 4, 6, 1, 7, 0, 2, 5], [4, 1, 6, 3, 0, 5, 2, 7],
    [4, 7, 1, 2, 0, 3, 5, 6], [7, 4, 6, 5, 3, 0, 2, 1], [6, 3, 4, 1, 2, 7, 0, 5],
    [6, 4, 1, 3, 2, 0, 5, 7], [6, 7, 4, 5, 2, 3, 0, 1], [5, 3, 2, 4, 1, 7, 6, 0],
    [3, 5, 4, 2, 7, 1, 0, 6], [5, 2, 4, 3, 1, 6, 0, 7], [5, 7, 2, 0, 1, 3, 6, 4],
    [7, 5, 4, 6, 3, 1, 0, 2], [5, 3, 6, 0, 1, 7, 2, 4], [5, 6, 0, 3, 1, 2, 4, 7],
    [5, 7, 6, 4, 1, 3, 2, 0], [6, 5, 3, 0, 2, 1, 7, 4], [6, 5, 7, 4, 2, 1, 3, 0],
    [4, 3, 2, 5, 0, 7, 6, 1], [3, 4, 5, 2, 7, 0, 1, 6], [4, 2, 5, 3, 0, 6, 1, 7],
    [4, 7, 2, 1, 0, 3, 6, 5], [7, 4, 5, 6, 3, 0, 1, 2], [4, 3, 6, 1, 0, 7, 2, 5],
    [4, 6, 1, 3, 0, 2, 5, 7], [4, 7, 6, 5, 0, 3, 2, 1], [6, 4, 3, 1, 2, 0, 7, 5],
    [6, 4, 7, 5, 2, 0, 3, 1], [5, 3, 4, 2, 1, 7, 0, 6], [5, 4, 2, 3, 1, 0, 6, 7],
    [5, 7, 4, 6, 1, 3, 0, 2], [5, 6, 3, 0, 1, 2, 7, 4], [5, 6, 7, 4, 1, 2, 3, 0],
    [6, 5, 4, 7, 2, 1, 0, 3], [4, 3, 5, 2, 0, 7, 1, 6], [4, 5, 2, 3, 0, 1, 6, 7],
    [4, 7, 5, 6, 0, 3, 1, 2], [4, 6, 3, 1, 0, 2, 7, 5], [4, 6, 7, 5, 0, 2, 3, 1],
    [6, 4, 5, 7, 2, 0, 1, 3], [5, 4, 3, 2, 1, 0, 7, 6], [5, 4, 7, 6, 1, 0, 3, 2],
    [5, 6, 4, 7, 1, 2, 0, 3], [4, 5, 3, 2, 0, 1, 7, 6], [4, 5, 7, 6, 0, 1, 3, 2],
    [4, 6, 5, 7, 0, 2, 1, 3], [5, 4, 6, 7, 1, 0, 2, 3], [4, 5, 6, 7, 0, 1, 2, 3]]

theorem words_length : words.length = 192 := by decide +kernel

theorem eltsT_eq : eltsT = words.map wtab := by decide +kernel

theorem eltsT_nodup : eltsT.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup
    (fun t : List ℕ => t.getD 0 0 + 8 * (t.getD 1 0 + 8 * t.getD 2 0)) (by decide +kernel)

theorem model {Q : Type*} [Group Q] (e : Q ≃* coxeterD4.Group) :
    ∃ (θ : Q → List ℕ) (ε : Q →* ℤˣ), (∀ a b, θ (a * b) = tcomp (θ a) (θ b)) ∧ θ 1 = tid ∧
      Function.Injective θ ∧ (∀ q, ∃ w ∈ words, θ q = wtab w ∧ ε q = (-1) ^ w.length) ∧
      (∀ t ∈ eltsT, ∃ q, θ q = t) ∧ ∃ q₀, ε q₀ ≠ 1 := by
  classical
  let cs : CoxeterSystem coxeterD4 coxeterD4.Group := coxeterD4.toCoxeterSystem
  let φ : coxeterD4.Group →* Equiv.Perm (Fin 8) := cs.lift ⟨wylPerm, wylPerm_liftable⟩
  have hl : coxeterD4.IsLiftable (fun _ : Fin 4 => (-1 : ℤˣ)) := fun i j => by simp
  let ε : coxeterD4.Group →* ℤˣ := cs.lift ⟨fun _ => -1, hl⟩
  have hφs : ∀ i, φ (cs.simple i) = wylPerm i := fun i => cs.lift_apply_simple wylPerm_liftable i
  have hεs : ∀ i, ε (cs.simple i) = -1 := fun i => cs.lift_apply_simple hl i
  have hφw : ∀ w : List (Fin 4), φ (wp cs.simple w) = wp wylPerm w := by
    intro w
    unfold wp
    rw [map_list_prod, List.map_map]
    have : (φ ∘ cs.simple) = wylPerm := funext hφs
    rw [this]
  have hεw : ∀ w : List (Fin 4), ε (wp cs.simple w) = (-1) ^ w.length := by
    intro w
    unfold wp
    rw [map_list_prod, List.map_map]
    have : (ε ∘ cs.simple) = fun _ => (-1 : ℤˣ) := funext hεs
    rw [this, List.map_const', List.prod_replicate]
  obtain ⟨hfin, hcard⟩ := finite_card_D4 (M := coxeterD4)
    (fun i j => by fin_cases i <;> fin_cases j <;> rfl) cs
  have : Finite coxeterD4.Group := hfin
  have helts_nodup : elts.Nodup := by
    have h1 : (elts.map tabOf).Nodup := by
      have : elts.map tabOf = eltsT := by
        rw [eltsT_eq]
        simp only [elts, List.map_map]
        rfl
      rw [this]
      exact eltsT_nodup
    exact List.Nodup.of_map _ h1
  have hsub : (↑elts.toFinset : Set (Equiv.Perm (Fin 8))) ⊆ Set.range φ := by
    intro σ hσ
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hσ))
    exact ⟨wp cs.simple w, hφw w⟩
  have hcard192 : (↑elts.toFinset : Set (Equiv.Perm (Fin 8))).ncard = 192 := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup helts_nodup]
    simp [elts, words_length]
  have hupp : (Set.range φ).ncard ≤ 192 := by
    calc (Set.range φ).ncard = Nat.card (Set.range φ) := (Nat.card_coe_set_eq _).symm
      _ ≤ Nat.card coxeterD4.Group := Finite.card_range_le φ
      _ ≤ 192 := hcard
  have hrange : (↑elts.toFinset : Set (Equiv.Perm (Fin 8))) = Set.range φ :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  have hφinj : Function.Injective φ := by
    have hlow : 192 ≤ Nat.card (Set.range φ) := by
      rw [Nat.card_coe_set_eq, ← hrange, hcard192]
    have hbij : Function.Bijective (Set.rangeFactorization φ) :=
      Set.rangeFactorization_surjective.bijective_of_nat_card_le (by omega)
    intro a b hab
    exact hbij.1 (Subtype.ext hab)
  have hφmem : ∀ g, ∃ w ∈ words, wp wylPerm w = φ g := by
    intro g
    have : φ g ∈ (↑elts.toFinset : Set (Equiv.Perm (Fin 8))) := by
      rw [hrange]; exact ⟨g, rfl⟩
    exact List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp this))
  refine ⟨fun q => tabOf (φ (e q)), ε.comp e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    simp [tabOf_mul]
  · simp [tabOf_one]
  · exact tabOf_injective.comp (hφinj.comp e.injective)
  · intro q
    obtain ⟨w, hw, hwq⟩ := hφmem (e q)
    have hq : e q = wp cs.simple w := hφinj (by rw [hφw, hwq])
    refine ⟨w, hw, ?_, ?_⟩
    · simp only [wtab, hwq]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hq, hεw]
  · intro t ht
    rw [eltsT_eq] at ht
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp ht
    exact ⟨e.symm (wp cs.simple w), by simp [hφw, wtab]⟩
  · refine ⟨e.symm (cs.simple 0), ?_⟩
    simp [hεs]

end Wyl4

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
