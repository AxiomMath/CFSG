module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairGraph
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open Matrix

theorem dotL_ofFn {n : ℕ} (a b : Fin n → ℤ) : dotL (List.ofFn a) (List.ofFn b) = a ⬝ᵥ b := by
  have : List.zipWith (· * ·) (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => a i * b i) := by
    apply List.ext_getElem <;> simp
  rw [dotL, this, List.sum_ofFn]
  rfl

theorem zipWith_add_ofFn {n : ℕ} (a b : Fin n → ℤ) :
    List.zipWith (· + ·) (List.ofFn a) (List.ofFn b) = List.ofFn (a + b) := by
  apply List.ext_getElem <;> simp

variable {n d : ℕ} (R W : List (List ℤ)) (nbL order : List ℕ) (wR wW budget : ℕ)
  (wt : ℕ → Fin n → ℤ) (Pos : (Fin n → ℤ) → Prop)

theorem getD_idxOf {l : List ℤ} (hl : l ∈ R) : R.getD (R.idxOf l) [] = l := by
  have h : R.idxOf l < R.length := List.idxOf_lt_length_iff.2 hl
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_W (hW : W = (List.range d).map fun a => List.ofFn (wt a)) {a : ℕ} (ha : a < d) :
    W.getD a [] = List.ofFn (wt a) := by
  subst hW
  simp [ha]

theorem pair_transfer
    (hnb : nbL = (List.range (W.length + R.length)).map fun v =>
      bitsOf (W.length + R.length) (adjP R W v))
    (hchk : ∀ i < R.length,
      (pairGraph W.length nbL wR wW).bnb order 200
        (rootMask W.length (W.length + R.length) nbL i) budget = true)
    (hR : ∀ γ : Fin n → ℤ, Pos γ ↔ List.ofFn γ ∈ R)
    (hW : W = (List.range d).map fun a => List.ofFn (wt a))
    (X : Finset (Fin n → ℤ)) (Y : Finset (Fin d)) (hX : X.Nonempty) (hXP : ∀ γ ∈ X, Pos γ)
    (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ Pos (γ + δ))
    (hXY : ∀ γ ∈ X, ∀ a ∈ Y, ¬ (wt a ⬝ᵥ γ = -1)) :
    wR * X.card + wW * Y.card ≤ wR + budget := by
  classical
  have hWlen : W.length = d := by subst hW; simp
  let idx : (Fin n → ℤ) → ℕ := fun γ => R.idxOf (List.ofFn γ)
  have hidxlt : ∀ γ ∈ X, idx γ < R.length := fun γ hγ =>
    List.idxOf_lt_length_iff.2 ((hR γ).1 (hXP γ hγ))
  have hget : ∀ γ ∈ X, R.getD (idx γ) [] = List.ofFn γ := fun γ hγ =>
    getD_idxOf R ((hR γ).1 (hXP γ hγ))
  have hinj : Set.InjOn idx X := by
    intro γ hγ δ hδ h
    have := (List.idxOf_inj ((hR γ).1 (hXP γ hγ))).1 h
    exact List.ofFn_injective this
  have hXc : (X.image idx).card = X.card := Finset.card_image_of_injOn hinj
  have hYc : (Y.image (fun a : Fin d => (a : ℕ))).card = Y.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have key := pair_bound R W nbL order wR wW budget hnb hchk (X.image idx)
    (Y.image fun a : Fin d => (a : ℕ)) (hX.image idx) ?_ ?_ ?_ ?_
  · rw [hXc, hYc] at key; exact key
  · intro i hi
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hi
    exact hidxlt γ hγ
  · intro a ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 ha
    rw [hWlen]; exact b.2
  · intro i hi j hj hij
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hj
    have h1 := hidxlt γ hγ
    have h2 := hidxlt δ hδ
    simp only [adjP, Nat.not_lt.2 (Nat.le_add_right _ _), ite_false, Nat.add_sub_cancel_left,
      decide_eq_true h1, decide_eq_true h2, Bool.true_and, decide_eq_false_iff_not]
    rw [hget γ hγ, hget δ hδ, zipWith_add_ofFn, ← hR]
    exact hXX γ hγ δ hδ
  · intro i hi a ha
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    have h1 := hidxlt γ hγ
    have hbW : (b : ℕ) < W.length := by rw [hWlen]; exact b.2
    have hnot : ¬ dotL (W.getD b []) (R.getD (idx γ) []) = -1 := by
      rw [getD_W W wt hW b.2, hget γ hγ, dotL_ofFn]
      exact hXY γ hγ b hb
    constructor
    · simp only [adjP, Nat.not_lt.2 (Nat.le_add_right _ _), ite_false, hbW, ite_true,
        Nat.add_sub_cancel_left, decide_eq_true h1, Bool.true_and, decide_eq_false_iff_not]
      exact hnot
    · simp only [adjP, hbW, ite_true, Nat.not_lt.2 (Nat.le_add_right _ _), ite_false,
        Nat.add_sub_cancel_left, decide_eq_true h1, Bool.true_and, decide_eq_false_iff_not]
      exact hnot

theorem abelian_transfer
    (hnb : nbL = (List.range R.length).map fun v => bitsOf R.length (adjP R [] v))
    (hchk : (pairGraph 0 nbL 1 1).bnb order 200 (bitsOf R.length fun _ => true) budget = true)
    (hR : ∀ γ : Fin n → ℤ, Pos γ ↔ List.ofFn γ ∈ R)
    (X : Finset (Fin n → ℤ)) (hXP : ∀ γ ∈ X, Pos γ) (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ Pos (γ + δ)) :
    X.card ≤ budget := by
  classical
  let idx : (Fin n → ℤ) → ℕ := fun γ => R.idxOf (List.ofFn γ)
  have hidxlt : ∀ γ ∈ X, idx γ < R.length := fun γ hγ =>
    List.idxOf_lt_length_iff.2 ((hR γ).1 (hXP γ hγ))
  have hget : ∀ γ ∈ X, R.getD (idx γ) [] = List.ofFn γ := fun γ hγ =>
    getD_idxOf R ((hR γ).1 (hXP γ hγ))
  have hinj : Set.InjOn idx X := by
    intro γ hγ δ hδ h
    have := (List.idxOf_inj ((hR γ).1 (hXP γ hγ))).1 h
    exact List.ofFn_injective this
  have key := abelian_bound R nbL order budget hnb hchk (X.image idx) ?_ ?_
  · rwa [Finset.card_image_of_injOn hinj] at key
  · intro i hi
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hi
    exact hidxlt γ hγ
  · intro i hi j hj hij
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hj
    have h1 := hidxlt γ hγ
    have h2 := hidxlt δ hδ
    simp only [adjP, List.length_nil, Nat.not_lt_zero, ite_false, Nat.sub_zero,
      decide_eq_true h1, decide_eq_true h2, Bool.true_and, decide_eq_false_iff_not]
    rw [hget γ hγ, hget δ hδ, zipWith_add_ofFn, ← hR]
    exact hXX γ hγ δ hδ

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
