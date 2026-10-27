module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame
public import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.RankTwoSporadic.Endgame

@[expose] def fix1782 (σ : Equiv.Perm (Fin 1782)) : ℕ :=
  (Finset.univ.filter fun x : Fin 1782 => σ x = x).card

@[expose] noncomputable def suzEndE (i : ℕ) : Equiv.Perm (Fin 1782) := permOfArr 1782 suzE0[i]!

@[expose] def suzInMA (a : Array ℕ) : Prop := isInvA 1782 a (invCand 1782 a) = true ∧ suzInM a = true

structure SuzEndFactsK : Prop where
  e_mem : ∀ i < 2, suzInMA suzE0[i]!
  e_sq : ∀ i < 2, suzEndE i * suzEndE i = 1
  e_comm : suzEndE 0 * suzEndE 1 = suzEndE 1 * suzEndE 0
  e_fix : fix1782 (suzEndE 0) = 42 ∧ fix1782 (suzEndE 1) = 42 ∧
    fix1782 (suzEndE 0 * suzEndE 1) = 42
  conj : ∃ b : Array ℕ, ∃ x : Fin 8 → Array ℕ, suzInMA b ∧ (∀ i, suzInMA (x i)) ∧
    (∀ i < 2, ∀ j < 2, suzEndE i * ((permOfArr 1782 b)⁻¹ * suzEndE j * permOfArr 1782 b) =
      (permOfArr 1782 b)⁻¹ * suzEndE j * permOfArr 1782 b * suzEndE i) ∧
    (permOfArr 1782 b)⁻¹ * suzEndE 0 * permOfArr 1782 b ∉
      ({1, suzEndE 0, suzEndE 1, suzEndE 0 * suzEndE 1} : Set (Equiv.Perm (Fin 1782))) ∧
    (∀ i, ∀ j < 2, permOfArr 1782 (x i) * suzEndE j = suzEndE j * permOfArr 1782 (x i)) ∧
    tree3 (fun i => permOfArr 1782 (x i)) =
      suzEndE 0 * ((permOfArr 1782 b)⁻¹ * suzEndE 0 * permOfArr 1782 b)
  lgrp : ∃ l : Array (Array ℕ), (∀ k < l.size, suzInMA l[k]! ∧
      ∀ j < 2, permOfArr 1782 l[k]! * suzEndE j = suzEndE j * permOfArr 1782 l[k]!) ∧
    Nat.card (closure (permsA 1782 l)) = 20160 ∧
    ∃ s : Array (Array ℕ), (∀ k < s.size, permOfArr 1782 s[k]! ∈ closure (permsA 1782 l)) ∧
      Nat.card (closure (permsA 1782 s)) = 64 ∧
      ∀ z ∈ closure (permsA 1782 s), z ^ 2 = 1 → z ≠ 1 → fix1782 z ≠ 42
  sigma : ∃ σ : Array ℕ, suzInMA σ ∧ permOfArr 1782 σ * suzEndE 0 = suzEndE 0 * permOfArr 1782 σ ∧
    permOfArr 1782 σ * suzEndE 1 ≠ suzEndE 1 * permOfArr 1782 σ
  c0 : ∃ c : Array ℕ, suzInMA c ∧
    permOfArr 1782 c * suzEndE 0 * (permOfArr 1782 c)⁻¹ = permOfArr 1782 (tArr 0)

end CFSG.ComponentClassification.RankTwoSporadic.Suz

end
