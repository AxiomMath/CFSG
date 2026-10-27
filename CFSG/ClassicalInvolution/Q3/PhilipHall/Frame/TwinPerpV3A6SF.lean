module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SEdge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

@[expose] def ae6CLetter : Fin 7 → Fin 8 := ![0, 1, 2, 4, 5, 6, 7]

@[expose] def ae6ZWord : List (Fin 8) := [0, 4, 2, 4, 0, 6, 2, 6, 4, 0, 2, 0, 4, 6, 2, 6]

@[expose] def ae6KWord : Fin 3 → List (Fin 8) :=
  ![[2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6],
    [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6, 0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]]

@[expose] def ae6WWords : List (List (Fin 8)) :=
  [[4, 2, 4, 2, 6, 2, 4, 2, 0], [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2],
    [0, 2, 0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 0, 6], [0, 4, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2, 4]]

@[expose] def ae6TwinWord : Fin 4 → List (Fin 8) := ![[], [0], [4], [6]]

@[expose] noncomputable def ae6Twin (i : Fin 4) : Subgroup AE6Om := conjSub (ae6Word (ae6TwinWord i)) ae6ModelK

@[expose] def ae6Blk (n : Fin 12) : Fin 4 := ⟨n / 3, by omega⟩

@[expose] def ae6CycWord (n : Fin 12) : List (Fin 8) :=
  ae6TwinWord (ae6Blk n) ++ ae6KWord ⟨n % 3, by omega⟩ ++ (ae6TwinWord (ae6Blk n)).reverse

@[expose] noncomputable def ae6Cyc (n : Fin 12) : AE6Om := ae6Word (ae6CycWord n)

@[expose] def ae6LetterHat : Fin 7 → Fin 12 → Fin 12 :=
  ![![3, 4, 5, 0, 1, 2, 9, 11, 10, 6, 8, 7], ![4, 5, 3, 2, 0, 1, 11, 10, 9, 8, 7, 6],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], ![6, 7, 8, 9, 11, 10, 0, 1, 2, 3, 5, 4],
    ![8, 6, 7, 10, 9, 11, 1, 2, 0, 4, 3, 5], ![9, 10, 11, 6, 8, 7, 3, 5, 4, 0, 1, 2],
    ![11, 9, 10, 7, 6, 8, 4, 3, 5, 1, 2, 0]]

@[expose] def ae6Diag : Fin 2 → Fin 8 → Fin 8 := ![![4, 5, 2, 3, 0, 1, 6, 7], ![6, 7, 2, 3, 4, 5, 0, 1]]

@[expose] def ae6GammaHat : Fin 2 → Fin 12 → Fin 12 :=
  ![![9, 11, 10, 3, 4, 5, 6, 7, 8, 0, 2, 1], ![6, 8, 7, 3, 4, 5, 0, 2, 1, 9, 10, 11]]

theorem ae6LetterHat_involutive (x : Fin 7) : Function.Involutive (ae6LetterHat x) := by
  have h : ∀ x : Fin 7, ∀ n : Fin 12, ae6LetterHat x (ae6LetterHat x n) = n := by decide
  exact h x

theorem ae6GammaHat_involutive (c : Fin 2) : Function.Involutive (ae6GammaHat c) := by
  have h : ∀ c : Fin 2, ∀ n : Fin 12, ae6GammaHat c (ae6GammaHat c n) = n := by decide
  exact h c

@[expose] def ae6LetterHatPerm (x : Fin 7) : Equiv.Perm (Fin 12) :=
  Function.Involutive.toPerm _ (ae6LetterHat_involutive x)

@[expose] def ae6GammaHatPerm (c : Fin 2) : Equiv.Perm (Fin 12) :=
  Function.Involutive.toPerm _ (ae6GammaHat_involutive c)

@[expose] def AE6FFin : Prop :=
  Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) = ae6LetterSub (Set.range ae6CLetter) ∧
    (∀ y ∈ ae6ModelK, y = 1 ∨ y = ae6ModelZ ∨
      ∃ s : Fin 3, y = ae6Word (ae6KWord s) ∨ y = (ae6Word (ae6KWord s))⁻¹) ∧
    (∀ s : Fin 3, ae6Word (ae6KWord s) ^ 2 = ae6ModelZ) ∧ ae6ModelZ ≠ 1 ∧ ae6ModelZ * ae6ModelZ = 1 ∧
    (∀ i : Fin 8, A6.curtisGen i * A6.curtisGen i = 1) ∧
    (∀ (x : Fin 7) (i : Fin 4), ∃ j : Fin 4, conjSub (A6.curtisGen (ae6CLetter x)) (ae6Twin i) = ae6Twin j) ∧
    (∀ m n : Fin 12, m ≠ n → ae6Cyc m ≠ ae6Cyc n ∧ ae6Cyc m ≠ (ae6Cyc n)⁻¹) ∧
    (∀ m n : Fin 12, ae6Blk m ≠ ae6Blk n → ae6Cyc m * ae6Cyc n = ae6Cyc n * ae6Cyc m) ∧
    (∀ m n : Fin 12, ae6Blk m = ae6Blk n → m ≠ n → ae6Cyc m * ae6Cyc n * (ae6Cyc m)⁻¹ = (ae6Cyc n)⁻¹) ∧
    (∀ (x : Fin 7) (n : Fin 12),
      A6.curtisGen (ae6CLetter x) * ae6Cyc n * A6.curtisGen (ae6CLetter x) = ae6Cyc (ae6LetterHat x n) ∨
        A6.curtisGen (ae6CLetter x) * ae6Cyc n * A6.curtisGen (ae6CLetter x) = (ae6Cyc (ae6LetterHat x n))⁻¹) ∧
    (∀ c : Fin 2,
      (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) r = 1) ∧
        ae6Word (ae6ZWord.map (ae6Diag c)) = ae6ModelZ ∧
        (∀ n : Fin 12, ae6Word ((ae6CycWord n).map (ae6Diag c)) = ae6Cyc (ae6GammaHat c n) ∨
          ae6Word ((ae6CycWord n).map (ae6Diag c)) = (ae6Cyc (ae6GammaHat c n))⁻¹) ∧
        ∀ w ∈ ae6WWords, ae6Word (w.map (ae6Diag c)) ∈ ae6ModelW) ∧
    ∀ σ : Equiv.Perm (Fin 12), (∀ m n : Fin 12, ae6Blk m = ae6Blk n ↔ ae6Blk (σ m) = ae6Blk (σ n)) →
      σ ∉ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm) →
      ∃ τ ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)), orderOf τ = 3 ∧
        (∀ n, ae6Blk (τ n) = ae6Blk n) ∧ (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
