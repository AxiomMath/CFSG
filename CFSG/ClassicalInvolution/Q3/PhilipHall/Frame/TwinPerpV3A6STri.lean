module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SF

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

@[expose] def ae6MLetters : Finset (Fin 8) := {0, 2, 3, 4, 6}

@[expose] def ae6EdgeK : Fin 3 → Fin 3 := ![0, 0, 1]

@[expose] def ae6EdgeL : Fin 3 → Fin 3 := ![1, 2, 2]

@[expose] def ae6Delta : Fin 3 → Fin 8 → List (Fin 8) :=
  ![![[0], [], [4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [4, 2, 0, 2, 3, 4, 6, 2, 0, 2, 6],
      [2, 0, 4, 6, 2, 0, 4, 6, 2, 0, 4, 6, 2, 6], [0, 2, 0, 4, 2, 5, 6, 2, 0, 2, 4, 6, 2],
      [2, 0, 4, 6, 2, 0, 4, 6, 2, 0, 4, 6, 2, 4], [0, 2, 0, 6, 2, 4, 2, 0, 2, 4, 7, 6, 2]],
    ![[2, 6, 4, 0, 2, 6, 4, 0, 2, 6, 4, 0, 2, 4], [6, 2, 6, 0, 2, 4, 2, 6, 2, 4, 1, 0, 2],
      [4, 2, 6, 2, 0, 2, 4, 2, 6, 2, 0], [4, 2, 6, 2, 3, 4, 0, 2, 6, 2, 0],
      [2, 6, 4, 0, 2, 6, 4, 0, 2, 6, 4, 0, 2, 0], [6, 2, 6, 4, 2, 5, 0, 2, 6, 2, 4, 0, 2], [6], []],
    ![[2, 4, 0, 6, 2, 4, 0, 6, 2, 4, 0, 6, 2, 6], [4, 2, 4, 0, 2, 1, 6, 2, 4, 2, 0, 6, 2],
      [0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6], [0, 2, 4, 2, 3, 0, 6, 2, 4, 2, 6], [4], [],
      [2, 4, 0, 6, 2, 4, 0, 6, 2, 4, 0, 6, 2, 0], [4, 2, 4, 6, 2, 0, 2, 4, 2, 0, 7, 6, 2]]]

@[expose] def ae6DeltaW (k : Fin 3) (w : List (Fin 8)) : List (Fin 8) := w.flatMap (ae6Delta k)

@[expose] def ae6TriMemC : Fin 3 → List (Fin 8) :=
  ![[], [2, 6, 2, 4, 2, 0, 2, 4, 2, 6, 2, 4], [2, 6, 2, 0, 2, 6, 2, 4, 2, 0, 2]]

@[expose] def ae6TriQWords : Fin 4 → List (List (Fin 8)) :=
  ![[[6], [0], [2, 6, 2], [2, 0, 2], [4, 2, 6, 2, 4], [4, 2, 0, 2, 4]],
    [[0], [4], [2, 4, 2], [2, 0, 2], [6, 2, 0, 2, 6], [6, 2, 4, 2, 6]],
    [[6], [4], [2, 4, 2], [2, 6, 2], [0, 2, 6, 2, 0], [0, 2, 4, 2, 0]],
    [[0, 6], [4, 6], [2, 4, 6, 2], [2, 0, 6, 2], [0, 2, 0, 6, 2, 4], [0, 2, 0, 4, 2, 6]]]

@[expose] noncomputable def ae6TriQ (x : Fin 4) : Subgroup AE6Om :=
  Subgroup.closure {g | ∃ w ∈ ae6TriQWords x, ae6Word w = g}

@[expose] def ae6DeltaQ : Fin 3 → Fin 4 → Fin 4 := ![![0, 1, 3, 2], ![0, 3, 2, 1], ![3, 1, 2, 0]]

@[expose] def ae6EdgeMap : Fin 3 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 2, 3, 6, 7, 0, 1], ![4, 5, 2, 3, 0, 1, 6, 7]]

@[expose] def ae6TriGen₀ : Fin 6 → List (Fin 8) :=
  ![[2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6],
    [0, 2, 6, 2, 4, 2, 0, 2, 6, 2, 4, 2], [0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2],
    [0, 2, 0, 3, 4, 2, 0, 6, 2, 0, 4, 2, 6], [0, 6, 2, 0, 6, 2, 4, 2, 0, 2, 5, 6, 2, 4]]

@[expose] def ae6TriGen (e : Fin 3) (i : Fin 6) : List (Fin 8) := (ae6TriGen₀ i).map (ae6EdgeMap e)

@[expose] def ae6TriProf : List (List (Fin 6)) :=
  [[0], [1], [2], [3], [4], [5], [0, 1], [0, 2], [0, 3], [0, 4], [1, 5], [4, 5], [0, 2, 4], [0, 2, 3], [0, 3, 4]]

@[expose] def ae6EdgeQuat (k l : Fin 3) : Set AE6Om :=
  {x | ∃ J ∈ ae6ConjIn (ae6ModelE k l) ae6ModelK, x ∈ J ∧ orderOf x = 4}

@[expose] def ae6TriRep (e : Fin 3) : Fin 6 → List (Fin 8) → List (Fin 8) :=
  ![id, ae6DeltaW (ae6EdgeK e), ae6DeltaW (ae6EdgeL e), ae6DeltaW (ae6EdgeL e) ∘ ae6DeltaW (ae6EdgeK e),
    ae6DeltaW (ae6EdgeK e) ∘ ae6DeltaW (ae6EdgeL e),
    ae6DeltaW (ae6EdgeK e) ∘ ae6DeltaW (ae6EdgeL e) ∘ ae6DeltaW (ae6EdgeK e)]

@[expose] def AE6TriFin : Prop :=
  ae6ModelM = ae6LetterSub ↑ae6MLetters ∧
    (∀ k l : Fin 3, k ≠ l → ae6ModelE k l = ae6LetterSub ↑(ae6EdgeLetters k l)) ∧
    (∀ m ∈ ae6ModelM, (∀ i ∈ ae6MLetters, m * A6.curtisGen i = A6.curtisGen i * m) → m = 1) ∧
    (∀ k : Fin 3, Nat.card (ae6ModelV k) = 1290240 ∧
      Nat.card (Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) =>
        (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta k i)))) = 1290240 ∧
      Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) => ae6Word (ae6Delta k i)) = ae6ModelV k ∧
      (∀ i ∈ ae6VertexLetters k, ∀ j ∈ ae6Delta k i, j ∈ ae6VertexLetters k ∧ (i ∈ ae6MLetters → j ∈ ae6MLetters) ∧
        ∀ l : Fin 3, l ≠ k → i ∈ ae6EdgeLetters k l → j ∈ ae6EdgeLetters k l) ∧
      ∀ s : Fin 3, ae6Word (ae6DeltaW k (ae6KWord s)) ∈ conjSub (ae6Word (ae6TriMemC k)) ae6ModelK) ∧
    (∀ x : Fin 4, ∀ w ∈ ae6TriQWords x, (∀ i ∈ w, i ∈ ae6MLetters) ∧
      ∀ i ∈ ae6MLetters, A6.curtisGen i * ae6Word w * A6.curtisGen i ∈ ae6TriQ x) ∧
    (∀ x y : Fin 4, x ≠ y → ae6TriQ x ≠ ae6TriQ y) ∧
    (∀ (k : Fin 3) (x : Fin 4), ∀ w ∈ ae6TriQWords x, ae6Word (ae6DeltaW k w) ∈ ae6TriQ (ae6DeltaQ k x)) ∧
    ∀ e : Fin 3,
      Subgroup.closure (Set.range fun i => ae6Word (ae6TriGen e i)) = ae6ModelE (ae6EdgeK e) (ae6EdgeL e) ∧
      (∀ i, ae6Word (ae6TriGen e i) ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) ∧
      ∀ y : Fin 6 → AE6Om, (∀ i, y i ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) →
        (∀ u ∈ ae6TriProf,
          orderOf (u.map y).prod = orderOf (u.map fun i => ae6Word (ae6TriGen e i)).prod ∧
          ((u.map y).prod ∈ ae6ModelM ↔ (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6ModelM) ∧
          ((u.map y).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e) ↔
            (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e))) →
        ∃ m ∈ ae6ModelM, ∃ j : Fin 6, ∀ i, y i = m * ae6Word (ae6TriRep e j (ae6TriGen e i)) * m⁻¹

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
