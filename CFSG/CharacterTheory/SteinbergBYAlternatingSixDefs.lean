module

public import CFSG.CharacterTheory.SteinbergBYNortonCriterion
public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.CharacterTheory.SteinbergBY.AlternatingSix

open Matrix Equiv FieldFour
open scoped Kronecker

@[expose] def invImages (v : Vector (Fin 6) 6) : Vector (Fin 6) 6 :=
  Vector.ofFn fun y => ((List.finRange 6).find? fun x => v[x] = y).getD 0

@[expose] def permOfImages (v : Vector (Fin 6) 6) : Perm (Fin 6) :=
  if h : (∀ x : Fin 6, (invImages v)[v[x]] = x) ∧ ∀ y : Fin 6, v[(invImages v)[y]] = y then
    ⟨fun x => v[x], fun y => (invImages v)[y], h.1, h.2⟩
  else 1

@[expose] def a6OfImages (v : Vector (Fin 6) 6) : alternatingGroup (Fin 6) :=
  if h : Perm.sign (permOfImages v) = 1 then ⟨permOfImages v, Perm.mem_alternatingGroup.mpr h⟩
  else 1

@[expose] def heartCoordTable : Vector (Vector (ZMod 2) 6) 4 :=
  #v[#v[1, 0, 0, 0, 0, 1], #v[1, 1, 0, 0, 0, 0], #v[1, 1, 1, 0, 0, 1], #v[1, 1, 1, 1, 0, 0]]

@[expose] def heartCoord : Matrix (Fin 4) (Fin 6) (ZMod 2) := untab heartCoordTable

@[expose] def heartBasis : Matrix (Fin 6) (Fin 4) (ZMod 2) :=
  Matrix.of fun l j =>
    (Pi.single j.castSucc.castSucc 1 + Pi.single j.succ.castSucc 1 : Fin 6 → ZMod 2) l

@[expose] def permMat (σ : Perm (Fin 6)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => if σ j = i then 1 else 0

@[expose] def heartMatrixOf (σ : Fin 6 → Fin 6) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => heartCoord i (σ j.castSucc.castSucc) + heartCoord i (σ j.succ.castSucc)

@[expose] def totalsTable : Vector (Vector (Vector (Fin 6) 6) 5) 6 :=
  #v[
    #v[#v[1, 0, 3, 2, 5, 4], #v[2, 4, 0, 5, 1, 3], #v[3, 5, 4, 0, 2, 1], #v[4, 3, 5, 1, 0, 2],
      #v[5, 2, 1, 4, 3, 0]],
    #v[#v[1, 0, 3, 2, 5, 4], #v[2, 5, 0, 4, 3, 1], #v[3, 4, 5, 0, 1, 2], #v[4, 2, 1, 5, 0, 3],
      #v[5, 3, 4, 1, 2, 0]],
    #v[#v[1, 0, 4, 5, 2, 3], #v[2, 3, 0, 1, 5, 4], #v[3, 4, 5, 0, 1, 2], #v[4, 5, 3, 2, 0, 1],
      #v[5, 2, 1, 4, 3, 0]],
    #v[#v[1, 0, 4, 5, 2, 3], #v[2, 5, 0, 4, 3, 1], #v[3, 2, 1, 0, 5, 4], #v[4, 3, 5, 1, 0, 2],
      #v[5, 4, 3, 2, 1, 0]],
    #v[#v[1, 0, 5, 4, 3, 2], #v[2, 3, 0, 1, 5, 4], #v[3, 5, 4, 0, 2, 1], #v[4, 2, 1, 5, 0, 3],
      #v[5, 4, 3, 2, 1, 0]],
    #v[#v[1, 0, 5, 4, 3, 2], #v[2, 4, 0, 5, 1, 3], #v[3, 2, 1, 0, 5, 4], #v[4, 5, 3, 2, 0, 1],
      #v[5, 3, 4, 1, 2, 0]]]

@[expose] def partner (j : Fin 6) (a : Fin 5) (x : Fin 6) : Fin 6 := totalsTable[j][a][x]

@[expose] def MapsTotal (σ : Fin 6 → Fin 6) (j i : Fin 6) : Prop :=
  ∀ a : Fin 5, ∃ b : Fin 5, ∀ x, σ (partner j a x) = partner i b (σ x)

instance (σ : Fin 6 → Fin 6) (j i : Fin 6) : Decidable (MapsTotal σ j i) :=
  inferInstanceAs (Decidable (∀ a : Fin 5, ∃ b : Fin 5, ∀ x, σ (partner j a x) = partner i b (σ x)))

@[expose] def totalIdx (σ : Fin 6 → Fin 6) (j : Fin 6) : Fin 6 :=
  ((List.finRange 6).find? fun i => decide (MapsTotal σ j i)).getD 0

@[expose] def totalCheckVec (v : Vector (Fin 6) 6) : Bool :=
  decide (∀ j : Fin 6, ∃ i : Fin 6, MapsTotal (fun x => v[x]) j i)

@[expose] def totalCheck (σ : Perm (Fin 6)) : Bool := totalCheckVec (Vector.ofFn σ)

@[expose] def totalCheckIfSwap (σ : Perm (Fin 6)) : Bool :=
  if σ.support.card = 2 then totalCheck σ else true

@[expose] def heartTab (v : Vector (Fin 6) 6) : Vector (Vector (ZMod 2) 4) 4 :=
  tab (heartMatrixOf fun x => v[x])

@[expose] def totalVec (v : Vector (Fin 6) 6) : Vector (Fin 6) 6 :=
  Vector.ofFn (totalIdx fun x => v[x])

@[expose] def rep4aTab (σ : alternatingGroup (Fin 6)) : Vector (Vector (ZMod 2) 4) 4 :=
  heartTab (Vector.ofFn (σ : Perm (Fin 6)))

@[expose] def rep4bTab (σ : alternatingGroup (Fin 6)) : Vector (Vector (ZMod 2) 4) 4 :=
  heartTab (totalVec (Vector.ofFn (σ : Perm (Fin 6))))

@[expose] def kron16 (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)

@[expose] def basis8Table : Vector (Vector FieldFour 8) 16 :=
  #v[#v[ω₂, ω₂, 1, ω₂, ω₂, ω₂, ω₂, ω],
    #v[ω₂, 1, ω, 0, ω, 0, ω₂, ω₂],
    #v[0, ω₂, 1, 1, 0, 0, ω₂, 0],
    #v[ω, ω₂, 1, 0, 0, 0, 1, ω],
    #v[1, ω, ω₂, 1, ω₂, 0, ω₂, ω₂],
    #v[ω, 0, 1, 0, 1, ω, 1, 1],
    #v[1, 0, 0, 0, 0, 0, 0, 0],
    #v[0, 1, 0, 0, 0, 0, 0, 0],
    #v[0, 0, ω, ω₂, ω, ω, ω₂, 0],
    #v[0, 0, ω₂, 0, ω₂, 0, ω₂, ω],
    #v[0, 0, 1, 0, 0, 0, 0, 0],
    #v[0, 0, 0, 1, 0, 0, 0, 0],
    #v[0, 0, 0, 0, 1, 0, 0, 0],
    #v[0, 0, 0, 0, 0, 1, 0, 0],
    #v[0, 0, 0, 0, 0, 0, 1, 0],
    #v[0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def basis8 : Matrix (Fin 16) (Fin 8) FieldFour := untab basis8Table

@[expose] def proj8Table : Vector (Vector FieldFour 16) 8 :=
  #v[#v[0, 1, 0, 0, 0, 0, ω, 1, 0, 1, 1, 0, 1, 0, 0, 1],
    #v[0, 0, 0, 0, 1, 0, 1, ω₂, 0, 1, 0, 1, 0, 0, 0, 1],
    #v[1, 0, 0, 1, 0, 0, 1, 0, 1, 0, ω₂, 0, 1, 1, 1, 0],
    #v[0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, ω₂, 0, 0, 0, 0],
    #v[1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, ω, 1, 0, 1],
    #v[0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, ω₂, 1, 0],
    #v[0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, ω, 1],
    #v[0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, ω₂]]

@[expose] def proj8 : Matrix (Fin 8) (Fin 16) FieldFour := untab proj8Table

@[expose] def kronOfTabs (a b : Vector (Vector (ZMod 2) 4) 4) : Vector (Vector FieldFour 16) 16 :=
  tab ((kron16 (untab a) (untab b)).map ofPrime)

@[expose] def kronTab (σ : alternatingGroup (Fin 6)) : Vector (Vector FieldFour 16) 16 :=
  kronOfTabs (rep4aTab σ) (rep4bTab σ)

@[expose] def mulBasis8 (PK : Vector (Vector FieldFour 16) 8) : Vector (Vector FieldFour 8) 8 :=
  tab (untab PK * basis8)

@[expose] def rep8aOfKron (K : Vector (Vector FieldFour 16) 16) : Vector (Vector FieldFour 8) 8 :=
  mulBasis8 (tab (proj8 * untab K))

@[expose] def rep8aTab (σ : alternatingGroup (Fin 6)) : Vector (Vector FieldFour 8) 8 :=
  rep8aOfKron (kronTab σ)

@[expose] def invCheckOfKron (K : Vector (Vector FieldFour 16) 16) : Bool :=
  decide (untab K * basis8 = basis8 * untab (rep8aOfKron K))

@[expose] def invCheckPerm (σ : Perm (Fin 6)) : Bool :=
  invCheckOfKron (kronOfTabs (heartTab (Vector.ofFn σ)) (heartTab (totalVec (Vector.ofFn σ))))

@[expose] def invCheckIfThreeCycle (σ : Perm (Fin 6)) : Bool :=
  if σ.support.card = 3 then invCheckPerm σ else true

@[expose] def cert1 : NortonData (alternatingGroup (Fin 6)) (ZMod 2) 1 where
  terms := []
  Q := #v[#v[1]]
  Qi := #v[#v[1]]
  R := #v[#v[1]]
  S := #v[#v[1]]
  Si := #v[#v[1]]
  spin := #v[1]
  w := #v[1]
  T := #v[#v[1]]
  Ti := #v[#v[1]]
  dual := #v[1]

@[expose] def cert4a : NortonData (alternatingGroup (Fin 6)) (ZMod 2) 4 where
  terms := [(a6OfImages #v[3, 5, 4, 0, 1, 2], 1), (a6OfImages #v[2, 4, 5, 3, 0, 1], 1)]
  Q := #v[#v[0, 1, 0, 0],
      #v[1, 0, 0, 0],
      #v[0, 0, 1, 0],
      #v[0, 0, 0, 1]]
  Qi := #v[#v[0, 1, 0, 0],
      #v[1, 0, 0, 0],
      #v[0, 0, 1, 0],
      #v[0, 0, 0, 1]]
  R := #v[#v[0, 0, 0, 1],
      #v[1, 0, 0, 0],
      #v[0, 1, 1, 0],
      #v[0, 0, 1, 0]]
  S := #v[#v[0, 0, 0, 1],
      #v[1, 1, 1, 1],
      #v[0, 1, 1, 0],
      #v[0, 0, 1, 1]]
  Si := #v[#v[1, 1, 1, 0],
      #v[1, 0, 1, 1],
      #v[1, 0, 0, 1],
      #v[1, 0, 0, 0]]
  spin := #v[a6OfImages #v[0, 1, 2, 3, 4, 5], a6OfImages #v[0, 1, 3, 2, 5, 4],
      a6OfImages #v[0, 1, 4, 2, 3, 5], a6OfImages #v[0, 1, 5, 2, 4, 3]]
  w := #v[0, 0, 0, 1]
  T := #v[#v[0, 0, 0, 1],
      #v[0, 0, 1, 0],
      #v[0, 1, 1, 0],
      #v[1, 1, 0, 1]]
  Ti := #v[#v[1, 1, 1, 1],
      #v[0, 1, 1, 0],
      #v[0, 1, 0, 0],
      #v[1, 0, 0, 0]]
  dual := #v[a6OfImages #v[0, 1, 2, 3, 4, 5], a6OfImages #v[0, 1, 2, 4, 5, 3],
      a6OfImages #v[0, 1, 4, 2, 3, 5], a6OfImages #v[0, 4, 1, 2, 5, 3]]

@[expose] def cert4b : NortonData (alternatingGroup (Fin 6)) (ZMod 2) 4 where
  terms := [(a6OfImages #v[3, 5, 4, 0, 1, 2], 1), (a6OfImages #v[2, 4, 5, 3, 0, 1], 1)]
  Q := #v[#v[0, 1, 0, 0],
      #v[1, 0, 1, 0],
      #v[1, 0, 0, 1],
      #v[1, 0, 0, 0]]
  Qi := #v[#v[0, 0, 0, 1],
      #v[1, 0, 0, 0],
      #v[0, 1, 0, 1],
      #v[0, 0, 1, 1]]
  R := #v[#v[0, 1, 1, 1],
      #v[0, 0, 0, 1],
      #v[0, 0, 1, 0],
      #v[1, 0, 0, 0]]
  S := #v[#v[0, 1, 1, 0],
      #v[1, 1, 1, 0],
      #v[1, 0, 0, 1],
      #v[1, 0, 1, 1]]
  Si := #v[#v[1, 1, 0, 0],
      #v[1, 0, 1, 1],
      #v[0, 0, 1, 1],
      #v[1, 1, 1, 0]]
  spin := #v[a6OfImages #v[0, 1, 2, 3, 4, 5], a6OfImages #v[0, 1, 2, 4, 5, 3],
      a6OfImages #v[0, 1, 3, 2, 5, 4], a6OfImages #v[0, 1, 3, 4, 2, 5]]
  w := #v[0, 1, 1, 1]
  T := #v[#v[0, 1, 1, 1],
      #v[1, 1, 1, 1],
      #v[0, 0, 1, 1],
      #v[1, 1, 0, 1]]
  Ti := #v[#v[1, 1, 0, 0],
      #v[1, 0, 1, 0],
      #v[0, 1, 0, 1],
      #v[0, 1, 1, 1]]
  dual := #v[a6OfImages #v[0, 1, 2, 3, 4, 5], a6OfImages #v[0, 1, 2, 4, 5, 3],
      a6OfImages #v[0, 1, 3, 2, 5, 4], a6OfImages #v[0, 1, 3, 4, 2, 5]]

@[expose] def cert8a : NortonData (alternatingGroup (Fin 6)) FieldFour 8 where
  terms := [(a6OfImages #v[5, 0, 4, 1, 2, 3], 1), (a6OfImages #v[5, 3, 0, 1, 2, 4], 1),
      (a6OfImages #v[1, 4, 3, 0, 2, 5], ω)]
  Q := #v[#v[ω₂, 1, 0, 0, 0, 0, 0, 0],
      #v[1, 0, 1, 0, 0, 0, 0, 0],
      #v[ω, 0, 0, 1, 0, 0, 0, 0],
      #v[0, 0, 0, 0, 1, 0, 0, 0],
      #v[ω, 0, 0, 0, 0, 1, 0, 0],
      #v[0, 0, 0, 0, 0, 0, 1, 0],
      #v[1, 0, 0, 0, 0, 0, 0, 1],
      #v[1, 0, 0, 0, 0, 0, 0, 0]]
  Qi := #v[#v[0, 0, 0, 0, 0, 0, 0, 1],
      #v[1, 0, 0, 0, 0, 0, 0, ω₂],
      #v[0, 1, 0, 0, 0, 0, 0, 1],
      #v[0, 0, 1, 0, 0, 0, 0, ω],
      #v[0, 0, 0, 1, 0, 0, 0, 0],
      #v[0, 0, 0, 0, 1, 0, 0, ω],
      #v[0, 0, 0, 0, 0, 1, 0, 0],
      #v[0, 0, 0, 0, 0, 0, 1, 1]]
  R := #v[#v[1, ω₂, 1, ω₂, ω, ω, ω, ω₂],
      #v[0, 1, 1, ω, 0, 1, ω₂, 1],
      #v[0, ω, 1, ω, 0, ω₂, 0, 0],
      #v[0, 0, ω, ω, 0, 0, ω, 1],
      #v[0, 0, 1, ω, ω₂, 1, 1, 0],
      #v[0, ω, ω, 0, 0, 0, 1, ω₂],
      #v[0, 1, 1, 0, 0, ω₂, 1, ω],
      #v[0, 1, ω, ω₂, ω₂, 1, 1, 1]]
  S := #v[#v[ω₂, ω₂, 0, ω, 0, ω, ω₂, ω],
      #v[1, 0, 1, 1, 1, 0, 0, 1],
      #v[ω, ω₂, ω₂, 1, ω, 0, 0, 0],
      #v[0, 0, 0, 1, 1, 0, 0, 1],
      #v[ω, ω₂, ω, ω₂, ω₂, ω, 0, ω],
      #v[0, 0, 0, 0, 0, 0, 1, 1],
      #v[1, 1, 0, 1, 0, 1, ω₂, ω],
      #v[1, 1, 1, 1, 1, 1, 1, 0]]
  Si := #v[#v[ω, 0, ω, 1, ω₂, 0, ω, 0],
      #v[ω, 0, 1, 1, 0, ω, 0, ω₂],
      #v[ω, 1, ω, 0, ω₂, 0, ω, 0],
      #v[0, 1, ω₂, 1, ω, ω, ω₂, 0],
      #v[ω, 1, ω, 0, ω₂, ω, ω₂, 1],
      #v[ω, 1, 1, 1, 0, ω₂, 0, ω],
      #v[ω, 0, 1, 0, 1, 1, 0, 1],
      #v[ω, 0, 1, 0, 1, 0, 0, 1]]
  spin := #v[a6OfImages #v[0, 1, 2, 3, 4, 5], a6OfImages #v[0, 1, 2, 4, 5, 3],
      a6OfImages #v[0, 1, 2, 5, 3, 4], a6OfImages #v[0, 1, 3, 2, 5, 4],
      a6OfImages #v[0, 1, 3, 4, 2, 5], a6OfImages #v[0, 1, 3, 5, 4, 2],
      a6OfImages #v[0, 1, 4, 2, 3, 5], a6OfImages #v[0, 1, 4, 5, 2, 3]]
  w := #v[ω, 1, ω, 1, ω₂, ω₂, ω₂, 1]
  T := #v[#v[ω, 1, ω, 1, ω₂, ω₂, ω₂, 1],
      #v[ω, 0, ω, 0, ω, 1, ω₂, ω],
      #v[0, 0, ω₂, 1, ω, 0, ω, 1],
      #v[0, 0, 0, 0, 1, ω, 0, ω],
      #v[0, 0, 0, 0, 0, ω₂, 1, 1],
      #v[0, 0, ω₂, 0, ω₂, ω, ω, ω₂],
      #v[0, 0, 0, 0, 1, ω, 0, ω₂],
      #v[0, 0, 0, 0, 1, 0, 1, ω₂]]
  Ti := #v[#v[0, ω₂, 0, ω, ω, ω, 1, ω₂],
      #v[1, 1, 1, 1, 0, 1, 1, 0],
      #v[0, 0, 0, ω, 0, ω, 0, ω₂],
      #v[0, 0, 1, 1, 0, 1, 0, 0],
      #v[0, 0, 0, 1, ω, 0, ω, ω],
      #v[0, 0, 0, 1, 1, 0, 0, 1],
      #v[0, 0, 0, ω, ω, 0, 1, ω₂],
      #v[0, 0, 0, 1, 0, 0, 1, 0]]
  dual := #v[a6OfImages #v[0, 1, 2, 3, 4, 5], a6OfImages #v[0, 1, 2, 4, 5, 3],
      a6OfImages #v[0, 1, 3, 2, 5, 4], a6OfImages #v[0, 1, 3, 4, 2, 5],
      a6OfImages #v[0, 1, 3, 5, 4, 2], a6OfImages #v[0, 1, 4, 2, 3, 5],
      a6OfImages #v[0, 1, 4, 3, 5, 2], a6OfImages #v[0, 1, 4, 5, 2, 3]]

@[expose] def classReps : Vector (Vector (Fin 6) 6) 5 :=
  #v[#v[0, 1, 2, 3, 4, 5], #v[1, 2, 0, 3, 4, 5], #v[1, 2, 0, 4, 5, 3], #v[1, 2, 3, 4, 0, 5],
    #v[2, 3, 4, 0, 1, 5]]

@[expose] def composeImages (v w : Vector (Fin 6) 6) : Vector (Fin 6) 6 :=
  Vector.ofFn fun x => v[w[x]]

@[expose] def powImages (v : Vector (Fin 6) 6) : ℕ → Vector (Fin 6) 6
  | 0 => Vector.ofFn id
  | n + 1 => composeImages v (powImages v n)

@[expose] def isIdVec (v : Vector (Fin 6) 6) : Bool := decide (∀ x : Fin 6, v[x] = x)

@[expose] def conjCandidates (v : Vector (Fin 6) 6) : List (Fin 5 × Vector (Fin 6) 6) :=
  let moved := (List.finRange 6).filter fun x => v[x] ≠ x
  let fixed := (List.finRange 6).filter fun x => v[x] = x
  let a := moved.getD 0 0
  match moved.length with
  | 0 => [(0, #v[0, 1, 2, 3, 4, 5])]
  | 3 =>
    let f₀ := fixed.getD 0 0
    let f₁ := fixed.getD 1 0
    let f₂ := fixed.getD 2 0
    [(1, #v[a, v[a], v[v[a]], f₀, f₁, f₂]), (1, #v[a, v[a], v[v[a]], f₁, f₀, f₂])]
  | 5 =>
    let f := fixed.getD 0 0
    let c := #v[a, v[a], v[v[a]], v[v[v[a]]], v[v[v[v[a]]]], f]
    [(3, c), (4, #v[c[0], c[3], c[1], c[4], c[2], c[5]])]
  | 6 =>
    let d := (moved.filter fun x => x ≠ a ∧ x ≠ v[a] ∧ x ≠ v[v[a]]).getD 0 0
    [(2, #v[a, v[a], v[v[a]], d, v[d], v[v[d]]]), (2, #v[d, v[d], v[v[d]], a, v[a], v[v[a]]])]
  | _ => []

@[expose] def conjTestWith (c v : Vector (Fin 6) 6) (j : Fin 5) : Bool :=
  decide (∀ x : Fin 6, v[c[x]] = c[classReps[j][x]])

@[expose] def conjTest (v : Vector (Fin 6) 6) (p : Fin 5 × Vector (Fin 6) 6) : Bool :=
  conjTestWith (Vector.ofFn ⇑(a6OfImages p.2 : Perm (Fin 6))) v p.1

@[expose] def classCheckElem (v : Vector (Fin 6) 6) : Bool :=
  !isIdVec (powImages v 45) || (conjCandidates v).any (conjTest v)

@[expose] def allImages : Multiset (Vector (Fin 6) 6) :=
  (Finset.univ : Finset (alternatingGroup (Fin 6))).val.map fun c : alternatingGroup (Fin 6) =>
    Vector.ofFn ⇑(c : Perm (Fin 6))

@[expose] def classCheckWith (all : Multiset (Vector (Fin 6) 6)) : Bool :=
  decide (∀ v ∈ all, classCheckElem v = true)

@[expose] def classCheck : Bool := classCheckWith allImages

@[expose] def threeCycle : alternatingGroup (Fin 6) := a6OfImages #v[1, 2, 0, 3, 4, 5]

@[expose] def fiveCycle : alternatingGroup (Fin 6) := a6OfImages #v[1, 2, 3, 4, 0, 5]

@[expose] def traceCheckWith (a b : Vector (Vector (ZMod 2) 4) 4)
    (c : Vector (Vector FieldFour 8) 8) : Bool :=
  decide (Matrix.trace (untab a) = 1) && decide (Matrix.trace (untab b) = 0) &&
    decide (Matrix.trace (untab c) = ω₂)

@[expose] def traceCheck : Bool :=
  traceCheckWith (rep4aTab threeCycle) (rep4bTab threeCycle) (rep8aTab fiveCycle)

@[expose] def basisProj : Vector (Vector FieldFour 16) 16 := tab (basis8 * proj8)

@[expose] def zeroTab16 : Vector (Vector FieldFour 16) 16 := tab 0

@[expose] def selectOmega (K : Vector (Vector FieldFour 16) 16) : Vector (Vector FieldFour 16) 16 :=
  if Matrix.trace (untab K * untab basisProj) = ω₂ then K else zeroTab16

@[expose] def selectFiveCycle (g : alternatingGroup (Fin 6)) : Vector (Vector FieldFour 16) 16 :=
  if (g : Perm (Fin 6)).support.card = 5 then selectOmega (kronTab g) else zeroTab16

@[expose] def addTab {m n : ℕ} {α : Type*} [Add α] (a b : Vector (Vector α n) m) :
    Vector (Vector α n) m :=
  Vector.ofFn fun i => Vector.ofFn fun j => a[i][j] + b[i][j]

theorem addTab_left_comm {m n : ℕ} {α : Type*} [AddCommSemigroup α]
    (a b c : Vector (Vector α n) m) : addTab a (addTab b c) = addTab b (addTab a c) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [addTab, Vector.getElem_ofFn, Fin.getElem_fin]
  exact add_left_comm _ _ _

@[expose] def fiveCycleStep (g : alternatingGroup (Fin 6))
    (acc : Vector (Vector FieldFour 16) 16) : Vector (Vector FieldFour 16) 16 :=
  addTab (selectFiveCycle g) acc

instance : LeftCommutative fiveCycleStep := ⟨fun _ _ _ => addTab_left_comm _ _ _⟩

@[expose] def sumFiveCycles (s : Multiset (alternatingGroup (Fin 6))) :
    Vector (Vector FieldFour 16) 16 :=
  s.foldr fiveCycleStep zeroTab16

@[expose] def isOmegaScalar (S : Vector (Vector FieldFour 8) 8) : Bool :=
  decide (untab S = ω₂ • 1)

@[expose] def classSumCheck : Bool :=
  isOmegaScalar (rep8aOfKron (sumFiveCycles (Finset.univ : Finset (alternatingGroup (Fin 6))).val))

end CFSG.CharacterTheory.SteinbergBY.AlternatingSix
