module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CosetNative
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

structure PipeData where
  n : Nat
  N : Nat
  ta : Array Nat
  tb : Array Nat
  tai : Array Nat
  tbi : Array Nat
  prog : List (Nat × Nat)
  qp : List (Nat × Nat)
  Aa : Array Nat
  Ab : Array Nat
  par : Array Nat
  gen : Array Nat
  repR : Array Nat
  xs : Array (List Nat)

@[expose] def treeStepT (ta tb par gen : Array Nat) (acc : Array (Array Nat)) (i : Nat) :
    Array (Array Nat) :=
  acc.push (compArr (if gen.getD i 0 = 0 then ta else tb) (acc.getD (par.getD i 0) #[]))

@[expose] def treeTabs (n N : Nat) (ta tb par gen : Array Nat) : Array (Array Nat) :=
  (List.range' 1 (N - 1)).foldl (treeStepT ta tb par gen) #[Array.range n]

@[expose] def treeStepU (tai tbi par gen : Array Nat) (acc : Array (Array Nat)) (i : Nat) :
    Array (Array Nat) :=
  acc.push (compArr (acc.getD (par.getD i 0) #[]) (if gen.getD i 0 = 0 then tai else tbi))

@[expose] def treeInvTabs (n N : Nat) (tai tbi par gen : Array Nat) : Array (Array Nat) :=
  (List.range' 1 (N - 1)).foldl (treeStepU tai tbi par gen) #[Array.range n]

@[expose] def omegaOf (N : Nat) (Aa Ab par gen : Array Nat) : Nat → Nat → Array Nat
  | 0, _ => Array.range N
  | fuel + 1, x =>
    if x = 0 then Array.range N
    else compArr (if gen.getD x 0 = 0 then Aa else Ab) (omegaOf N Aa Ab par gen fuel (par.getD x 0))

@[expose] def xsOK (N : Nat) (xs : Array (List Nat)) : Prop :=
  0 < xs.size ∧ xs.getD 0 [] = [] ∧ ∀ h < xs.size, ∀ x ∈ xs.getD h [], x < N

instance (N : Nat) (xs : Array (List Nat)) : Decidable (xsOK N xs) := by
  unfold xsOK; infer_instance

@[expose] def qpOK (n : Nat) (NT : Array (Array Nat)) (qp : List (Nat × Nat)) : Prop :=
  ∀ p ∈ qp, p.1 < NT.size ∧ p.2 < NT.size ∧
    ∀ q < n, img NT[p.2]! (img NT[p.1]! q) = q

instance (n : Nat) (NT : Array (Array Nat)) (qp : List (Nat × Nat)) : Decidable (qpOK n NT qp) := by
  unfold qpOK; infer_instance

@[expose] def aszOK (N : Nat) (Aa Ab : Array Nat) : Prop := N ≤ Aa.size ∧ N ≤ Ab.size

instance (N : Nat) (Aa Ab : Array Nat) : Decidable (aszOK N Aa Ab) := by
  unfold aszOK; infer_instance

@[expose] def treeValid (N : Nat) (par gen : Array Nat) : Prop :=
  par.size = N ∧ gen.size = N ∧ ∀ i < N, 0 < i → par.getD i 0 < i ∧ gen.getD i 0 < 2

instance (N : Nat) (par gen : Array Nat) : Decidable (treeValid N par gen) := by
  unfold treeValid; infer_instance

@[expose] def memR (n : Nat) (P : List Nat) (Ts : Array (List Nat)) (RT : Std.HashMap Nat Nat)
    (E : Array Nat) : Bool :=
  let cand := P.map (img E)
  match RT[keyNat n n cand]? with
  | some k => decide (Ts.getD k [] = cand)
  | none => false

@[expose] def keyMap (n : Nat) (Ts : Array (List Nat)) : Std.HashMap Nat Nat :=
  (Ts.foldl (fun (st : Std.HashMap Nat Nat × Nat) T => (st.1.insert (keyNat n n T) st.2, st.2 + 1))
    (∅, 0)).1

@[expose] def edgeOK (n N : Nat) (P : List Nat) (Ts : Array (List Nat)) (RT : Std.HashMap Nat Nat)
    (ta tb Aa Ab : Array Nat) (T U : Array (Array Nat)) : Bool :=
  (List.range N).all fun i =>
    decide (Aa.getD i 0 < N) && decide (Ab.getD i 0 < N) &&
    memR n P Ts RT (compArr (U.getD (Aa.getD i 0) #[]) (compArr ta (T.getD i #[]))) &&
    memR n P Ts RT (compArr (U.getD (Ab.getD i 0) #[]) (compArr tb (T.getD i #[])))

@[expose] def invValid (n : Nat) (ta tb tai tbi : Array Nat) : Prop :=
  ta.size = n ∧ tb.size = n ∧ tai.size = n ∧ tbi.size = n ∧
    ∀ q < n, tai.getD (ta.getD q 0) 0 = q ∧ tbi.getD (tb.getD q 0) 0 = q

instance (n : Nat) (ta tb tai tbi : Array Nat) : Decidable (invValid n ta tb tai tbi) := by
  unfold invValid; infer_instance

@[expose] def gensOm (ROm : List (Array Nat)) (N : Nat) (Aa Ab par gen : Array Nat)
    (xs : List Nat) : List (Array Nat) :=
  ROm ++ xs.map fun x => omegaOf N Aa Ab par gen x x

@[expose] def blocksOf (ROm : List (Array Nat)) (N : Nat) (Aa Ab par gen : Array Nat)
    (xs : Array (List Nat)) : Array (Array Bool) :=
  xs.map fun l => bfsVis N (gensOm ROm N Aa Ab par gen l) 0

@[expose] def repList (N : Nat) (repR : Array Nat) : List Nat :=
  (List.range N).foldl (fun acc i =>
    let x := repR.getD i 0
    if acc.contains x then acc else x :: acc) []

@[expose] def repOrbs (ROm : List (Array Nat)) (N : Nat) (reps : List Nat) :
    List (Nat × Array Bool) :=
  reps.map fun x => (x, bfsVis N ROm x)

@[expose] def repsOK (ROm : List (Array Nat)) (N : Nat) (repR : Array Nat) (reps : List Nat)
    (orbs : List (Nat × Array Bool)) : Prop :=
  (∀ i < N, repR.getD i 0 < N) ∧ (∀ i < N, repR.getD i 0 ∈ reps) ∧
  (∀ p ∈ orbs, ClosedOK N ROm p.1 p.2) ∧
  (∀ i < N, ∃ p ∈ orbs, p.1 = repR.getD i 0 ∧ p.2.getD i false = true)

instance (ROm : List (Array Nat)) (N : Nat) (repR : Array Nat) (reps : List Nat)
    (orbs : List (Nat × Array Bool)) : Decidable (repsOK ROm N repR reps orbs) := by
  unfold repsOK; infer_instance

@[expose] def blocksClosed (ROm : List (Array Nat)) (N : Nat) (Aa Ab par gen : Array Nat)
    (xs : Array (List Nat)) (blocks : Array (Array Bool)) : Prop :=
  blocks.size = xs.size ∧ ∀ h < xs.size,
    ClosedOK N (gensOm ROm N Aa Ab par gen (xs.getD h [])) 0 (blocks.getD h #[])

instance (ROm : List (Array Nat)) (N : Nat) (Aa Ab par gen : Array Nat) (xs : Array (List Nat))
    (blocks : Array (Array Bool)) : Decidable (blocksClosed ROm N Aa Ab par gen xs blocks) := by
  unfold blocksClosed; infer_instance

@[expose] def closureOK (ROm : List (Array Nat)) (N : Nat) (Aa Ab par gen : Array Nat)
    (xs : Array (List Nat)) (blocks : Array (Array Bool)) (reps : List Nat) : Prop :=
  ∀ h < xs.size, ∀ x ∈ reps, ∃ k < xs.size,
    bfsVis N (gensOm ROm N Aa Ab par gen (xs.getD h []) ++ [omegaOf N Aa Ab par gen x x]) 0 =
      blocks.getD k #[] ∧
    ClosedOK N (gensOm ROm N Aa Ab par gen (xs.getD h []) ++ [omegaOf N Aa Ab par gen x x]) 0
      (blocks.getD k #[])

instance (ROm : List (Array Nat)) (N : Nat) (Aa Ab par gen : Array Nat) (xs : Array (List Nat))
    (blocks : Array (Array Bool)) (reps : List Nat) :
    Decidable (closureOK ROm N Aa Ab par gen xs blocks reps) := by
  unfold closureOK; infer_instance

@[expose] def blkSub (N : Nat) (b b' : Array Bool) : Prop :=
  ∀ i < N, b.getD i false = true → b'.getD i false = true

instance (N : Nat) (b b' : Array Bool) : Decidable (blkSub N b b') := by
  unfold blkSub; infer_instance

@[expose] def blkFull (N : Nat) (b : Array Bool) : Prop := ∀ i < N, b.getD i false = true

instance (N : Nat) (b : Array Bool) : Decidable (blkFull N b) := by
  unfold blkFull; infer_instance

@[expose] def blkSize (N : Nat) (b : Array Bool) : Nat :=
  (List.range N).foldl (fun c i => if b.getD i false then c + 1 else c) 0

@[expose] def shapeOK (N : Nat) (blocks : Array (Array Bool)) : Prop :=
  ∃ h₁ < blocks.size, ∃ h₂ < blocks.size,
    ¬ blkFull N (blocks.getD h₁ #[]) ∧ ¬ blkFull N (blocks.getD h₂ #[]) ∧
    blkSize N (blocks.getD h₁ #[]) ≠ blkSize N (blocks.getD h₂ #[]) ∧
    (∀ h < blocks.size, blkSub N (blocks.getD h₁ #[]) (blocks.getD h #[]) →
      blkSub N (blocks.getD h #[]) (blocks.getD h₁ #[]) ∨ blkFull N (blocks.getD h #[])) ∧
    (∀ h < blocks.size, blkSub N (blocks.getD h₂ #[]) (blocks.getD h #[]) →
      blkSub N (blocks.getD h #[]) (blocks.getD h₂ #[]) ∨ blkFull N (blocks.getD h #[])) ∧
    (∀ h < blocks.size, ¬ blkFull N (blocks.getD h #[]) →
      blkSub N (blocks.getD h #[]) (blocks.getD h₁ #[]) ∨
      blkSub N (blocks.getD h #[]) (blocks.getD h₂ #[]))

instance (N : Nat) (blocks : Array (Array Bool)) : Decidable (shapeOK N blocks) := by
  unfold shapeOK; infer_instance

end CFSG.QuasithinUnique.Setup.X1
