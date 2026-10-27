module


public section

namespace CFSG.QuasithinUnique.Setup.X1

@[expose] def arrImg (t : Array Nat) (p : Nat) : Nat := t.getD p 0

@[expose] def cArr (s t : Array Nat) : Array Nat := t.map fun j => s.getD j 0

@[expose] def bfsExpand (ts : List (Array Nat)) (x : Nat) (st : Array Bool × List Nat) :
    Array Bool × List Nat :=
  ts.foldl (fun acc t =>
    let y := arrImg t x
    if acc.1.getD y true then acc else (acc.1.set! y true, y :: acc.2)) st

@[expose] def bfsAux (ts : List (Array Nat)) : Nat → Array Bool → List Nat → Array Bool
  | 0, vis, _ => vis
  | _ + 1, vis, [] => vis
  | f + 1, vis, x :: q =>
    let st := bfsExpand ts x (vis, q)
    bfsAux ts f st.1 st.2

@[expose] def bfsVis (N : Nat) (ts : List (Array Nat)) (s : Nat) : Array Bool :=
  bfsAux ts (N + 1) ((Array.replicate N false).set! s true) [s]

@[expose] def ClosedOK (N : Nat) (ts : List (Array Nat)) (s : Nat) (vis : Array Bool) : Prop :=
  vis.getD s false = true ∧
    ∀ i < N, vis.getD i false = true → ∀ t ∈ ts, vis.getD (arrImg t i) false = true

instance (N : Nat) (ts : List (Array Nat)) (s : Nat) (vis : Array Bool) :
    Decidable (ClosedOK N ts s vis) := by
  unfold ClosedOK; infer_instance

end CFSG.QuasithinUnique.Setup.X1
