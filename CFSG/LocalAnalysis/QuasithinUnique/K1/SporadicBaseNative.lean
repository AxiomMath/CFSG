module

public import Std.Data.HashMap.Basic

public section

namespace CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def img (s : Array Nat) (p : Nat) : Nat := s.getD p 0

@[expose] def ptsOf (B : List Nat) (G : List (Array Nat)) : List Nat :=
  B ++ G.flatMap fun s => B.map (img s)

@[expose] def applyTab (s : Array Nat) (T : List Nat) : List Nat := T.map (img s)

@[expose] def keyNat (n r : Nat) (T : List Nat) : Nat :=
  (T.take r).foldl (fun acc q => acc * n + q) 0

@[expose] def conjImg (z g gi : Array Nat) (p : Nat) : Nat := img gi (img z (img g p))

@[expose] def BaseEnumOK (n : Nat) (B : List Nat) (G Gi : List (Array Nat))
    (Ts : Array (List Nat)) (par cl : Array Nat) : Prop :=
  0 < Ts.size ∧ Ts[0]! = ptsOf B G ∧ par.size = Ts.size ∧
  (∀ i < Ts.size, 0 < i → par[i]! < i ∧ ∃ s ∈ G, Ts[i]! = applyTab s Ts[par[i]!]!) ∧
  (Ts.toList.map (keyNat n B.length)).Nodup ∧
  (∀ i < Ts.size, ∀ j < G.length, cl[i * (G.length + Gi.length) + j]! < Ts.size ∧
    Ts[cl[i * (G.length + Gi.length) + j]!]! = applyTab G[j]! Ts[i]!) ∧
  (∀ i < Ts.size, ∀ j < Gi.length, cl[i * (G.length + Gi.length) + G.length + j]! < Ts.size ∧
    Ts[cl[i * (G.length + Gi.length) + G.length + j]!]! = applyTab Gi[j]! Ts[i]!)

instance (n : Nat) (B : List Nat) (G Gi : List (Array Nat)) (Ts : Array (List Nat))
    (par cl : Array Nat) : Decidable (BaseEnumOK n B G Gi Ts par cl) := by
  unfold BaseEnumOK; infer_instance

@[expose] def bfsLoopB (n r : Nat) (G : List (Array Nat)) :
    Nat → Nat → Array (List Nat) × Array Nat × Std.HashMap Nat Nat →
      Array (List Nat) × Array Nat × Std.HashMap Nat Nat
  | 0, _, st => st
  | fuel + 1, i, st =>
    if i < st.1.size then
      let T := st.1[i]!
      let st' := G.foldl (fun acc s =>
        let T' := applyTab s T
        let k := keyNat n r T'
        if acc.2.2.contains k then acc
        else (acc.1.push T', acc.2.1.push i, acc.2.2.insert k acc.1.size)) st
      bfsLoopB n r G fuel (i + 1) st'
    else st

@[expose] def bfsEnumB (n : Nat) (B : List Nat) (G Gi : List (Array Nat)) (fuel : Nat) :
    Array (List Nat) × Array Nat × Array Nat :=
  let P := ptsOf B G
  let r := B.length
  let st := bfsLoopB n r G fuel 0 (#[P], #[0], (∅ : Std.HashMap Nat Nat).insert (keyNat n r P) 0)
  let cl := (List.range st.1.size).foldl (fun acc i =>
    (G ++ Gi).foldl (fun acc' s => acc'.push ((st.2.2.getD (keyNat n r (applyTab s st.1[i]!)) 0)))
      acc) (#[] : Array Nat)
  (st.1, st.2.1, cl)

@[expose] def BaseCert (n : Nat) (B : List Nat) (qp : List (Array Nat × Array Nat))
    (z g gi h hi : Array Nat) (Ts : Array (List Nat)) (par cl : Array Nat) (k : Nat) : Prop :=
  (∀ p ∈ qp, ∀ q < n, img p.2 (img p.1 q) = q) ∧
  (∀ q < n, img gi (img g q) = q) ∧ (∀ q < n, img hi (img h q) = q) ∧
  BaseEnumOK n B (qp.map Prod.fst) (qp.map Prod.snd) Ts par cl ∧
  Ts.size = 2 ^ k ∧
  (∀ T ∈ Ts.toList, (∀ t < (qp.map Prod.fst).length, ∀ j < B.length,
      T.getD (B.length * (1 + t) + j) 0 = img ((qp.map Prod.fst).getD t #[]) (T.getD j 0)) →
    T = ptsOf B (qp.map Prod.fst) ∨ T = applyTab z (ptsOf B (qp.map Prod.fst))) ∧
  (ptsOf B (qp.map Prod.fst)).map (conjImg z g gi) ∈ Ts.toList ∧
  (ptsOf B (qp.map Prod.fst)).map (conjImg z h hi) ∈ Ts.toList ∧
  ∃ j < B.length, conjImg z g gi (conjImg z h hi (B.getD j 0)) ≠
    conjImg z h hi (conjImg z g gi (B.getD j 0))

instance (n : Nat) (B : List Nat) (qp : List (Array Nat × Array Nat)) (z g gi h hi : Array Nat)
    (Ts : Array (List Nat)) (par cl : Array Nat) (k : Nat) :
    Decidable (BaseCert n B qp z g gi h hi Ts par cl k) := by
  unfold BaseCert; infer_instance

@[expose] def compArr (s t : Array Nat) : Array Nat := t.map fun j => s[j]!

@[expose] def slpStepA (acc : Array (Array Nat)) (p : Nat × Nat) : Array (Array Nat) :=
  acc.push (compArr acc[p.1]! acc[p.2]!)

@[expose] def slpTabsA (ta tb : Array Nat) (prog : List (Nat × Nat)) : Array (Array Nat) :=
  prog.foldl slpStepA #[ta, tb]

@[expose] def slpValidAux : List (Nat × Nat) → Nat → Bool
  | [], _ => true
  | p :: rest, m => decide (p.1 < m ∧ p.2 < m) && slpValidAux rest (m + 1)

@[expose] def BaseCertS (n : Nat) (B : List Nat) (T : Array (Array Nat)) (qp : List (Nat × Nat))
    (zn gn gin hn hin : Nat) (Ts : Array (List Nat)) (par cl : Array Nat) (k : Nat) : Prop :=
  (∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size) ∧
  zn < T.size ∧ gn < T.size ∧ gin < T.size ∧ hn < T.size ∧ hin < T.size ∧
  BaseCert n B (qp.map fun p => (T[p.1]!, T[p.2]!)) T[zn]! T[gn]! T[gin]! T[hn]! T[hin]!
    Ts par cl k

instance (n : Nat) (B : List Nat) (T : Array (Array Nat)) (qp : List (Nat × Nat))
    (zn gn gin hn hin : Nat) (Ts : Array (List Nat)) (par cl : Array Nat) (k : Nat) :
    Decidable (BaseCertS n B T qp zn gn gin hn hin Ts par cl k) := by
  unfold BaseCertS; infer_instance

end CFSG.QuasithinUnique.K1.SporadicPerm
