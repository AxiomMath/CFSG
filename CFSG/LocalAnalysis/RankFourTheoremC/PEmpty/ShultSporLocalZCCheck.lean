module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

class ZCKey (A : Type) where
  key : A → ℕ

instance (priority := low) zcKeyDefault (A : Type) : ZCKey A := ⟨fun _ => 0⟩

@[expose] def zcPermKey {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((List.ofFn (fun i => σ i)).take 6).foldl (fun h i => h * n + i.val) 0

instance zcKeyPerm (n : ℕ) : ZCKey (Equiv.Perm (Fin n)) := ⟨zcPermKey⟩

section Bfs

variable {A : Type} [DecidableEq A]

@[expose] def zcNew (acc l : List A) : List A :=
  (l.filter (fun y => decide (y ∉ acc))).dedup

@[expose] def zcBfsAux (step : A → List A) (cap : ℕ) : ℕ → List A → List A → List A
  | 0, acc, _ => acc
  | _ + 1, acc, [] => acc
  | fuel + 1, acc, fr@(_ :: _) =>
    if cap < acc.length then acc else
      let new := zcNew acc (fr.flatMap step)
      zcBfsAux step cap fuel (acc ++ new) new

@[expose] def zcBfs (step : A → List A) (cap fuel : ℕ) (seeds : List A) : List A :=
  let s := seeds.dedup
  zcBfsAux step cap fuel s s

@[expose] def zcMemK (key : A → ℕ) (OK : List (ℕ × A)) (y : A) : Bool :=
  let k := key y
  OK.any (fun q => q.1 == k && decide (q.2 = y))

@[expose] def zcAddK (key : A → ℕ) (acc : List (ℕ × A)) (l : List A) :
    List (ℕ × A) × List A :=
  l.foldl (fun st y => if zcMemK key st.1 y then st else ((key y, y) :: st.1, y :: st.2))
    (acc, [])

@[expose] def zcBfsKAux (key : A → ℕ) (step : A → List A) (cap : ℕ) :
    ℕ → List (ℕ × A) → List A → List (ℕ × A)
  | 0, acc, _ => acc
  | _ + 1, acc, [] => acc
  | fuel + 1, acc, fr@(_ :: _) =>
    if cap < acc.length then acc else
      let st := zcAddK key acc (fr.flatMap step)
      zcBfsKAux key step cap fuel st.1 st.2

@[expose] def zcBfsK (key : A → ℕ) (step : A → List A) (cap fuel : ℕ) (seeds : List A) :
    List A :=
  let st := zcAddK key [] seeds
  (zcBfsKAux key step cap fuel st.1 st.2).map Prod.snd

end Bfs

section Words

variable {A : Type} [Group A]

@[expose] def zcRStep (cn : A → A) (gens : List A) (x : A) : List A :=
  gens.map (fun s => cn (x * s))

@[expose] def zcCStep (cn : A → A) (gs : List A) (x : A) : List A :=
  gs.map (fun g => cn (g * x * g⁻¹))

@[expose] def zcPow (cn : A → A) (x : A) : ℕ → A
  | 0 => 1
  | e + 1 => cn (zcPow cn x e * x)

@[expose] def zcEval (cn : A → A) (a b : A) : PW → A
  | [] => 1
  | (c, e) :: w => cn (zcPow cn (if c then b else a) e * zcEval cn a b w)

end Words

section Check

variable {A : Type} [Group A] [DecidableEq A]

@[expose] def zcSubOK (cn : A → A) (hs : List (A × A × PSimple)) (cs L : List A) : Bool :=
  decide ((1 : A) ∈ L) && cs.all (fun c => decide (c ∈ L)) &&
  L.all (fun x => L.all (fun y => decide (cn (x * y) ∈ L))) &&
  L.all (fun x => decide (x⁻¹ ∈ L)) &&
  hs.any (fun t => L.all (fun v => decide (cn (t.1 * v * t.1⁻¹) ∈ L) &&
    decide (cn (t.2.1 * v * t.2.1⁻¹) ∈ L)))

@[expose] def zcPerU (cn : A → A) (fuel : ℕ) (z₀ : A) (p : ℕ) (hs : List (A × A × PSimple))
    (u : A) : Bool :=
  let cs := List.iterate (fun x => cn (z₀ * x * z₀⁻¹)) u p
  !(cs.all (fun x => cs.all (fun y => decide (x * y = y * x)))) ||
    zcSubOK cn hs cs (zcBfs (zcRStep cn cs) fuel fuel [1])

@[expose] def zcCheckWith (cn : A → A) (key : A → ℕ) (n p k : ℕ) (z₀ : A) (gens E cg O : List A)
    (hs : List (A × A × PSimple)) : Bool :=
  let OK := O.map (fun x => (key x, x))
  decide (zcPow cn z₀ p = 1) && decide (z₀ ≠ 1) &&
  decide (2 ^ k ∣ n) && decide (¬ 2 ^ (k + 1) ∣ n) &&
  (decide (E.length = 2 ^ k) && decide E.Nodup && decide ((1 : A) ∈ E) &&
    E.all (fun x => gens.all (fun s => decide (cn (x * s) ∈ E)))) &&
  O.all (fun x => cg.all (fun g => zcMemK key OK (cn (g * x * g⁻¹)))) &&
  E.all (fun s => decide (s * s = 1 → s ≠ 1 → zcMemK key OK s = true)) &&
  O.all (zcPerU cn n z₀ p hs) &&
  hs.all (fun t => t.2.2.check t.1 t.2.1 z₀)

@[expose] def ZCData.check [ZCKey A] (cn : A → A) (a b : A) (d : ZCData) (n : ℕ) : Bool :=
  let gens := d.syl.map (fun w => cn (zcEval cn a b w))
  let cg := [a, b, a⁻¹, b⁻¹]
  zcCheckWith cn ZCKey.key n d.p d.k (cn (zcEval cn a b d.z)) gens
    (zcBfs (zcRStep cn gens) (2 ^ d.k) n [1]) cg
    (zcBfsK ZCKey.key (zcCStep cn cg) n n (d.seeds.map (fun w => cn (zcEval cn a b w))))
    (d.hs.map (fun t => (cn (zcEval cn a b t.1), cn (zcEval cn a b t.2.1), t.2.2)))

end Check

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
