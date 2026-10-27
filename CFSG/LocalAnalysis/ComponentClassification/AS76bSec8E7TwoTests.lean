module

public import CFSG.Blueprint.ChevalleyRootArtifact
public meta import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint.Chevalley

@[expose] def e7CartanList (δ : Fin Tag.E7.rank → ℤ) : List ℤ :=
  List.ofFn fun i => ∑ j, Tag.E7.cartan i j * δ j

@[expose] def e7Dot (γ δ : Fin Tag.E7.rank → ℤ) : ℤ :=
  (List.zipWith (· * ·) (List.ofFn γ) (e7CartanList δ)).sum

@[expose] def e7ReflectL (i : Fin Tag.E7.rank) (l : List ℤ) : List ℤ :=
  List.ofFn fun k : Fin Tag.E7.rank =>
    l.getD k 0 - if k = i then ∑ j : Fin Tag.E7.rank, Tag.E7.cartan i j * l.getD j 0 else 0

@[expose] def e7ChainB {α : Type} (r : α → α → Bool) : List α → Bool
  | a :: b :: l => r a b && e7ChainB r (b :: l)
  | _ => true

@[expose] def e7LinkB (F : List (Fin Tag.E7.rank → ℤ))
    (p : (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) ×
      (Fin Tag.E7.rank → ℤ)) : Bool :=
  decide (List.ofFn p.1 ∈ Tag.artifactRoots .E7) &&
    decide (List.ofFn p.2.1 ∈ Tag.artifactRoots .E7) && decide (p.2.2.1 ∈ F) &&
    decide (p.2.2.2 ∈ F) && decide (p.2.2.1 ≠ p.2.2.2) &&
    decide (p.1 + p.2.2.1 = p.2.1 + p.2.2.2) &&
    decide (List.ofFn (p.1 + p.2.2.1) ∈ Tag.artifactRoots .E7) &&
    decide (0 < height (p.1 + p.2.2.1)) && decide (e7Dot p.1 p.2.2.1 = -1) &&
    decide (e7Dot p.2.1 p.2.2.2 = -1) &&
    F.all (fun σ => decide (σ = p.2.2.1) || decide (0 ≤ e7Dot p.1 σ)) &&
    F.all (fun σ => decide (σ = p.2.2.2) || decide (0 ≤ e7Dot p.2.1 σ)) &&
    decide (0 ≤ e7Dot p.1 (p.1 + p.2.2.1)) && decide (0 ≤ e7Dot (p.1 + p.2.2.1) p.2.2.1)

@[expose] def zxCheckE7 (F : List (Fin Tag.E7.rank → ℤ))
    (Δc : List ((Fin Tag.E7.rank → ℤ) × List ℤ))
    (kills : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)))
    (ws : List (List (Fin Tag.E7.rank)))
    (links : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) ×
      (Fin Tag.E7.rank → ℤ))) : Bool :=
  decide (F ++ kills.map Prod.fst).Nodup &&
    (F ++ kills.map Prod.fst).all (fun α =>
      decide (List.ofFn α ∈ Tag.artifactRoots .E7) && decide (9 ≤ height α)) &&
    decide (F.Pairwise fun σ σ' => e7Dot σ σ' = 0) &&
    (Tag.artifactRoots .E7).all (fun l => decide (l.sum ≤ 0) ||
      decide (l ∈ (F ++ kills.map Prod.fst).map List.ofFn) ||
      Δc.any fun p => decide ((List.zipWith (· * ·) l p.2).sum = -1)) &&
    Δc.all (fun p => decide (p.2 = e7CartanList p.1) &&
      decide (List.ofFn p.1 ∈ Tag.artifactRoots .E7) && decide (0 < height p.1) &&
      F.all fun σ => decide (0 ≤ (List.zipWith (· * ·) (List.ofFn σ) p.2).sum)) &&
    kills.all (fun p => decide (List.ofFn p.2 ∈ Tag.artifactRoots .E7) &&
      decide (List.ofFn (p.1 - p.2) ∈ Tag.artifactRoots .E7) && decide (0 < height (p.1 - p.2)) &&
      decide (p.1 - p.2 ∉ F ++ kills.map Prod.fst) && decide (-p.2 ≠ p.1) &&
      decide (-p.2 ≠ -p.1) &&
      (F ++ kills.map Prod.fst).all (fun α => decide (α = p.1) || (decide (-p.2 ≠ α) &&
        decide (-p.2 ≠ -α) && decide (List.ofFn (-p.2 + α) ∉ Tag.artifactRoots .E7))) &&
      F.all fun σ => decide (0 ≤ e7Dot (-p.2) σ)) &&
    ws.all (fun ω => decide ((F.map fun σ => ω.foldr e7ReflectL (List.ofFn σ)).Perm
        (F.map List.ofFn)) &&
      F.all fun σ =>
        decide (ω.foldr e7ReflectL (ω.foldr e7ReflectL (List.ofFn σ)) = List.ofFn σ)) &&
    links.all (e7LinkB F) &&
    e7ChainB (fun σ σ' => ws.any (fun ω => decide (ω.foldr e7ReflectL (List.ofFn σ) =
      List.ofFn σ')) || links.any fun p => decide (p.2.2.1 = σ) && decide (p.2.2.2 = σ')) F

@[expose] def e7ZxFrameX : List (Fin Tag.E7.rank → ℤ) :=
  [![2, 2, 3, 4, 3, 2, 1]]

@[expose] def e7ZxDeltaX : List ((Fin Tag.E7.rank → ℤ) × List ℤ) :=
  [(![0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1, 2]),
    (![0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, -1, 2, -1]),
    (![0, 0, 0, 0, 1, 0, 0], [0, 0, 0, -1, 2, -1, 0]),
    (![0, 0, 0, 1, 0, 0, 0], [0, -1, -1, 2, -1, 0, 0]),
    (![0, 0, 1, 0, 0, 0, 0], [-1, 0, 2, -1, 0, 0, 0]),
    (![0, 1, 0, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0]),
    (![1, 0, 0, 0, 0, 0, 0], [2, 0, -1, 0, 0, 0, 0])]

@[expose] def e7ZxFrameY : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 1]]

@[expose] def e7ZxDeltaY : List ((Fin Tag.E7.rank → ℤ) × List ℤ) :=
  [(![0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1, 2]),
    (![0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, -1, 2, -1]),
    (![0, 1, 0, 1, 1, 0, 0], [0, 1, -1, 0, 1, -1, 0]),
    (![0, 0, 1, 0, 0, 0, 0], [-1, 0, 2, -1, 0, 0, 0]),
    (![0, 0, 0, 1, 0, 0, 0], [0, -1, -1, 2, -1, 0, 0]),
    (![1, 0, 0, 0, 0, 0, 0], [2, 0, -1, 0, 0, 0, 0]),
    (![0, 0, 0, 0, 1, 1, 0], [0, 0, 0, -1, 1, 1, -1])]

@[expose] def e7ZxKillsY : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![2, 2, 3, 4, 3, 2, 1], ![1, 0, 0, 0, 0, 0, 0])]

@[expose] def e7ZxWordsY : List (List (Fin Tag.E7.rank)) :=
  [([4, 1] : List (Fin 7))]

@[expose] def e7ZxFrameZ : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 2, 2, 3, 2, 1, 0], ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1, 1]]

@[expose] def e7ZxDeltaZ : List ((Fin Tag.E7.rank → ℤ) × List ℤ) :=
  [(![0, 0, 0, 0, 1, 0, 0], [0, 0, 0, -1, 2, -1, 0]),
    (![0, 0, 1, 1, 0, 0, 0], [-1, -1, 1, 1, -1, 0, 0]),
    (![1, 0, 0, 0, 0, 0, 0], [2, 0, -1, 0, 0, 0, 0]),
    (![0, 1, 1, 1, 0, 0, 0], [-1, 1, 1, 0, -1, 0, 0]),
    (![0, 0, 0, 1, 1, 1, 0], [0, -1, -1, 1, 0, 1, -1]),
    (![0, 0, 1, 0, 0, 0, 0], [-1, 0, 2, -1, 0, 0, 0]),
    (![0, 1, 0, 1, 1, 1, 1], [0, 1, -1, 0, 0, 0, 1])]

@[expose] def e7ZxKillsZ : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![2, 2, 3, 4, 3, 2, 1], ![1, 0, 0, 0, 0, 0, 0])]

@[expose] def e7ZxWordsZ : List (List (Fin Tag.E7.rank)) :=
  [([5, 6, 5, 1, 3, 1] : List (Fin 7)), ([5, 3] : List (Fin 7))]

@[expose] def e7ZxFrameU : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 1, 1], ![0, 1, 1, 2, 2, 2, 1]]

@[expose] def e7ZxDeltaU : List ((Fin Tag.E7.rank → ℤ) × List ℤ) :=
  [(![0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1, 2]),
    (![0, 0, 0, 1, 0, 0, 0], [0, -1, -1, 2, -1, 0, 0]),
    (![0, 1, 0, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0]),
    (![1, 0, 1, 1, 1, 1, 0], [1, -1, 0, 0, 0, 1, -1]),
    (![0, 0, 1, 1, 1, 0, 0], [-1, -1, 1, 0, 1, -1, 0]),
    (![0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, -1, 1, 1])]

@[expose] def e7ZxKillsU : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![1, 2, 2, 4, 3, 2, 1], ![0, 0, 0, 1, 0, 0, 0]),
    (![1, 2, 3, 4, 3, 2, 1], ![0, 0, 1, 1, 1, 0, 0]),
    (![2, 2, 3, 4, 3, 2, 1], ![1, 0, 1, 1, 1, 1, 0])]

@[expose] def e7ZxWordsU : List (List (Fin Tag.E7.rank)) :=
  [([4, 2] : List (Fin 7)), ([4, 5, 4, 0, 2, 0] : List (Fin 7))]

@[expose] def e7ZxFrameV : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 2, 2, 3, 2, 1, 0], ![0, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 1]]

@[expose] def e7ZxDeltaV : List ((Fin Tag.E7.rank → ℤ) × List ℤ) :=
  [(![0, 0, 0, 1, 0, 0, 0], [0, -1, -1, 2, -1, 0, 0]),
    (![0, 1, 0, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0]),
    (![0, 0, 1, 1, 1, 0, 0], [-1, -1, 1, 0, 1, -1, 0]),
    (![1, 0, 1, 1, 1, 1, 0], [1, -1, 0, 0, 0, 1, -1]),
    (![0, 1, 0, 1, 1, 1, 1], [0, 1, -1, 0, 0, 0, 1]),
    (![0, 1, 1, 1, 1, 1, 1], [-1, 1, 1, -1, 0, 0, 1]),
    (![1, 1, 1, 1, 1, 1, 1], [1, 1, 0, -1, 0, 0, 1])]

@[expose] def e7ZxKillsV : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![1, 2, 2, 4, 3, 2, 1], ![0, 0, 0, 1, 0, 0, 0]),
    (![1, 2, 3, 4, 3, 2, 1], ![0, 0, 1, 1, 1, 0, 0]),
    (![2, 2, 3, 4, 3, 2, 1], ![1, 0, 1, 1, 1, 1, 0])]

@[expose] def e7ZxWordsV : List (List (Fin Tag.E7.rank)) :=
  [([4, 5, 4, 0, 2, 0] : List (Fin 7)), ([4, 2] : List (Fin 7))]

@[expose] def e7ZxLinksV : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) ×
    (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 0, 0, 0, 0, 1, 1], ![1, 1, 1, 1, 0, 0, 0], ![1, 2, 2, 3, 2, 1, 0],
    ![0, 1, 1, 2, 2, 2, 1])]

@[expose] def e7ZxCheckX : Bool := zxCheckE7 e7ZxFrameX e7ZxDeltaX [] [] []

@[expose] def e7ZxCheckY : Bool := zxCheckE7 e7ZxFrameY e7ZxDeltaY e7ZxKillsY e7ZxWordsY []

@[expose] def e7ZxCheckZ : Bool := zxCheckE7 e7ZxFrameZ e7ZxDeltaZ e7ZxKillsZ e7ZxWordsZ []

@[expose] def e7ZxCheckU : Bool := zxCheckE7 e7ZxFrameU e7ZxDeltaU e7ZxKillsU e7ZxWordsU []

@[expose] def e7ZxCheckV : Bool :=
  zxCheckE7 e7ZxFrameV e7ZxDeltaV e7ZxKillsV e7ZxWordsV e7ZxLinksV

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
