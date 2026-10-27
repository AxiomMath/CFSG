module

public import CFSG.Blueprint.ChevalleyRootArtifact
public meta import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open CFSG.Blueprint.Chevalley

@[expose] def e8CartanList (δ : Fin Tag.E8.rank → ℤ) : List ℤ :=
  List.ofFn fun i => ∑ j, Tag.E8.cartan i j * δ j

@[expose] def e8Dot (γ δ : Fin Tag.E8.rank → ℤ) : ℤ :=
  (List.zipWith (· * ·) (List.ofFn γ) (e8CartanList δ)).sum

@[expose] def e8ReflectL (i : Fin Tag.E8.rank) (l : List ℤ) : List ℤ :=
  List.ofFn fun k : Fin Tag.E8.rank =>
    l.getD k 0 - if k = i then ∑ j : Fin Tag.E8.rank, Tag.E8.cartan i j * l.getD j 0 else 0

@[expose] def zxCheckB (F : List (Fin Tag.E8.rank → ℤ))
    (Δc : List ((Fin Tag.E8.rank → ℤ) × List ℤ))
    (kills : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)))
    (ws : List (List (Fin Tag.E8.rank))) : Bool :=
  decide (F ++ kills.map Prod.fst).Nodup &&
    (F ++ kills.map Prod.fst).all (fun α =>
      decide (List.ofFn α ∈ Tag.artifactRoots .E8) && decide (15 ≤ height α)) &&
    decide (F.Pairwise fun σ σ' => e8Dot σ σ' = 0) &&
    (Tag.artifactRoots .E8).all (fun l => decide (l.sum ≤ 0) ||
      decide (l ∈ (F ++ kills.map Prod.fst).map List.ofFn) ||
      Δc.any fun p => decide ((List.zipWith (· * ·) l p.2).sum = -1)) &&
    Δc.all (fun p => decide (p.2 = e8CartanList p.1) &&
      decide (List.ofFn p.1 ∈ Tag.artifactRoots .E8) && decide (0 < height p.1) &&
      F.all fun σ => decide (0 ≤ (List.zipWith (· * ·) (List.ofFn σ) p.2).sum)) &&
    kills.all (fun p => decide (List.ofFn p.2 ∈ Tag.artifactRoots .E8) &&
      decide (List.ofFn (p.1 - p.2) ∈ Tag.artifactRoots .E8) && decide (0 < height (p.1 - p.2)) &&
      decide (p.1 - p.2 ∉ F ++ kills.map Prod.fst) && decide (-p.2 ≠ p.1) &&
      decide (-p.2 ≠ -p.1) &&
      (F ++ kills.map Prod.fst).all (fun α => decide (α = p.1) || (decide (-p.2 ≠ α) &&
        decide (-p.2 ≠ -α) && decide (List.ofFn (-p.2 + α) ∉ Tag.artifactRoots .E8))) &&
      F.all fun σ => decide (0 ≤ e8Dot (-p.2) σ)) &&
    ws.all (fun ω => decide ((F.map fun σ => ω.foldr e8ReflectL (List.ofFn σ)).Perm
        (F.map List.ofFn)) &&
      F.all fun σ =>
        decide (ω.foldr e8ReflectL (ω.foldr e8ReflectL (List.ofFn σ)) = List.ofFn σ)) &&
    decide (List.zipWith (fun ω σ => ω.foldr e8ReflectL (List.ofFn σ)) ws F =
      F.tail.map List.ofFn)

@[expose] def e8ZxFrameX : List (Fin Tag.E8.rank → ℤ) := [![2, 3, 4, 6, 5, 4, 3, 2]]

@[expose] def e8ZxFrameY : List (Fin Tag.E8.rank → ℤ) :=
  [![2, 2, 4, 5, 4, 3, 2, 1], ![2, 3, 3, 5, 4, 3, 2, 1]]

@[expose] def e8ZxFrameZ : List (Fin Tag.E8.rank → ℤ) :=
  [![2, 2, 3, 4, 3, 2, 2, 1], ![1, 2, 3, 4, 3, 3, 2, 1], ![1, 2, 2, 4, 4, 3, 2, 1]]

@[expose] def e8ZxFrameU : List (Fin Tag.E8.rank → ℤ) :=
  [![2, 2, 3, 4, 3, 2, 1, 0], ![1, 2, 3, 4, 3, 2, 1, 1], ![1, 2, 2, 3, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 2, 1]]

@[expose] def e8ZxDeltaX : List ((Fin Tag.E8.rank → ℤ) × List ℤ) :=
  [(![1, 0, 0, 0, 0, 0, 0, 0], [2, 0, -1, 0, 0, 0, 0, 0]),
    (![0, 0, 1, 0, 0, 0, 0, 0], [-1, 0, 2, -1, 0, 0, 0, 0]),
    (![0, 0, 0, 1, 0, 0, 0, 0], [0, -1, -1, 2, -1, 0, 0, 0]),
    (![0, 1, 0, 1, 1, 0, 0, 0], [0, 1, -1, 0, 1, -1, 0, 0]),
    (![0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, -1, 1, 1, -1, 0]),
    (![0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, -1, 1, 1, -1]),
    (![0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, -1, 1, 1]),
    (![1, 2, 2, 3, 2, 2, 1, 1], [0, 1, 0, 0, -1, 1, -1, 1]),
    (![1, 1, 2, 3, 3, 2, 2, 1], [0, -1, 0, 0, 1, -1, 1, 0]),
    (![0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, -1, 2])]

@[expose] def e8ZxDeltaY : List ((Fin Tag.E8.rank → ℤ) × List ℤ) :=
  [(![1, 0, 0, 0, 0, 0, 0, 0], [2, 0, -1, 0, 0, 0, 0, 0]),
    (![0, 1, 1, 1, 0, 0, 0, 0], [-1, 1, 1, 0, -1, 0, 0, 0]),
    (![0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, -1, 2, -1, 0, 0]),
    (![0, 0, 0, 1, 0, 0, 0, 0], [0, -1, -1, 2, -1, 0, 0, 0]),
    (![0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, -1, 2, -1, 0]),
    (![0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, -1, 2, -1]),
    (![0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, -1, 2]),
    (![2, 2, 4, 5, 4, 3, 2, 1], [0, -1, 1, 0, 0, 0, 0, 0])]

@[expose] def e8ZxKillsY : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(![2, 3, 4, 6, 5, 4, 3, 2], ![0, 0, 0, 0, 0, 0, 0, 1])]

@[expose] def e8ZxWordsY : List (List (Fin Tag.E8.rank)) :=
  [([1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2] : List (Fin 8))]

@[expose] def e8ZxDeltaZ : List ((Fin Tag.E8.rank → ℤ) × List ℤ) :=
  [(![0, 1, 0, 0, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0, 0]),
    (![0, 0, 0, 1, 0, 0, 0, 0], [0, -1, -1, 2, -1, 0, 0, 0]),
    (![0, 0, 1, 1, 1, 0, 0, 0], [-1, -1, 1, 0, 1, -1, 0, 0]),
    (![1, 0, 1, 1, 1, 1, 0, 0], [1, -1, 0, 0, 0, 1, -1, 0]),
    (![0, 0, 0, 0, 1, 1, 1, 0], [0, 0, 0, -1, 1, 0, 1, -1]),
    (![0, 0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 0, -1, 1, 0, 1]),
    (![0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, -1, 2]),
    (![0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, -1, 2, -1]),
    (![1, 2, 3, 4, 3, 3, 2, 1], [-1, 0, 1, 0, -1, 1, 0, 0])]

@[expose] def e8ZxKillsZ : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(![2, 3, 4, 6, 5, 4, 3, 2], ![0, 0, 0, 0, 0, 0, 0, 1])]

@[expose] def e8ZxWordsZ : List (List (Fin Tag.E8.rank)) :=
  [([3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 0, 3, 1, 2, 3, 4, 3, 2, 1, 3, 0] : List (Fin 8)),
    ([0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 0, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 0,
      2] : List (Fin 8))]

@[expose] def e8ZxDeltaU : List ((Fin Tag.E8.rank → ℤ) × List ℤ) :=
  [(![0, 1, 0, 0, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0, 0]),
    (![0, 0, 0, 1, 1, 1, 0, 0], [0, -1, -1, 1, 0, 1, -1, 0]),
    (![0, 0, 1, 1, 1, 1, 1, 0], [-1, -1, 1, 0, 0, 0, 1, -1]),
    (![1, 0, 1, 1, 1, 1, 1, 1], [1, -1, 0, 0, 0, 0, 0, 1]),
    (![0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, -1, 2, -1, 0, 0]),
    (![1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, -1, 0, 0, 0]),
    (![0, 1, 1, 1, 0, 0, 0, 0], [-1, 1, 1, 0, -1, 0, 0, 0]),
    (![1, 2, 2, 4, 3, 2, 2, 1], [0, 0, -1, 1, 0, -1, 1, 0])]

@[expose] def e8ZxKillsU : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(![2, 3, 4, 6, 5, 3, 2, 1], ![0, 0, 0, 0, 1, 0, 0, 0]),
    (![2, 3, 4, 6, 5, 4, 2, 1], ![0, 0, 0, 1, 1, 1, 0, 0]),
    (![2, 3, 4, 6, 5, 4, 3, 1], ![0, 0, 1, 1, 1, 1, 1, 0]),
    (![2, 3, 4, 6, 5, 4, 3, 2], ![1, 0, 1, 1, 1, 1, 1, 1])]

@[expose] def e8ZxWordsU : List (List (Fin Tag.E8.rank)) :=
  [([2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 0, 2, 3, 4, 5, 6, 5, 4, 3, 2, 0] : List (Fin 8)),
    ([4, 5, 6, 5, 4, 2, 3, 4, 3, 2] : List (Fin 8)),
    ([3, 4, 3, 4, 5, 4] : List (Fin 8))]

@[expose] def e8ZxCheckX : Bool := zxCheckB e8ZxFrameX e8ZxDeltaX [] []

@[expose] def e8ZxCheckY : Bool := zxCheckB e8ZxFrameY e8ZxDeltaY e8ZxKillsY e8ZxWordsY

@[expose] def e8ZxCheckZ : Bool := zxCheckB e8ZxFrameZ e8ZxDeltaZ e8ZxKillsZ e8ZxWordsZ

@[expose] def e8ZxCheckU : Bool := zxCheckB e8ZxFrameU e8ZxDeltaU e8ZxKillsU e8ZxWordsU

end CFSG.ComponentClassification.RankTwoExceptional.E8
