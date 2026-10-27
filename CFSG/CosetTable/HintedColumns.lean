module

public import CFSG.CosetTable.Hinted
public import CFSG.Certificates.CosetTableColumns

public section

namespace CFSG.CosetTable

variable {m : ℕ}

structure SBlock (m : ℕ) where
  path : List (Fin m × Bool)
  rels : List (List (Fin m × Bool))
  lim : ℕ
  scan : List ℕ

structure SHints (m : ℕ) where
  blocks : List (SBlock m)
  late : ℕ
  lateScan : List ℕ
  kCol : ℕ
  kScan : List ℕ

@[expose] def SHints.toHints (ws : List (List (Fin m × Bool))) (T : SHints m) : Hints where
  blocks := T.blocks.map fun b =>
    { path := b.path.map (colCode ws), rels := colCodes ws b.rels, lim := b.lim, scan := b.scan }
  late := T.late
  lateScan := T.lateScan
  kCol := T.kCol
  kScan := T.kScan

@[expose] def subsetCheckHinted (ws : List (List (Fin m × Bool))) (S : List ℕ) (T : SHints m)
    (cap n : ℕ) : Bool :=
  checkHinted (colParams ws ((subsetOf m S).map fun x => [(x, true)])) (T.toHints ws) cap n

theorem index_le_of_subsetCheckHinted (ws : List (List (Fin m × Bool))) (S : List ℕ)
    (T : SHints m) {cap n : ℕ} (h : subsetCheckHinted ws S T cap n = true) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).index ≤ n :=
  index_le_of_checkHinted (goodColParams ws _ _ (genSub_words_mem ws (subsetOf m S)))
    (by simpa [colParams, mkParams] using closure_colLetter ws) h

end CFSG.CosetTable
