module

public import CFSG.LieType.Ree.FixedWeylData

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Images

variable {τ : Tag}

@[expose] def simpleImages
    (w : WeylGroup τ) : List (List ℤ) :=
  List.ofFn fun i => List.ofFn (w • (Pi.single i 1 : Fin τ.rank → ℤ))

variable (τ) in
@[expose] def wordImages (ω : List (Fin τ.rank)) : List (List ℤ) :=
  List.ofFn fun i => List.ofFn (ω.foldr (reflect τ) (Pi.single i 1))

theorem simpleImages_wordProd
    (ω : List (Fin τ.rank)) :
    simpleImages ((coxeterSystem τ).wordProd ω) = wordImages τ ω := by
  simp only [simpleImages, wordImages, CFSG.LieType.Ree.wordProd_smul]

theorem simpleImages_injective
    : Function.Injective (simpleImages (τ := τ)) := by
  intro w w' h
  have h1 := List.ofFn_injective h
  exact ext_single fun i => List.ofFn_injective (congrFun h1 i)

theorem getD_simpleImages
    (w : WeylGroup τ) (l i : Fin τ.rank) :
    ((simpleImages w).getD l []).getD i 0 = (w • (Pi.single l 1 : Fin τ.rank → ℤ)) i := by
  simp [simpleImages, List.getD_eq_getElem?_getD]

theorem sum_getD_simpleImages
    (w : WeylGroup τ) (l : Fin τ.rank) :
    ((simpleImages w).getD l []).sum = height (w • (Pi.single l 1 : Fin τ.rank → ℤ)) := by
  rw [simpleImages, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, List.sum_ofFn]
  rfl

end Images

namespace ReeTag

variable (t : ReeTag)

@[expose] def fixedOrbitRep : (t : ReeTag) → Fin t.fixedOrbitCount → Fin t.tag.rank
  | G2, _ => (0 : Fin 2)
  | F4, j => if j.val = 0 then (0 : Fin 4) else (1 : Fin 4)

@[expose] def fixedOrbitIndex : (t : ReeTag) → Fin t.tag.rank → Fin t.fixedOrbitCount
  | G2, _ => (0 : Fin 1)
  | F4, i => if i.val = 0 ∨ i.val = 3 then (0 : Fin 2) else (1 : Fin 2)

variable {t}

theorem mem_fixedOrbitSet (j : Fin t.fixedOrbitCount) (i : Fin t.tag.rank) :
    i ∈ t.fixedOrbitSet j ↔ t.fixedOrbitIndex i = j := by
  revert j i
  cases t
  · show ∀ (j : Fin 1) (i : Fin 2), i ∈ ({0, 1} : Set (Fin 2)) ↔ (0 : Fin 1) = j
    intro j i
    fin_cases j
    fin_cases i <;> simp
  · show ∀ (j : Fin 2) (i : Fin 4),
      i ∈ (if j.val = 0 then ({0, 3} : Set (Fin 4)) else ({1, 2} : Set (Fin 4))) ↔
        (if i.val = 0 ∨ i.val = 3 then (0 : Fin 2) else (1 : Fin 2)) = j
    intro j i
    fin_cases j <;> fin_cases i <;> simp

theorem fixedOrbitIndex_eq_iff (i : Fin t.tag.rank) (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitIndex i = j ↔ i = t.fixedOrbitRep j ∨ i = t.perm (t.fixedOrbitRep j) := by
  revert i j
  cases t <;> decide

theorem fixedOrbitIndex_fixedOrbitRep (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitIndex (t.fixedOrbitRep j) = j :=
  ((fixedOrbitIndex_eq_iff _ j).2 (Or.inl rfl))

theorem fixedOrbitIndex_perm (i : Fin t.tag.rank) :
    t.fixedOrbitIndex (t.perm i) = t.fixedOrbitIndex i := by
  revert i
  cases t <;> decide

theorem fixedOrbitIndex_of_mem_fixedOrbitWord (j : Fin t.fixedOrbitCount) :
    ∀ i ∈ t.fixedOrbitWord j, t.fixedOrbitIndex i = j := by
  revert j
  cases t <;> decide

variable (t)

@[expose] def fixedWeylOrder : ReeTag → ℕ
  | G2 => 2
  | F4 => 16

@[expose] def fixedRelWord : (t : ReeTag) → Fin t.fixedWeylOrder → List (Fin t.fixedOrbitCount)
  | G2, k => ([[], [0]] : List (List (Fin 1))).getD k.val []
  | F4, k => ([[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [1, 0, 1], [0, 1, 0, 1], [1, 0, 1, 0],
      [0, 1, 0, 1, 0], [1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0],
      [0, 1, 0, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1]] :
      List (List (Fin 2))).getD k.val []

@[expose] def fixedRelMat : (t : ReeTag) → Fin t.fixedWeylOrder → List (List ℤ)
  | G2, k => ([[[1, 0], [0, 1]], [[-1, 0], [0, -1]]] : List (List (List ℤ))).getD k.val []
  | F4, k => ([[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
      [[-1, 0, 0, 0], [1, 1, 0, 0], [0, 0, 1, 1], [0, 0, 0, -1]],
      [[1, 2, 2, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 1, 2, 1]],
      [[1, 2, 2, 2], [-1, -1, 0, 0], [0, 0, -1, -1], [1, 1, 2, 1]],
      [[-1, -2, -2, 0], [1, 1, 2, 0], [0, 1, 1, 1], [0, -1, -2, -1]],
      [[-1, -2, -2, -2], [0, 1, 2, 2], [1, 1, 1, 0], [-1, -1, -2, -1]],
      [[1, 2, 4, 2], [-1, -1, -2, 0], [0, -1, -1, -1], [1, 2, 2, 1]],
      [[1, 2, 4, 2], [0, -1, -2, -2], [-1, -1, -1, 0], [1, 2, 2, 1]],
      [[-1, -2, -4, -2], [0, 1, 2, 2], [1, 1, 1, 0], [-1, -2, -2, -1]],
      [[-1, -2, -4, -2], [1, 1, 2, 0], [0, 1, 1, 1], [-1, -2, -2, -1]],
      [[1, 2, 2, 2], [0, -1, -2, -2], [-1, -1, -1, 0], [1, 1, 2, 1]],
      [[1, 2, 2, 0], [-1, -1, -2, 0], [0, -1, -1, -1], [0, 1, 2, 1]],
      [[-1, -2, -2, -2], [1, 1, 0, 0], [0, 0, 1, 1], [-1, -1, -2, -1]],
      [[-1, -2, -2, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, -1, -2, -1]],
      [[1, 0, 0, 0], [-1, -1, 0, 0], [0, 0, -1, -1], [0, 0, 0, 1]],
      [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]] :
      List (List (List ℤ))).getD k.val []

@[expose] def fixedRelRight :
    (t : ReeTag) → Fin t.fixedWeylOrder → Fin t.fixedOrbitCount → Fin t.fixedWeylOrder
  | G2, k, _ => ([1, 0] : List (Fin 2)).getD k.val 0
  | F4, k, j => (([[1, 2], [0, 3], [4, 0], [5, 1], [2, 6], [3, 7], [8, 4], [9, 5], [6, 10],
      [7, 11], [12, 8], [13, 9], [10, 14], [11, 15], [15, 12], [14, 13]] :
      List (List (Fin 16))).getD k.val []).getD j.val 0

@[expose] def fixedOrbitRootList : (t : ReeTag) → Fin t.fixedOrbitCount →
    List (Fin t.tag.rank → ℤ)
  | G2, _ => ([![0, 1], ![1, 0], ![1, 1], ![1, 2], ![1, 3], ![2, 3]] : List (Fin 2 → ℤ))
  | F4, j => if j.val = 0 then ([![0, 0, 0, 1], ![1, 0, 0, 0]] : List (Fin 4 → ℤ))
      else ([![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 2, 0]] : List (Fin 4 → ℤ))

theorem wordImages_fixedRelWord (k : Fin t.fixedWeylOrder) :
    wordImages t.tag ((t.fixedRelWord k).flatMap t.fixedOrbitWord) = t.fixedRelMat k := by
  revert k
  cases t <;> decide +kernel

theorem wordImages_fixedRelWord_append (k : Fin t.fixedWeylOrder) (j : Fin t.fixedOrbitCount) :
    wordImages t.tag ((t.fixedRelWord k).flatMap t.fixedOrbitWord ++ t.fixedOrbitWord j) =
      t.fixedRelMat (t.fixedRelRight k j) := by
  revert k j
  cases t <;> decide +kernel

theorem fixedRelMat_injective : Function.Injective t.fixedRelMat := by
  intro k k'
  revert k k'
  cases t <;> decide +kernel

theorem fixedRelRight_length (k : Fin t.fixedWeylOrder) (j : Fin t.fixedOrbitCount) :
    if 0 < ((t.fixedRelMat k).getD (t.fixedOrbitRep j) []).sum then
      (t.fixedRelWord (t.fixedRelRight k j)).length = (t.fixedRelWord k).length + 1
    else (t.fixedRelWord (t.fixedRelRight k j)).length + 1 = (t.fixedRelWord k).length := by
  revert k j
  cases t <;> decide +kernel

theorem fixedRelWord_zero :
    ∃ k : Fin t.fixedWeylOrder, t.fixedRelWord k = [] := by
  cases t
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨0, by decide⟩, rfl⟩

theorem fixedRelMat_parabolic (k : Fin t.fixedWeylOrder) (j : Fin t.fixedOrbitCount) :
    t.fixedRelWord k = [] ∨ t.fixedRelWord k = [j] ∨
      ∃ l i : Fin t.tag.rank, t.fixedOrbitIndex i ≠ j ∧
        ((t.fixedRelMat k).getD l []).getD i 0 ≠ (Pi.single l 1 : Fin t.tag.rank → ℤ) i := by
  revert k j
  cases t <;> decide +kernel

theorem fixedOrbitWord_root_check_mem :
    ∀ k < t.tag.rootCertificate.roots.length, ∀ j : Fin t.fixedOrbitCount,
      0 < height (t.tag.rootCertificate.root k) →
        (∀ i, t.fixedOrbitIndex i ≠ j → t.tag.rootCertificate.root k i = 0) →
          0 < height (-(t.fixedOrbitWord j).foldr (reflect t.tag) (t.tag.rootCertificate.root k)) ∧
            ∀ i, t.fixedOrbitIndex i ≠ j →
              (t.fixedOrbitWord j).foldr (reflect t.tag) (t.tag.rootCertificate.root k) i = 0 := by
  cases t <;> decide +kernel

theorem fixedOrbitWord_root_check_not_mem :
    ∀ k < t.tag.rootCertificate.roots.length, ∀ j : Fin t.fixedOrbitCount,
      0 < height (t.tag.rootCertificate.root k) →
        (∃ i, t.fixedOrbitIndex i ≠ j ∧ t.tag.rootCertificate.root k i ≠ 0) →
          0 < height ((t.fixedOrbitWord j).foldr (reflect t.tag) (t.tag.rootCertificate.root k)) ∧
            ∃ i, t.fixedOrbitIndex i ≠ j ∧
              (t.fixedOrbitWord j).foldr (reflect t.tag) (t.tag.rootCertificate.root k) i ≠ 0 := by
  cases t <;> decide +kernel

theorem fixedOrbitRootList_check :
    (∀ k < t.tag.rootCertificate.roots.length, ∀ j : Fin t.fixedOrbitCount,
      (0 < height (t.tag.rootCertificate.root k) ∧
        ∀ i, t.fixedOrbitIndex i ≠ j → t.tag.rootCertificate.root k i = 0) ↔
        t.tag.rootCertificate.root k ∈ t.fixedOrbitRootList j) ∧
    ∀ j : Fin t.fixedOrbitCount, ∀ α ∈ t.fixedOrbitRootList j,
      ∃ k < t.tag.rootCertificate.roots.length, t.tag.rootCertificate.root k = α := by
  cases t <;> decide +kernel

theorem fixedOrbitRootList_nodup (j : Fin t.fixedOrbitCount) : (t.fixedOrbitRootList j).Nodup := by
  revert j
  cases t <;> decide

end ReeTag

end CFSG.LieType.Ree
