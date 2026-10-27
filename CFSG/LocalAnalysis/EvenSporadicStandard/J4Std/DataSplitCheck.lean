module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataSplitBits
public import Certificates.Certificate25150

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataSplit

open CFSG.Sporadic.J4.QT Matrix

theorem chkRel_true : chkRel = true :=
  (Bool.and_eq_true_iff.1 Certificates.certificate25150).1

theorem chkDual_true : chkDual = true :=
  (Bool.and_eq_true_iff.1 Certificates.certificate25150).2

@[expose] def toMat (X : List ℕ) : Mat := maskMatrix F2 (fun i => X.getD i 0)

@[expose] def Amat (k : Fin 6) : Mat := maskMatrix F2 (fun i => letterRow (letterOf k) i)

@[expose] def splitPsi (k' : Fin 6) : Mat := toMat (psiRows.getD k' [])

@[expose] def splitCm (k : Fin 6) (r : Fin 5) : Mat := toMat ((cmRows.getD k []).getD r [])

@[expose] def splitWordsF (r : Fin 5) : List (Fin 6) := splitWords.getD r []

theorem getD_range_map {α : Type*} (f : ℕ → α) (d : α) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem toMat_apply (X : List ℕ) (i j : Fin 11) :
    toMat X i j = vecOfMask (X.getD i 0) j := rfl

theorem toMat_pMul (X Y : List ℕ) : toMat (pMul X Y) = toMat X * toMat Y := by
  ext i j
  have h1 : (pMul X Y).getD i 0 = rowsXor (fun j => Y.getD j 0) 11 (X.getD i 0) :=
    getD_range_map (fun i => rowsXor (fun j => Y.getD j 0) 11 (X.getD i 0)) 0 i.2
  have h2 := congrFun (vecOfMask_rowsXor (fun j => Y.getD j 0) (X.getD i 0)) j
  rw [toMat_apply, h1, h2]
  rfl

theorem toMat_pAdd (X Y : List ℕ) : toMat (pAdd X Y) = toMat X + toMat Y := by
  ext i j
  have h1 : (pAdd X Y).getD i 0 = X.getD i 0 ^^^ Y.getD i 0 :=
    getD_range_map (fun i => X.getD i 0 ^^^ Y.getD i 0) 0 i.2
  rw [toMat_apply, h1, vecOfMask_xor]
  rfl

theorem toMat_pOne : toMat pOne = 1 := by
  ext i j
  have h1 : pOne.getD i 0 = 2 ^ (i : ℕ) := getD_range_map (2 ^ ·) 0 i.2
  rw [toMat_apply, h1, Matrix.one_apply]
  simp only [vecOfMask, Nat.testBit_two_pow]
  by_cases h : (i : ℕ) = j
  · simp [h, Fin.ext_iff]
  · have : i ≠ j := fun h' => h (congrArg Fin.val h')
    simp [h, this]

theorem getD_replicate_zero (n i : ℕ) : (List.replicate n (0 : ℕ)).getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

theorem toMat_pZero : toMat pZero = 0 := by
  ext i j
  rw [toMat_apply]
  have h1 : pZero.getD i 0 = 0 := getD_replicate_zero 11 i
  rw [h1, vecOfMask_zero]
  rfl

theorem toMat_pLetter (k : Fin 6) : toMat (pLetter k) = Amat k := by
  ext i j
  have h1 : (pLetter k).getD i 0 = letterRow (letterOf k) i := getD_range_map _ 0 i.2
  rw [toMat_apply, h1]
  rfl

theorem pPair_spec (k' : Fin 6) (r : List (Fin 6)) :
    toMat (pPair k' r).1 = wordMat Amat r ∧ toMat (pPair k' r).2 = wordBlk Amat k' r := by
  induction r with
  | nil => exact ⟨toMat_pOne, toMat_pZero⟩
  | cons k r ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · show toMat (pMul (pPair k' r).1 (pLetter k)) = _
      rw [toMat_pMul, ih1, toMat_pLetter]
      rfl
    · show toMat (pAdd (pPair k' r).2 (if k' = k then (pPair k' r).1 else pZero)) =
        wordBlk Amat k' r + if k' = k then wordMat Amat r else 0
      rw [toMat_pAdd, ih2]
      congr 1
      split_ifs
      · exact ih1
      · exact toMat_pZero

theorem toMat_foldl (F : ℕ → List ℕ) (n : ℕ) :
    toMat ((List.range n).foldl (fun acc r => pAdd acc (F r)) pZero) =
      ∑ r ∈ Finset.range n, toMat (F r) := by
  induction n with
  | zero => simpa using toMat_pZero
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, toMat_pAdd, ih,
      Finset.sum_range_succ]

theorem relators_trivial (r : Fin 5) (j : ℕ) (hj : j < 11) :
    ((splitWordsF r).map letterOf).foldr act (2 ^ j) = 2 ^ j := by
  have h := chkRel_true
  unfold chkRel at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hw : splitWordsF r ∈ splitWords := by
    unfold splitWordsF
    rw [List.getD_eq_getElem _ _ (by simp [splitWords])]
    exact List.getElem_mem _
  exact h _ hw j hj

theorem toMat_dualRhs (k k' : Fin 6) :
    toMat (dualRhs k k') = (1 + Amat k) * splitPsi k' +
      ∑ r : Fin 5, splitCm k r * wordBlk Amat k' (splitWordsF r) := by
  unfold dualRhs
  rw [toMat_pAdd, toMat_pMul, toMat_pAdd, toMat_pOne, toMat_pLetter, toMat_foldl,
    Finset.sum_range]
  refine congrArg _ (Finset.sum_congr rfl (fun r _ => ?_))
  rw [toMat_pMul, (pPair_spec k' _).2]
  rfl

theorem dual_identity (k k' : Fin 6) :
    (if k = k' then (1 : Mat) else 0) = (1 + Amat k) * splitPsi k' +
      ∑ r : Fin 5, splitCm k r * wordBlk Amat k' (splitWordsF r) := by
  have h := chkDual_true
  unfold chkDual at h
  simp only [List.all_eq_true, List.mem_finRange, beq_iff_eq, forall_const] at h
  have h1 := congrArg toMat (h k k')
  have e1 : toMat (if k = k' then pOne else pZero) = if k = k' then (1 : Mat) else 0 := by
    by_cases hk : k = k'
    · simp [hk, toMat_pOne]
    · simp [hk, toMat_pZero]
  rw [e1, toMat_dualRhs] at h1
  exact h1

theorem letterOf_mem (k : Fin 6) : letterOf k ∈ letters := by
  fin_cases k <;> decide

end CFSG.EvenSporadicStandard.J4Std.DataSplit
