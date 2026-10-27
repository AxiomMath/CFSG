module

public import CFSG.F3.Spec
public import Certificates.Certificate12046

public section

namespace CFSG.LieType.Multipliers.F42

open CFSG.F3.Native CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem lifts_check :
    (List.range 48).all (liftOK lifts) = true :=
  Certificates.certificate12046.1

theorem pairs_check : pairsOK lifts = true :=
  Certificates.certificate12046.2.1

theorem words_check :
    (List.range 48).all (wordOK lifts) = true :=
  Certificates.certificate12046.2.2.1

theorem neg_check : negOK lifts 0 35 = true :=
  Certificates.certificate12046.2.2.2

@[expose] def Good (X : Array V) : Prop := X.size = 52 ∧ RowsWF X

theorem Good.mul {X Y : Array V} (hX : Good X) (hY : Good Y) : Good (mul 52 X Y) :=
  ⟨by unfold CFSG.F3.Native.mul; rw [Array.size_map]; exact hX.1, RowsWF.mul X 52 hX.2 hY.2⟩

theorem toMat_mul_of_good {X Y : Array V} (hX : Good X) (hY : Good Y) :
    toMat 52 (mul 52 X Y) = toMat 52 X * toMat 52 Y :=
  toMat_mul hX.1 hX.2 hY.2

theorem good_idM : Good (idM 52) := ⟨by simp [idM], RowsWF.idM 52⟩

theorem negM_getElem! {X : Array V} {i : ℕ} (hi : i < X.size) : (negM X)[i]! = X[i]!.neg := by
  unfold negM
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos X i hi]

theorem Good.negM {X : Array V} (hX : Good X) : Good (negM X) := by
  refine ⟨by rw [F42.negM, Array.size_map]; exact hX.1, fun j => ?_⟩
  by_cases hj : j < X.size
  · rw [negM_getElem! hj]
    exact V.wf_neg (hX.2 j)
  · rw [getElem!_neg _ j (by simpa [F42.negM] using hj)]
    exact V.wf_zero

theorem toMat_negM {X : Array V} (hX : Good X) : toMat 52 (negM X) = -toMat 52 X := by
  ext i j
  rw [toMat_apply, Matrix.neg_apply, toMat_apply, negM_getElem! (by rw [hX.1]; exact i.isLt),
    V.val_neg _ _ (hX.2 i)]

theorem toMat_eq_or_neg_of_eqPM {X Y : Array V} (hY : Good Y) (h : eqPM X Y = true) :
    toMat 52 X = toMat 52 Y ∨ toMat 52 X = -toMat 52 Y := by
  rw [eqPM, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (toMat_eq_of_eqM h)
  · exact Or.inr (by rw [toMat_eq_of_eqM h, toMat_negM hY])

theorem toMat_commute_of_commutes {X Y : Array V} (hX : Good X) (hY : Good Y)
    (h : commutes X Y = true) : toMat 52 X * toMat 52 Y = toMat 52 Y * toMat 52 X := by
  rw [← toMat_mul_of_good hX hY, ← toMat_mul_of_good hY hX]
  exact toMat_eq_of_eqM h

section Lifts


theorem liftOK_of_lt {k : ℕ} (hk : k < 48) : liftOK lifts k = true :=
  List.all_eq_true.1 lifts_check k (List.mem_range.2 hk)

theorem lift_facts {k : ℕ} (hk : k < 48) :
    Good (matOf lifts k) ∧ Good (invOf lifts k) ∧
      toMat 52 (matOf lifts k) * toMat 52 (invOf lifts k) = 1 ∧
      toMat 52 (invOf lifts k) * toMat 52 (matOf lifts k) = 1 ∧
      (toMat 52 (matOf lifts k) * toMat 52 (matOf lifts k) = 1 ∨
        toMat 52 (matOf lifts k) * toMat 52 (matOf lifts k) = -1) := by
  have h := liftOK_of_lt hk
  simp only [liftOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hM : Good (matOf lifts k) := ⟨h1, rowsWF_of_wfM h2⟩
  have hI : Good (invOf lifts k) := ⟨h3, rowsWF_of_wfM h4⟩
  refine ⟨hM, hI, ?_, ?_, ?_⟩
  · rw [← toMat_mul_of_good hM hI, toMat_eq_of_eqM h5, toMat_idM]
  · rw [← toMat_mul_of_good hI hM, toMat_eq_of_eqM h6, toMat_idM]
  · rw [← toMat_mul_of_good hM hM, ← toMat_idM 52]
    rcases toMat_eq_or_neg_of_eqPM good_idM h7 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, toMat_idM])

open _root_.Classical in
@[expose] noncomputable def liftGL (k : ℕ) : GL (Fin 52) (ZMod 3) :=
  if hk : k < 48 then
    ⟨toMat 52 (matOf lifts k), toMat 52 (invOf lifts k), (lift_facts hk).2.2.1,
      (lift_facts hk).2.2.2.1⟩
  else 1

theorem val_liftGL {k : ℕ} (hk : k < 48) :
    ((liftGL k : GL (Fin 52) (ZMod 3)) : Matrix (Fin 52) (Fin 52) (ZMod 3)) =
      toMat 52 (matOf lifts k) := by
  rw [liftGL, dite_eq_left hk, Units.val_mk]

theorem val_liftGL_inv {k : ℕ} (hk : k < 48) :
    (((liftGL k)⁻¹ : GL (Fin 52) (ZMod 3)) : Matrix (Fin 52) (Fin 52) (ZMod 3)) =
      toMat 52 (invOf lifts k) := by
  rw [liftGL, dite_eq_left hk, Units.inv_mk, Units.val_mk]

theorem liftGL_mul_self {k : ℕ} (hk : k < 48) :
    liftGL k * liftGL k = 1 ∨ liftGL k * liftGL k = -1 := by
  rcases (lift_facts hk).2.2.2.2 with h | h
  · exact Or.inl (Units.ext (by rw [Units.val_mul, val_liftGL hk, h, Units.val_one]))
  · refine Or.inr (Units.ext ?_)
    rw [Units.val_neg, Units.val_one, Units.val_mul, val_liftGL hk]
    exact h

theorem val_comm_liftGL {i j : ℕ} (hi : i < 48) (hj : j < 48) :
    ((⁅liftGL i, liftGL j⁆ : GL (Fin 52) (ZMod 3)) : Matrix (Fin 52) (Fin 52) (ZMod 3)) =
      toMat 52 (commArr lifts i j) := by
  obtain ⟨hMi, hIi, -⟩ := lift_facts hi
  obtain ⟨hMj, hIj, -⟩ := lift_facts hj
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, val_liftGL hi,
    val_liftGL hj, val_liftGL_inv hi, val_liftGL_inv hj, commArr,
    toMat_mul_of_good ((hMi.mul hMj).mul hIi) hIj, toMat_mul_of_good (hMi.mul hMj) hIi,
    toMat_mul_of_good hMi hMj]

open _root_.Classical in
@[expose] noncomputable def factorGL (c : Bool) (v : Fin Tag.F4.rank → ℤ) :
    GL (Fin 52) (ZMod 3) :=
  if (c && isRootB v) = true then liftGL (rootIdx v) else 1

theorem rootIdx_lt_of_isRootB {v : Fin Tag.F4.rank → ℤ} (h : isRootB v = true) :
    rootIdx v < 48 := by
  rw [isRootB, decide_eq_true_iff] at h
  exact (List.idxOf_lt_length_iff.2 h).trans_eq (by decide)

theorem factorGL_facts (c : Bool) (v : Fin Tag.F4.rank → ℤ) :
    Good (factor lifts c v) ∧
      ((factorGL c v : GL (Fin 52) (ZMod 3)) : Matrix (Fin 52) (Fin 52) (ZMod 3)) =
        toMat 52 (factor lifts c v) := by
  by_cases h : (c && isRootB v) = true
  · have hv : isRootB v = true := (Bool.and_eq_true _ _ ▸ h).2
    have hk := rootIdx_lt_of_isRootB hv
    rw [factorGL, ite_eq_left h, factor, ite_eq_left h, val_liftGL hk]
    exact ⟨(lift_facts hk).1, rfl⟩
  · rw [factorGL, ite_eq_right h, factor, ite_eq_right h, Units.val_one, toMat_idM]
    exact ⟨good_idM, rfl⟩

@[expose] noncomputable def fGL (i j : ℕ) : Fin 3 → GL (Fin 52) (ZMod 3)
  | 0 => factorGL (!isRootB (rootAt j - rootAt i)) (rootAt i + rootAt j)
  | 1 => factorGL true (rootAt i + 2 • rootAt j)
  | 2 => factorGL true (2 • rootAt i + rootAt j)

theorem val_prod_fGL (i j : ℕ) :
    ((fGL i j 0 * fGL i j 1 * fGL i j 2 : GL (Fin 52) (ZMod 3)) :
        Matrix (Fin 52) (Fin 52) (ZMod 3)) = toMat 52 (prodArr lifts i j) ∧
      Good (prodArr lifts i j) := by
  obtain ⟨g0, v0⟩ := factorGL_facts (!isRootB (rootAt j - rootAt i)) (rootAt i + rootAt j)
  obtain ⟨g1, v1⟩ := factorGL_facts true (rootAt i + 2 • rootAt j)
  obtain ⟨g2, v2⟩ := factorGL_facts true (2 • rootAt i + rootAt j)
  refine ⟨?_, (g0.mul g1).mul g2⟩
  rw [Units.val_mul, Units.val_mul]
  simp only [fGL]
  rw [v0, v1, v2, prodArr, f11, f12, f21, toMat_mul_of_good (g0.mul g1) g2,
    toMat_mul_of_good g0 g1]

theorem pairOK_of_lt {i j : ℕ} (hi : i < 48) (hj : j < 48) (hij : i ≠ j)
    (hs : rootAt i + rootAt j ≠ 0) : pairOK lifts i j = true := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 pairs_check i (List.mem_range.2 hi)) j
    (List.mem_range.2 hj)
  simpa [hij, hs] using h

theorem comm_liftGL {i j : ℕ} (hi : i < 48) (hj : j < 48) (hij : i ≠ j)
    (hs : rootAt i + rootAt j ≠ 0) :
    ⁅liftGL i, liftGL j⁆ = fGL i j 0 * fGL i j 1 * fGL i j 2 ∨
      ⁅liftGL i, liftGL j⁆ = -(fGL i j 0 * fGL i j 1 * fGL i j 2) := by
  have h := pairOK_of_lt hi hj hij hs
  simp only [pairOK, Bool.and_eq_true] at h
  obtain ⟨hv, hg⟩ := val_prod_fGL i j
  rcases toMat_eq_or_neg_of_eqPM hg h.1.1.1 with h' | h'
  · exact Or.inl (Units.ext (by rw [val_comm_liftGL hi hj, h', hv]))
  · exact Or.inr (Units.ext (by rw [Units.val_neg, hv, val_comm_liftGL hi hj]; exact h'))

theorem commute_fGL {i j : ℕ} (hi : i < 48) (hj : j < 48) (hij : i ≠ j)
    (hs : rootAt i + rootAt j ≠ 0) (a b : Fin 3) : Commute (fGL i j a) (fGL i j b) := by
  have h := pairOK_of_lt hi hj hij hs
  simp only [pairOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, h01⟩, h02⟩, h12⟩ := h
  obtain ⟨g0, v0⟩ := factorGL_facts (!isRootB (rootAt j - rootAt i)) (rootAt i + rootAt j)
  obtain ⟨g1, v1⟩ := factorGL_facts true (rootAt i + 2 • rootAt j)
  obtain ⟨g2, v2⟩ := factorGL_facts true (2 • rootAt i + rootAt j)
  have c01 : Commute (fGL i j 0) (fGL i j 1) := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    simp only [fGL]
    rw [v0, v1]
    exact toMat_commute_of_commutes g0 g1 h01)
  have c02 : Commute (fGL i j 0) (fGL i j 2) := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    simp only [fGL]
    rw [v0, v2]
    exact toMat_commute_of_commutes g0 g2 h02)
  have c12 : Commute (fGL i j 1) (fGL i j 2) := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    simp only [fGL]
    rw [v1, v2]
    exact toMat_commute_of_commutes g1 g2 h12)
  match a, b with
  | 0, 0 => exact Commute.refl _
  | 0, 1 => exact c01
  | 0, 2 => exact c02
  | 1, 0 => exact c01.symm
  | 1, 1 => exact Commute.refl _
  | 1, 2 => exact c12
  | 2, 0 => exact c02.symm
  | 2, 1 => exact c12.symm
  | 2, 2 => exact Commute.refl _

@[expose] def commPair (k : ℕ) : ℕ × ℕ := commPairs.getD k (0, 0)

theorem comm_liftGL_commPair {k : ℕ} (hk : k < 48) :
    (commPair k).1 < 48 ∧ (commPair k).2 < 48 ∧ (commPair k).1 ≠ (commPair k).2 ∧
      rootAt (commPair k).1 + rootAt (commPair k).2 ≠ 0 ∧
      rootAt (commPair k).1 + rootAt (commPair k).2 = rootAt k ∧
      isRootB (rootAt (commPair k).1 + 2 • rootAt (commPair k).2) = false ∧
      isRootB (2 • rootAt (commPair k).1 + rootAt (commPair k).2) = false ∧
      isRootB (rootAt (commPair k).2 - rootAt (commPair k).1) = false ∧
      ⁅liftGL (commPair k).1, liftGL (commPair k).2⁆ = liftGL k := by
  unfold commPair
  have h := List.all_eq_true.1 words_check k (List.mem_range.2 hk)
  simp only [wordOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, Units.ext ?_⟩
  rw [val_comm_liftGL h1 h2, val_liftGL hk]
  exact toMat_eq_of_eqM h9

theorem comm_liftGL_neg :
    rootAt 0 + rootAt 35 ≠ 0 ∧
      ⁅liftGL 0, liftGL 35⁆ = -(fGL 0 35 0 * fGL 0 35 1 * fGL 0 35 2) := by
  have h := neg_check
  simp only [negOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨-, h4⟩, h5⟩ := h
  refine ⟨h4, Units.ext ?_⟩
  obtain ⟨hv, hg⟩ := val_prod_fGL 0 35
  rw [Units.val_neg, hv, val_comm_liftGL (by norm_num) (by norm_num), toMat_eq_of_eqM h5]
  exact toMat_negM hg

end Lifts

end CFSG.LieType.Multipliers.F42
