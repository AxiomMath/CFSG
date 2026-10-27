module

public import Certificates.Data.Kernel.B45J2.Defs
public import CFSG.Certificates.Kernel.B45M12Sound
public import Certificates.Data.SmithB45J2Nor

public section

namespace CFSG.KC.B45J2

open CFSG.Quasithin CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.CharacterTheory.SteinbergBY
  FieldFour
open scoped Kronecker

theorem testBit_rowOf : ∀ (L : List ℕ) (i : ℕ),
    (rowOf L).testBit i = (L.getD (i / 60) 0).testBit (i % 60)
  | [], i => by simp [rowOf]
  | l :: ls, i => by
    rw [rowOf, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
    by_cases h : i < 60
    · rw [if_pos h, Nat.testBit_mod_two_pow, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      simp [h]
    · rw [if_neg h, testBit_rowOf ls]
      have h1 : i / 60 = (i - 60) / 60 + 1 := by omega
      have h2 : (i - 60) % 60 = i % 60 := by omega
      rw [h1, List.getD_cons_succ, h2]

theorem getD_rowsL (k : ℕ) : ∀ (m : ℕ) (L : List ℕ) (i : ℕ), i < m →
    (rowsL k m L).getD i 0 = rowOf ((L.drop (i * k)).take k)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, L, 0, _ => by simp [rowsL]
  | m + 1, L, i + 1, h => by
    rw [rowsL, List.getD_cons_succ, getD_rowsL k m (L.drop k) i (by omega), List.drop_drop]
    have e : k + i * k = (i + 1) * k := by rw [Nat.succ_mul, Nat.add_comm]
    rw [e]

theorem testBit_rowOf_take (L : List ℕ) {n j : ℕ} (hj : j < n) (a : ℕ) {b : ℕ} (hb : b < 2) :
    (rowOf ((L.drop a).take ((n + 29) / 30))).testBit (2 * j + b) =
      (L.getD (a + j / 30) 0).testBit (2 * (j % 30) + b) := by
  rw [testBit_rowOf]
  have h1 : (2 * j + b) / 60 = j / 30 := by omega
  have h2 : (2 * j + b) % 60 = 2 * (j % 30) + b := by omega
  have h3 : j / 30 < (n + 29) / 30 := by omega
  rw [h1, h2, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h3, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

theorem decF4L_eq (m n : ℕ) (L : List ℕ) :
    J2Mod.decF4L m n L = M12.decF4 m n (rowsL ((n + 29) / 30) m L) := by
  refine Vector.ext fun i hi => Vector.ext fun j hj => ?_
  simp only [J2Mod.decF4L, M12.decF4, J2Mod.limbEntry, Vector.getElem_ofFn, Vector.getElem_map,
    Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  rw [getD_rowsL _ _ _ _ hi]
  have e0 := testBit_rowOf_take L hj (i * ((n + 29) / 30)) (b := 0) (by omega)
  have e1 := testBit_rowOf_take L hj (i * ((n + 29) / 30)) (b := 1) (by omega)
  rw [Nat.add_zero, Nat.add_zero] at e0
  exact FieldFour.ext e0.symm e1.symm

theorem decVecF4L_eq (n : ℕ) (L : List ℕ) :
    J2Mod.decVecF4L n L = M12.decVecF4 n (rowOf (L.take ((n + 29) / 30))) := by
  refine Vector.ext fun j hj => ?_
  simp only [J2Mod.decVecF4L, M12.decVecF4, J2Mod.limbEntry, Vector.getElem_ofFn,
    Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  have e0 := testBit_rowOf_take L hj 0 (b := 0) (by omega)
  have e1 := testBit_rowOf_take L hj 0 (b := 1) (by omega)
  simp only [List.drop_zero, Nat.add_zero, Nat.zero_add] at e0 e1
  rw [Nat.zero_mul, Nat.zero_add]
  exact FieldFour.ext e0.symm e1.symm

theorem untab_decF4L (m n : ℕ) (L : List ℕ) :
    untab (J2Mod.decF4L m n L) = pairMat m n (colsL m n L) := by
  rw [decF4L_eq, untab_decF4_cols, colsL]

theorem untab_decF4J (m n : ℕ) (rows : List ℕ) :
    untab (J2Mod.decF4 m n rows) = pairMat m n (colsF4 n rows) :=
  untab_decF4_cols m n rows

theorem spinF4_eq (n : ℕ) (tw : List (List ℕ)) (tc : List ℕ) (Q Qi R Si Ti w : List ℕ)
    (spin dual : List (ℕ × ℕ)) :
    J2Mod.spinF4 n tw tc Q Qi R Si Ti w spin dual =
      M12.spinF4 n tw tc (rowsL ((n + 29) / 30) n Q) (rowsL ((n + 29) / 30) n Qi)
        (rowsL ((n + 29) / 30) n R) (rowsL ((n + 29) / 30) n Si) (rowsL ((n + 29) / 30) n Ti)
        (rowOf (w.take ((n + 29) / 30))) spin dual := by
  simp only [J2Mod.spinF4, M12.spinF4, decF4L_eq, decVecF4L_eq]
  rfl

theorem norL_sound {n : ℕ} [NeZero n] {tw : List (List ℕ)} {tc : List ℕ}
    {Q Qi R Si Ti w : List ℕ} {spin dual : List (ℕ × ℕ)} {Ga Gb : List (ℕ × ℕ)}
    {Ma Mb : Vector (Vector FieldFour n) n} (ha : untab Ma = pairMat n n Ga)
    (hb : untab Mb = pairMat n n Gb) (h : norL n tw tc Q Qi R Si Ti w spin dual Ga Gb = true) :
    (J2Mod.spinF4 n tw tc Q Qi R Si Ti w spin dual).check Ma Mb = true := by
  rw [spinF4_eq]
  exact norF4_sound ha hb h

theorem getD_shiftsF4 (n : ℕ) : ∀ (k p q l : ℕ), l < k →
    (shiftsF4 n k (p, q)).getD l (0, 0) = (p * 2 ^ (n * l), q * 2 ^ (n * l))
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, p, q, 0, _ => by simp [shiftsF4]
  | k + 1, p, q, l + 1, h => by
    rw [shiftsF4, List.getD_cons_succ, getD_shiftsF4 n k _ _ l (by omega)]
    congr 1 <;> ring

theorem length_shiftsF4 (n : ℕ) : ∀ (k : ℕ) (c : ℕ × ℕ), (shiftsF4 n k c).length = k
  | 0, _ => rfl
  | k + 1, c => by rw [shiftsF4, List.length_cons, length_shiftsF4 n k]

theorem getD_kronF4 (m n : ℕ) (B : List (ℕ × ℕ)) (hB : B.length = n) :
    ∀ (A : List (ℕ × ℕ)) (a b : ℕ), a < A.length → b < n →
      (kronF4 m n A B).getD (b + n * a) (0, 0) =
        actF4 (shiftsF4 n m ((B.getD b (0, 0)).1 % 2 ^ n, (B.getD b (0, 0)).2 % 2 ^ n))
          (A.getD a (0, 0))
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | x :: A, 0, b, _, hb => by
    have hb' : b < B.length := hB ▸ hb
    rw [kronF4, List.flatMap_cons, List.getD_eq_getElem?_getD, Nat.mul_zero, Nat.add_zero,
      List.getElem?_append_left (by rw [List.length_map]; exact hb'), List.getElem?_map,
      List.getD_cons_zero, List.getD_eq_getElem?_getD (l := B), List.getElem?_eq_getElem hb']
    rfl
  | x :: A, a + 1, b, h, hb => by
    have e := getD_kronF4 m n B hB A a b (Nat.lt_of_succ_lt_succ h) hb
    rw [kronF4] at e
    have hle : (B.map fun y => actF4 (shiftsF4 n m (y.1 % 2 ^ n, y.2 % 2 ^ n)) x).length ≤
        b + n * (a + 1) := by
      rw [List.length_map, hB, Nat.mul_add_one, ← Nat.add_assoc]
      exact Nat.le_add_left n _
    have e2 : b + n * (a + 1) - n = b + n * a := by
      rw [Nat.mul_add_one, ← Nat.add_assoc, Nat.add_sub_cancel]
    rw [kronF4, List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right hle,
      List.length_map, hB, List.getD_cons_succ, ← e, List.getD_eq_getElem?_getD, e2]

theorem testBit_shift {n j i l : ℕ} (hj : j < n) (x : ℕ) :
    ((x % 2 ^ n) * 2 ^ (n * l)).testBit (j + n * i) = (decide (l = i) && x.testBit j) := by
  rw [Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow]
  rcases Nat.lt_trichotomy l i with hl | rfl | hl
  · have h3 : n * l + n ≤ n * i := by
      rw [← Nat.mul_add_one]
      exact Nat.mul_le_mul_left n hl
    have h4 : ¬ (j + n * i - n * l < n) := by
      generalize n * l = p at h3 ⊢
      generalize n * i = q at h3 ⊢
      omega
    simp [h4, hl.ne]
  · simp [hj]
  · have h3 : n * i + n ≤ n * l := by
      rw [← Nat.mul_add_one]
      exact Nat.mul_le_mul_left n hl
    have h4 : ¬ (n * l ≤ j + n * i) := by
      generalize n * l = p at h3 ⊢
      generalize n * i = q at h3 ⊢
      omega
    simp [h4, hl.ne']

theorem pent_shift {n j i l : ℕ} (hj : j < n) (y : ℕ × ℕ) :
    pent ((y.1 % 2 ^ n) * 2 ^ (n * l), (y.2 % 2 ^ n) * 2 ^ (n * l)) (j + n * i) =
      if l = i then pent y j else 0 := by
  split_ifs with h
  · exact FieldFour.ext ((testBit_shift hj y.1).trans (by simp [h, pent]))
      ((testBit_shift hj y.2).trans (by simp [h, pent]))
  · rw [← pent_zero (j + n * i)]
    exact FieldFour.ext ((testBit_shift hj y.1).trans (by simp [h, pent]))
      ((testBit_shift hj y.2).trans (by simp [h, pent]))

theorem pairMat_kronF4 {m n : ℕ} {A B : List (ℕ × ℕ)} (hA : A.length = m) (hB : B.length = n) :
    pairMat (m * n) (m * n) (kronF4 m n A B) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (pairMat m m A ⊗ₖ pairMat n n B) := by
  refine Matrix.ext fun r c => ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective r
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective c
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.kroneckerMap_apply]
  simp only [pairMat, Matrix.of_apply, finProdFinEquiv_apply_val]
  have ha : (a : ℕ) < A.length := by
    rw [hA]
    exact a.2
  rw [getD_kronF4 m n B hB A a b ha b.2, pent_actF4, length_shiftsF4]
  rw [Finset.sum_eq_single (i : ℕ)]
  · rw [getD_shiftsF4 n m _ _ i i.2, pent_shift j.2, if_pos rfl]
  · intro l hl hli
    rw [getD_shiftsF4 n m _ _ l (Finset.mem_range.1 hl), pent_shift j.2, if_neg hli, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 i.2) h

theorem untab_wordT_eq {n : ℕ} {Ma Mb : Vector (Vector FieldFour n) n} {Ga Gb : List (ℕ × ℕ)}
    (ha : untab Ma = pairMat n n Ga) (hb : untab Mb = pairMat n n Gb) (hla : Ga.length ≤ n)
    (hlb : Gb.length ≤ n) :
    ∀ w : List Bool, untab (B45Mat.wordT Ma Mb w) = pairMat n n (wordF4 n Ga Gb w)
  | [] => by rw [B45Mat.wordT, untab_idT, wordF4, pairMat_idF4]
  | [z] => by cases z <;> simp [B45Mat.wordT, wordF4, genT, ha, hb]
  | z :: y :: w => by
    rw [B45Mat.wordT, untab_mulT, untab_wordT_eq ha hb hla hlb (y :: w), wordF4]
    cases z
    · rw [pairMat_mulF4 (k := n) _ _ hla]
      simp [genT, ha]
    · rw [pairMat_mulF4 (k := n) _ _ hlb]
      simp [genT, hb]

theorem subKF4_spec {m d : ℕ} {B P : List (ℕ × ℕ)} {KT : List (List (ℕ × ℕ) × List (ℕ × ℕ))}
    (h : subKF4 m d B P KT = true) :
    pairMat d m P * pairMat m d B = 1 ∧
      ∀ K T, (K, T) ∈ KT → K.length ≤ m ∧ T.length = d ∧
        pairMat d d T = pairMat d m P * (pairMat m m K * pairMat m d B) ∧
        pairMat m m K * pairMat m d B = pairMat m d B * (pairMat d m P * (pairMat m m K *
          pairMat m d B)) := by
  simp only [subKF4, pinF4, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hBl, hPl⟩, hPB⟩, hKT⟩ := h
  refine ⟨?_, fun K T hm => ?_⟩
  · rw [← pairMat_mulF4 _ _ hPl, pairMat_eq_of_eqF4 hPB, pairMat_idF4]
  obtain ⟨⟨hKl, hTl⟩, hT, hKB⟩ := hKT (K, T) hm
  have hT' : pairMat d d T = pairMat d m P * (pairMat m m K * pairMat m d B) := by
    rw [← pairMat_mulF4 _ _ hKl, ← pairMat_mulF4 _ _ hPl]
    exact (pairMat_eq_of_eqF4 hT).symm
  refine ⟨hKl, hTl, hT', ?_⟩
  rw [← hT', ← pairMat_mulF4 _ _ hKl, ← pairMat_mulF4 _ _ hBl]
  exact pairMat_eq_of_eqF4 hKB

theorem subOK_of_subKF4 {m d : ℕ} {Ka Kb : Vector (Vector FieldFour m) m}
    {B : Vector (Vector FieldFour d) m} {P : Vector (Vector FieldFour m) d}
    {Ka' Kb' B' P' Ta Tb : List (ℕ × ℕ)} {KT : List (List (ℕ × ℕ) × List (ℕ × ℕ))}
    (hKa : untab Ka = pairMat m m Ka') (hKb : untab Kb = pairMat m m Kb')
    (hB : untab B = pairMat m d B') (hP : untab P = pairMat d m P')
    (h : subKF4 m d B' P' KT = true) (ha : (Ka', Ta) ∈ KT) (hb : (Kb', Tb) ∈ KT) :
    subOK Ka Kb B P = true := by
  obtain ⟨hPB, hKT⟩ := subKF4_spec h
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [untab_mulT, hP, hB, hPB]
  · simp only [untab_mulT, hKa, hB, hP]
    exact (hKT _ _ ha).2.2.2
  · simp only [untab_mulT, hKb, hB, hP]
    exact (hKT _ _ hb).2.2.2

end CFSG.KC.B45J2

end
