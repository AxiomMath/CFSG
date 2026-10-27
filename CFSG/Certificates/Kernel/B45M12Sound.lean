module

public import Certificates.Data.Kernel.B45M12.Four
public import Certificates.Data.SmithB45MatM12Nor

public section

namespace CFSG.KC.B45M12

open CFSG.Quasithin.H.Mathieu (actM)
open CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12 CFSG.CharacterTheory.SteinbergBY FieldFour
open CFSG.Monster.Code (bvec bvec_zero bvec_xor)
open scoped Matrix

theorem testBit_eq_decide (c i : ℕ) : c.testBit i = decide (c / 2 ^ i % 2 = 1) := by
  rw [← Nat.testBit_zero, Nat.testBit_div_two_pow, Nat.zero_add]

theorem testBit_bit_zero {r b : ℕ} (hb : b < 2) : (2 * r + b).testBit 0 = decide (b = 1) := by
  rw [Nat.testBit_zero, decide_eq_decide]
  omega

theorem testBit_bit_succ {r b : ℕ} (hb : b < 2) (j : ℕ) :
    (2 * r + b).testBit (j + 1) = r.testBit j := by
  rw [Nat.testBit_add_one]
  congr 1
  omega

theorem testBit_bit_zero' {r b : ℕ} (hb : b < 2) : (b + 2 * r).testBit 0 = decide (b = 1) := by
  rw [Nat.add_comm]
  exact testBit_bit_zero hb

theorem testBit_bit_succ' {r b : ℕ} (hb : b < 2) (j : ℕ) :
    (b + 2 * r).testBit (j + 1) = r.testBit j := by
  rw [Nat.add_comm]
  exact testBit_bit_succ hb j

theorem beq_mod_two (x : ℕ) : Nat.beq (x % 2) 1 = x.testBit 0 := by
  rw [Nat.testBit_zero]
  exact Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, decide_eq_true_eq])

theorem testBit_mod_two_zero (c i : ℕ) : (c / 2 ^ i % 2).testBit 0 = c.testBit i := by
  rw [Nat.testBit_zero, Nat.mod_mod, testBit_eq_decide]

theorem eq_of_eqL : ∀ {X Y : List ℕ}, eqL X Y = true → X = Y
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, eq_of_eqL h.2]

theorem getD_mod_of_eqM {m : ℕ} : ∀ {X Y : List ℕ}, eqM m X Y = true →
    ∀ j, X.getD j 0 % 2 ^ m = Y.getD j 0 % 2 ^ m
  | [], Y, h, j => by
    simp only [eqM, List.all_eq_true, Nat.beq_eq] at h
    rw [List.getD_nil]
    by_cases hj : j < Y.length
    · rw [List.getD_eq_getElem _ _ hj, h _ (List.getElem_mem hj), Nat.zero_mod]
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hj)]
  | x :: xs, Y, h, j => by
    simp only [eqM, Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero => cases Y <;> simpa using h.1
    | succ j =>
      have := getD_mod_of_eqM h.2 j
      cases Y <;> simpa using this

theorem maskMat_eq_of_eqM {m n : ℕ} {X Y : List ℕ} (h : eqM m X Y = true) :
    maskMat m n X = maskMat m n Y := by
  refine Matrix.ext fun i j => ?_
  have h1 := congrArg (fun x => x.testBit i) (getD_mod_of_eqM h j)
  simp only [Nat.testBit_mod_two_pow, i.2, decide_true, Bool.true_and] at h1
  rw [maskMat_apply, maskMat_apply, h1]

theorem length_trStep : ∀ (rs : List ℕ) (c : ℕ), (trStep rs c).length = rs.length
  | [], _ => rfl
  | _ :: rs, c => by rw [trStep, List.length_cons, List.length_cons, length_trStep rs]

theorem getD_trStep : ∀ (rs : List ℕ) (c : ℕ) {i : ℕ}, i < rs.length →
    (trStep rs c).getD i 0 = 2 * rs.getD i 0 + c / 2 ^ i % 2
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | r :: rs, c, 0, _ => by simp [trStep, List.getD_cons_zero]
  | r :: rs, c, i + 1, h => by
    rw [trStep, List.getD_cons_succ, List.getD_cons_succ,
      getD_trStep rs (c / 2) (by simpa using h), Nat.div_div_eq_div_mul, Nat.pow_succ',
      Nat.mul_comm 2]

theorem length_trM (m : ℕ) : ∀ X : List ℕ, (trM m X).length = m
  | [] => List.length_replicate ..
  | c :: X => by
    change (trStep (trM m X) c).length = m
    rw [length_trStep, length_trM m X]

theorem testBit_trM (m : ℕ) : ∀ (X : List ℕ) {i : ℕ}, i < m → ∀ j,
    ((trM m X).getD i 0).testBit j = (X.getD j 0).testBit i
  | [], i, hi, j => by
    change ((List.replicate m 0).getD i 0).testBit j = _
    simp
  | c :: X, i, hi, j => by
    change ((trStep (trM m X) c).getD i 0).testBit j = _
    rw [getD_trStep _ _ (by rw [length_trM]; exact hi)]
    cases j with
    | zero =>
      rw [testBit_bit_zero (Nat.mod_lt _ (by norm_num)), List.getD_cons_zero, testBit_eq_decide]
    | succ j =>
      rw [testBit_bit_succ (Nat.mod_lt _ (by norm_num)), List.getD_cons_succ, testBit_trM m X hi j]

theorem maskMat_trM (m n : ℕ) (X : List ℕ) : maskMat n m (trM m X) = (maskMat m n X).transpose := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.transpose_apply, maskMat_apply, maskMat_apply, testBit_trM m X j.2]

theorem untab_decF2 (m n : ℕ) (rows : List ℕ) :
    untab (decF2 m n rows) = (maskMat n m rows).transpose := by
  refine Matrix.ext fun i j => ?_
  simp [untab, decF2, maskMat_apply]

theorem decVecF2_eq (n w : ℕ) : (fun j : Fin n => (decVecF2 n w)[j]) = bvec n w := by
  funext j
  simp [decVecF2, bvec]

theorem testBit_col0 : ∀ (Q : List ℕ) (l : ℕ), (col0 Q).testBit l = (Q.getD l 0).testBit 0
  | [], l => by simp [col0]
  | r :: Q, 0 => by
    change (r % 2 + 2 * col0 Q).testBit 0 = _
    rw [testBit_bit_zero' (Nat.mod_lt _ (by norm_num)), List.getD_cons_zero, Nat.testBit_zero]
  | r :: Q, l + 1 => by
    change (r % 2 + 2 * col0 Q).testBit (l + 1) = _
    rw [testBit_bit_succ' (Nat.mod_lt _ (by norm_num)), List.getD_cons_succ, testBit_col0 Q l]

theorem col0_eq (n : ℕ) [NeZero n] (Q : List ℕ) :
    (fun l : Fin n => (decF2 n n Q)[l][(0 : Fin n)]) = bvec n (col0 Q) := by
  funext l
  simp [decF2, bvec, testBit_col0]

theorem subK_spec {m d : ℕ} {B P : List ℕ} {KT : List (List ℕ × List ℕ)}
    (h : subK m d B P KT = true) :
    B.length ≤ d ∧ P.length ≤ m ∧ maskMat d d (mulM P B) = 1 ∧ ∀ K T, (K, T) ∈ KT →
      K.length ≤ m ∧ T = mulM P (mulM K B) ∧
        maskMat m d (mulM K B) = maskMat m d (mulM B T) := by
  simp only [subK, subStep, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hB, hP⟩, hPB⟩, hKT⟩ := h
  refine ⟨hB, hP, by rw [maskMat_eq_of_eqM hPB, maskMat_idM], fun K T hKT' => ?_⟩
  obtain ⟨hK, hT, hKB⟩ := hKT _ hKT'
  exact ⟨hK, (eq_of_eqL hT).symm, maskMat_eq_of_eqM hKB⟩

theorem subOKM_of_subK {m d : ℕ} {B P Ka Kb Ta Tb : List ℕ} {KT₁ KT₂ : List (List ℕ × List ℕ)}
    (h₁ : subK m d B P KT₁ = true) (h₂ : subK m d B P KT₂ = true) (ha : (Ka, Ta) ∈ KT₁)
    (hb : (Kb, Tb) ∈ KT₂) : subOKM m d Ka Kb B P = true := by
  obtain ⟨hB, hP, hPB, h₁⟩ := subK_spec h₁
  obtain ⟨-, -, -, h₂⟩ := subK_spec h₂
  obtain ⟨hKa, rfl, hKBa⟩ := h₁ _ _ ha
  obtain ⟨hKb, rfl, hKBb⟩ := h₂ _ _ hb
  simp only [subOKM, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true]
  exact ⟨⟨⟨⟨⟨hKa, hKb⟩, hB⟩, hP⟩, hPB⟩, hKBa, hKBb⟩

theorem quotK_spec {m d : ℕ} {B P : List ℕ} {KT : List (List ℕ × List ℕ)}
    (h : quotK m d B P KT = true) :
    B.length ≤ d ∧ P.length ≤ m ∧ maskMat d d (mulM P B) = 1 ∧ ∀ K T, (K, T) ∈ KT →
      K.length ≤ m ∧ T = mulM P (mulM K B) ∧
        maskMat d m (mulM P K) = maskMat d m (mulM (mulM (mulM P K) B) P) := by
  simp only [quotK, quotStep, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hB, hP⟩, hPB⟩, hKT⟩ := h
  refine ⟨hB, hP, by rw [maskMat_eq_of_eqM hPB, maskMat_idM], fun K T hKT' => ?_⟩
  obtain ⟨hK, hT, hPK⟩ := hKT _ hKT'
  exact ⟨hK, (eq_of_eqL hT).symm, maskMat_eq_of_eqM hPK⟩

theorem quotOKM_of_quotK {m d : ℕ} {B P Ka Kb Ta Tb : List ℕ}
    {KT₁ KT₂ : List (List ℕ × List ℕ)} (h₁ : quotK m d B P KT₁ = true)
    (h₂ : quotK m d B P KT₂ = true) (ha : (Ka, Ta) ∈ KT₁) (hb : (Kb, Tb) ∈ KT₂) :
    quotOKM m d Ka Kb B P = true := by
  obtain ⟨hB, hP, hPB, h₁⟩ := quotK_spec h₁
  obtain ⟨-, -, -, h₂⟩ := quotK_spec h₂
  obtain ⟨hKa, -, hPKa⟩ := h₁ _ _ ha
  obtain ⟨hKb, -, hPKb⟩ := h₂ _ _ hb
  simp only [quotOKM, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true]
  exact ⟨⟨⟨⟨⟨hKa, hKb⟩, hB⟩, hP⟩, hPB⟩, hPKa, hPKb⟩

section Coded

variable {F : Type*} [Field F] {α : Type}

def colMat {m : ℕ} (dec : α → Fin m → F) (d₀ : α) (n : ℕ) (X : List α) :
    Matrix (Fin m) (Fin n) F :=
  Matrix.of fun i j => dec (X.getD j d₀) i

theorem colMat_map {β : Type} {m k n : ℕ} {dec : α → Fin m → F} {d₀ : α}
    {dec' : β → Fin k → F} {d₀' : β} (h₀ : dec d₀ = 0) (h₀' : dec' d₀' = 0)
    {M : Matrix (Fin m) (Fin k) F} {f : β → α} (hf : ∀ x, dec (f x) = M *ᵥ dec' x)
    (X : List β) : colMat dec d₀ n (X.map f) = M * colMat dec' d₀' n X := by
  refine Matrix.ext fun i j => ?_
  have e : dec ((X.map f).getD j d₀) = M *ᵥ dec' (X.getD j d₀') := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases X[(j : ℕ)]? with
    | none =>
      change dec d₀ = M *ᵥ dec' d₀'
      rw [h₀, h₀', Matrix.mulVec_zero]
    | some x => exact hf x
  exact congrFun e i

theorem colMat_diag0 {n : ℕ} [NeZero n] {dec : α → Fin n → F} {d₀ : α} (h₀ : dec d₀ = 0)
    {L : List α} (hL : colMat dec d₀ n L = 1) :
    colMat dec d₀ n (d₀ :: L.tail) = Matrix.diagonal fun j : Fin n => if j = 0 then 0 else 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases hj0 : j = 0
  · subst hj0
    change dec ((d₀ :: L.tail).getD ((0 : Fin n) : ℕ) d₀) i = _
    rw [Fin.val_zero, List.getD_cons_zero, h₀, Matrix.diagonal_apply]
    simp
  · obtain ⟨j', hj'⟩ : ∃ j', (j : ℕ) = j' + 1 :=
      Nat.exists_eq_succ_of_ne_zero fun h => hj0 (Fin.ext (by rw [h, Fin.val_zero]))
    have e : (d₀ :: L.tail).getD j d₀ = L.getD j d₀ := by
      rw [hj', List.getD_cons_succ]
      cases L <;> simp
    change dec ((d₀ :: L.tail).getD j d₀) i = _
    rw [e]
    change colMat dec d₀ n L i j = _
    rw [hL]
    by_cases hij : i = j
    · subst hij
      simp [hj0]
    · simp [hij]

theorem untab_wordT_cons {n : ℕ} (Ma Mb : Vector (Vector F n) n) (z : Bool) (w : List Bool) :
    untab (CFSG.Quasithin.B45Mat.wordT Ma Mb (z :: w)) =
      untab (genT Ma Mb z) * untab (CFSG.Quasithin.B45Mat.wordT Ma Mb w) := by
  cases w with
  | nil => rw [CFSG.Quasithin.B45Mat.wordT.eq_2, CFSG.Quasithin.B45Mat.wordT.eq_1, untab_idT, mul_one]
  | cons y w => rw [CFSG.Quasithin.B45Mat.wordT.eq_3, untab_mulT]

theorem dec_foldl_word {n : ℕ} (dec : α → Fin n → F) (step : ℕ → α → α)
    (Ma Mb : Vector (Vector F n) n)
    (hstep : ∀ z x, dec (step z x) = (untab (genT Ma Mb (z == 2)))ᵀ *ᵥ dec x) :
    ∀ (W : List ℕ) (y : α), dec (W.foldl (fun acc z => step z acc) y) =
      (untab (CFSG.Quasithin.B45Mat.wordT Ma Mb (boolWord W)))ᵀ *ᵥ dec y
  | [], y => by
    change dec y = (untab (CFSG.Quasithin.B45Mat.wordT Ma Mb []))ᵀ *ᵥ dec y
    rw [CFSG.Quasithin.B45Mat.wordT.eq_1, untab_idT, Matrix.transpose_one, Matrix.one_mulVec]
  | z :: W, y => by
    change dec (W.foldl (fun acc z => step z acc) (step z y)) =
      (untab (CFSG.Quasithin.B45Mat.wordT Ma Mb ((z == 2) :: boolWord W)))ᵀ *ᵥ dec y
    rw [dec_foldl_word dec step Ma Mb hstep W (step z y), hstep, Matrix.mulVec_mulVec,
      ← Matrix.transpose_mul, ← untab_wordT_cons]

theorem getD_reverse_of_lt {β : Type} (l : List β) (d d' : β) {i : ℕ} (h : i < l.length) :
    l.reverse.getD i d = l.getD (l.length - 1 - i) d' := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by omega),
    List.getElem_reverse]

theorem spinR_spec {n : ℕ} (dec : α → Fin n → F) (f : ℕ → α → α)
    (g : Bool → Vector F n → Vector F n) (v : α) (u : Vector F n) (hv : dec v = fun i => u[i])
    (hfg : ∀ z x (y : Vector F n), dec x = (fun i => y[i]) →
      dec (f z x) = fun i => (g (z == 2) y)[i]) :
    ∀ (prog : List (ℕ × ℕ)) (k : ℕ) (acc : List α) (arr : Array (Vector F n)),
      acc.length = k → arr.size = k →
      (∀ i < k, dec (acc.getD (k - 1 - i) v) = fun j => (arr.getD i u)[j]) →
      (spinR f v prog k acc).length = k + prog.length ∧
      (prog.foldl (fun a e => a.push (g (e.2 == 2) (a.getD e.1 u))) arr).size =
        k + prog.length ∧
      ∀ i < k + prog.length, dec ((spinR f v prog k acc).getD (k + prog.length - 1 - i) v) =
        fun j => ((prog.foldl (fun a e => a.push (g (e.2 == 2) (a.getD e.1 u))) arr).getD i u)[j]
  | [], k, acc, arr, hl, hs, h => by
    simp only [spinR, List.foldl_nil, List.length_nil, Nat.add_zero]
    exact ⟨hl, hs, h⟩
  | e :: es, k, acc, arr, hl, hs, h => by
    have hx : dec (if e.1 < k then acc.getD (k - 1 - e.1) v else v) =
        fun j => (arr.getD e.1 u)[j] := by
      split_ifs with he
      · exact h _ he
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
        exact hv
    obtain ⟨h1, h2, h3⟩ := spinR_spec dec f g v u hv hfg es (k + 1)
      (f e.2 (if e.1 < k then acc.getD (k - 1 - e.1) v else v) :: acc)
      (arr.push (g (e.2 == 2) (arr.getD e.1 u))) (by rw [List.length_cons, hl])
      (by rw [Array.size_push, hs]) (by
        intro i hi
        rw [getD_push, hs]
        by_cases hik : i = k
        · rw [if_pos hik, hik, Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero]
          exact hfg _ _ _ hx
        · rw [if_neg hik]
          have e' : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
          rw [e', List.getD_cons_succ]
          exact h i (by omega))
    have e1 : k + (e :: es).length = k + 1 + es.length := by
      rw [List.length_cons]
      omega
    rw [e1]
    exact ⟨h1, h2, h3⟩

theorem colMat_spin {n : ℕ} (dec : α → Fin n → F) (d₀ : α) (f : ℕ → α → α)
    (g : Bool → Vector F n → Vector F n) (v : α) (u : Vector F n) (hv : dec v = fun i => u[i])
    (hfg : ∀ z x (y : Vector F n), dec x = (fun i => y[i]) →
      dec (f z x) = fun i => (g (z == 2) y)[i])
    (prog : List (ℕ × ℕ)) (hn : prog.length + 1 = n) :
    (spinR f v prog 1 [v]).reverse.length = n ∧
    ∀ i j : Fin n, colMat dec d₀ n (spinR f v prog 1 [v]).reverse i j =
      ((prog.foldl (fun a e => a.push (g (e.2 == 2) (a.getD e.1 u))) #[u]).getD j u)[i] := by
  obtain ⟨h1, -, h3⟩ := spinR_spec dec f g v u hv hfg prog 1 [v] #[u] rfl rfl fun i hi => by
    obtain rfl : i = 0 := by omega
    exact hv
  refine ⟨by rw [List.length_reverse, h1]; omega, fun i j => ?_⟩
  have hj : (j : ℕ) < (spinR f v prog 1 [v]).length := by rw [h1]; omega
  have := congrFun (h3 j (by omega)) i
  change dec ((spinR f v prog 1 [v]).reverse.getD j d₀) i = _
  rw [getD_reverse_of_lt _ d₀ v hj, h1]
  exact this

theorem untab_colTab_apply {n : ℕ} (vs : Array (Vector F n)) (u : Vector F n) (i j : Fin n) :
    untab (colTab vs u) i j = (vs.getD j u)[i] := by
  simp [colTab, untab]

theorem untab_rowTab_apply {n : ℕ} (ws : Array (Vector F n)) (u : Vector F n) (i j : Fin n) :
    untab (rowTab ws u) i j = (ws.getD i u)[j] := by
  simp [rowTab, untab]

theorem beq_two_eq (z : ℕ) : Nat.beq z 2 = (z == 2) :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq])

theorem untab_sumTerms_cons {n : ℕ} (q : F × Vector (Vector F n) n)
    (l : List (F × Vector (Vector F n) n)) :
    untab (sumTerms (q :: l)) = q.1 • untab q.2 + untab (sumTerms l) := by
  simp only [sumTerms, untab_tab, List.map_cons, List.sum_cons]

theorem untab_sumTerms_nil {n : ℕ} : untab (sumTerms ([] : List (F × Vector (Vector F n) n))) = 0 := by
  simp only [sumTerms, untab_tab, List.map_nil, List.sum_nil]

end Coded

theorem maskMat_map {m k n : ℕ} {M : Matrix (Fin m) (Fin k) (ZMod 2)} {f : ℕ → ℕ}
    (hf : ∀ x, bvec m (f x) = M *ᵥ bvec k x) (X : List ℕ) :
    maskMat m n (X.map f) = M * maskMat k n X :=
  colMat_map (bvec_zero m) (bvec_zero k) hf X

theorem maskMat_diag0 (n : ℕ) [NeZero n] :
    maskMat n n (diag0 n) = Matrix.diagonal fun j : Fin n => if j = 0 then 0 else 1 :=
  colMat_diag0 (dec := bvec n) (d₀ := 0) (bvec_zero n) (maskMat_idM n)

theorem bvec_actM_mulVec {n : ℕ} (A : List ℕ) (hA : A.length ≤ n) (x : ℕ) :
    bvec n (actM A x) = maskMat n n A *ᵥ bvec n x := by
  funext i
  exact congrFun (congrFun (maskMat_mulM (m := n) (n := 1) A [x] hA) i) 0

theorem genM_eq (Ga Gb : List ℕ) (z : ℕ) : genM Ga Gb z = if (z == 2) = true then Gb else Ga := by
  rw [genM, beq_two_eq]
  cases z == 2 <;> rfl

theorem bvec_sumT {n : ℕ} {Ma Mb : Vector (Vector (ZMod 2) n) n} {Ha Hb : List ℕ}
    (hw : ∀ (W : List ℕ) y, bvec n (wordT Ha Hb W y) =
      (untab (CFSG.Quasithin.B45Mat.wordT Ma Mb (boolWord W)))ᵀ *ᵥ bvec n y) :
    ∀ (L : List (List ℕ × ℕ)) (y : ℕ), bvec n (sumT Ha Hb L y) =
      (untab (sumTerms ((L.map fun p => (boolWord p.1, (p.2 : ZMod 2))).map
        fun t => (t.2, CFSG.Quasithin.B45Mat.wordT Ma Mb t.1))))ᵀ *ᵥ bvec n y
  | [], y => by
    change bvec n 0 = _
    rw [List.map_nil, List.map_nil, untab_sumTerms_nil, Matrix.transpose_zero, Matrix.zero_mulVec,
      bvec_zero]
  | t :: L, y => by
    change bvec n ((if t.2 % 2 = 1 then wordT Ha Hb t.1 y else 0) ^^^ sumT Ha Hb L y) = _
    simp only [List.map_cons, untab_sumTerms_cons, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.add_mulVec, Matrix.smul_mulVec]
    rw [bvec_xor, bvec_sumT hw L y]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one t.2 with h | h
    · have hc : (t.2 : ZMod 2) = 0 := by rw [← ZMod.natCast_mod, h, Nat.cast_zero]
      rw [if_neg (by omega), bvec_zero, hc, zero_smul]
    · have hc : (t.2 : ZMod 2) = 1 := by rw [← ZMod.natCast_mod, h, Nat.cast_one]
      rw [if_pos h, hw, hc, one_smul]

theorem maskMat_spinM {n : ℕ} {Ma Mb : Vector (Vector (ZMod 2) n) n} {Ga Gb : List ℕ}
    (hact : ∀ z x, bvec n (actM (genM Ga Gb z) x) = untab (genT Ma Mb (z == 2)) *ᵥ bvec n x)
    {x₀ : ℕ} {u : Vector (ZMod 2) n} (hu : bvec n x₀ = fun i => u[i]) {prog : List (ℕ × ℕ)}
    (hn : prog.length + 1 = n) :
    (spinM Ga Gb x₀ prog).length = n ∧
      maskMat n n (spinM Ga Gb x₀ prog) = untab (colTab (spinVecs Ma Mb u (boolProg prog)) u) := by
  obtain ⟨h1, h2⟩ := colMat_spin (bvec n) 0 (fun z x => actM (genM Ga Gb z) x)
    (fun b y => mulVecT (genT Ma Mb b) y) x₀ u hu (fun z x y hxy =>
      (by rw [mulVecT_spec, ← hxy]; exact hact z x :
        bvec n (actM (genM Ga Gb z) x) = fun i => (mulVecT (genT Ma Mb (z == 2)) y)[i])) prog hn
  refine ⟨h1, Matrix.ext fun i j => ?_⟩
  rw [untab_colTab_apply, spinVecs, boolProg, List.foldl_map]
  exact h2 i j

theorem maskMat_spinM_dual {n : ℕ} {Ma Mb : Vector (Vector (ZMod 2) n) n} {Ha Hb : List ℕ}
    (hact : ∀ z x, bvec n (actM (genM Ha Hb z) x) = (untab (genT Ma Mb (z == 2)))ᵀ *ᵥ bvec n x)
    {x₀ : ℕ} {u : Vector (ZMod 2) n} (hu : bvec n x₀ = fun i => u[i]) {prog : List (ℕ × ℕ)}
    (hn : prog.length + 1 = n) :
    (spinM Ha Hb x₀ prog).length = n ∧
      maskMat n n (spinM Ha Hb x₀ prog) =
        (untab (rowTab (dualVecs Ma Mb u (boolProg prog)) u))ᵀ := by
  obtain ⟨h1, h2⟩ := colMat_spin (bvec n) 0 (fun z x => actM (genM Ha Hb z) x)
    (fun b y => vecMulT y (genT Ma Mb b)) x₀ u hu (fun z x y hxy =>
      (by rw [vecMulT_spec, ← hxy, ← Matrix.mulVec_transpose]; exact hact z x :
        bvec n (actM (genM Ha Hb z) x) = fun i => (vecMulT y (genT Ma Mb (z == 2)))[i])) prog hn
  refine ⟨h1, Matrix.ext fun i j => ?_⟩
  rw [Matrix.transpose_apply, untab_rowTab_apply, dualVecs, boolProg, List.foldl_map]
  exact h2 i j

theorem norF2_sound {n : ℕ} [NeZero n] {tw : List (List ℕ)} {tc : List ℕ}
    {Q Qi R Si Ti : List ℕ} {w : ℕ} {spin dual : List (ℕ × ℕ)} {Ga Gb : List ℕ}
    {Ma Mb : Vector (Vector (ZMod 2) n) n} (ha : untab Ma = maskMat n n Ga)
    (hb : untab Mb = maskMat n n Gb) (h : norF2 n tw tc Q Qi R Si Ti w spin dual Ga Gb = true) :
    (spinF2 n tw tc Q Qi R Si Ti w spin dual).check Ma Mb = true := by
  simp only [norF2, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hGa, hGb⟩, hQl⟩, hsp⟩, hdu⟩, hQQi⟩, hR⟩, hS⟩, hw⟩, hT⟩ := h
  have hact : ∀ z x, bvec n (actM (genM Ga Gb z) x) = untab (genT Ma Mb (z == 2)) *ᵥ bvec n x := by
    intro z x
    rw [genM_eq, genT]
    split_ifs
    · rw [bvec_actM_mulVec _ hGb, hb]
    · rw [bvec_actM_mulVec _ hGa, ha]
  have hactT : ∀ z x, bvec n (actM (genM (trM n Ga) (trM n Gb) z) x) =
      (untab (genT Ma Mb (z == 2)))ᵀ *ᵥ bvec n x := by
    intro z x
    rw [genM_eq, genT]
    split_ifs
    · rw [bvec_actM_mulVec _ (le_of_eq (length_trM n Gb)), maskMat_trM, hb]
    · rw [bvec_actM_mulVec _ (le_of_eq (length_trM n Ga)), maskMat_trM, ha]
  have hsum := bvec_sumT (Ma := Ma) (Mb := Mb)
    (dec_foldl_word (bvec n) (fun z x => actM (genM (trM n Ga) (trM n Gb) z) x) Ma Mb hactT)
    (tw.zip tc)
  simp only [SpinData.check, spinF2, Bool.and_eq_true]
  refine ⟨⟨⟨⟨decide_eq_true ?_, decide_eq_true ?_⟩, decide_eq_true ?_⟩, decide_eq_true ?_⟩,
    decide_eq_true ?_⟩
  · have e := maskMat_mulM (m := n) (n := n) Q Qi hQl
    rw [maskMat_eq_of_eqM hQQi, maskMat_idM] at e
    have e' := congrArg Matrix.transpose e
    rw [Matrix.transpose_one, Matrix.transpose_mul] at e'
    rw [untab_mulT, untab_decF2, untab_decF2]
    exact e'.symm
  · have hf := fun x : ℕ =>
      (bvec_actM_mulVec Q hQl (sumT (trM n Ga) (trM n Gb) (tw.zip tc) x)).trans
        ((congrArg (maskMat n n Q *ᵥ ·) (hsum x)).trans (Matrix.mulVec_mulVec _ _ _))
    have e := maskMat_map (n := n) hf R
    rw [maskMat_eq_of_eqM hR, maskMat_diag0] at e
    have e' := congrArg Matrix.transpose e
    rw [Matrix.diagonal_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, ← Matrix.mul_assoc] at e'
    rw [untab_mulT, untab_mulT, untab_decF2, untab_decF2]
    exact e'.symm
  · have hu : bvec n (col0 Q) = fun i => (Vector.ofFn fun l : Fin n => (decF2 n n Q)[l][(0 : Fin n)])[i] := by
      rw [← col0_eq]
      funext i
      simp
    obtain ⟨-, hSM⟩ := maskMat_spinM hact hu hsp
    have e := maskMat_mulM (m := n) (n := n) (trM n Si) (spinM Ga Gb (col0 Q) spin)
      (le_of_eq (length_trM n Si))
    rw [maskMat_eq_of_eqM hS, maskMat_idM, hSM, maskMat_trM] at e
    rw [untab_mulT, untab_decF2]
    exact e.symm
  · intro j
    have hbz : bvec n (sumT (trM n Ga) (trM n Gb) (tw.zip tc) w) = 0 := by
      funext i
      have h1 := congrArg (fun x => x.testBit i) hw
      simp only [Nat.testBit_mod_two_pow, i.2, decide_true, Bool.true_and,
        Nat.zero_testBit] at h1
      simp [bvec, h1]
    refine (congrFun (vecMulT_spec _ _) j).trans ?_
    rw [decVecF2_eq, ← Matrix.mulVec_transpose]
    exact congrFun ((hsum w).symm.trans hbz) j
  · obtain ⟨hUl, hUM⟩ := maskMat_spinM_dual hactT (decVecF2_eq n w).symm hdu
    have e := maskMat_mulM (m := n) (n := n) _ Ti (le_of_eq hUl)
    rw [maskMat_eq_of_eqM hT, maskMat_idM, hUM] at e
    have e' := congrArg Matrix.transpose e
    rw [Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose] at e'
    rw [untab_mulT, untab_decF2]
    exact e'.symm

@[expose] def pent (x : ℕ × ℕ) (i : ℕ) : FieldFour := ⟨x.1.testBit i, x.2.testBit i⟩

@[expose] def pairMat (m n : ℕ) (X : List (ℕ × ℕ)) : Matrix (Fin m) (Fin n) FieldFour :=
  Matrix.of fun i j => pent (X.getD j (0, 0)) i

theorem pent_zero (i : ℕ) : pent (0, 0) i = 0 := by
  simp only [pent, Nat.zero_testBit]
  rfl

theorem pent_xorP (x y : ℕ × ℕ) (i : ℕ) : pent (xorP x y) i = pent x i + pent y i :=
  FieldFour.ext (Nat.testBit_xor x.1 y.1 i) (Nat.testBit_xor x.2 y.2 i)

theorem pent_smulP (s₀ s₁ : Bool) (c : ℕ × ℕ) (i : ℕ) :
    pent (smulP s₀ s₁ c) i = (⟨s₀, s₁⟩ : FieldFour) * pent c i := by
  obtain ⟨c₀, c₁⟩ := c
  cases s₀ <;> cases s₁ <;> simp only [smulP, pent, Nat.testBit_xor, Nat.zero_testBit] <;>
    generalize c₀.testBit i = a <;> generalize c₁.testBit i = b <;> cases a <;> cases b <;> rfl

theorem actF4_zero : ∀ A : List (ℕ × ℕ), actF4 A (0, 0) = (0, 0)
  | [] => rfl
  | c :: cs => by
    rw [actF4]
    simp only [Nat.zero_mod, Nat.zero_div]
    rw [actF4_zero cs]
    simp [xorP, smulP]

theorem pent_actF4 (i : ℕ) : ∀ (A : List (ℕ × ℕ)) (x : ℕ × ℕ),
    pent (actF4 A x) i = ∑ l ∈ Finset.range A.length, pent x l * pent (A.getD l (0, 0)) i
  | [], x => by
    simp only [actF4, List.length_nil, Finset.range_zero, Finset.sum_empty]
    exact pent_zero i
  | c :: cs, x => by
    rw [actF4, pent_xorP, pent_actF4 i cs, List.length_cons, Finset.sum_range_succ', add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun l _ => ?_
      simp only [pent, Nat.testBit_add_one, List.getD_cons_succ]
    · rw [pent_smulP, List.getD_cons_zero]
      congr 1
      exact FieldFour.ext (beq_mod_two _) (beq_mod_two _)

theorem getD_mulF4 (A B : List (ℕ × ℕ)) (j : ℕ) :
    (mulF4 A B).getD j (0, 0) = actF4 A (B.getD j (0, 0)) := by
  rw [mulF4, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases B[j]? with
  | none => exact (actF4_zero A).symm
  | some b => rfl

theorem pairMat_mulF4 {m k n : ℕ} (A B : List (ℕ × ℕ)) (hA : A.length ≤ k) :
    pairMat m n (mulF4 A B) = pairMat m k A * pairMat k n B := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  simp only [pairMat, Matrix.of_apply]
  rw [getD_mulF4, pent_actF4]
  set x := B.getD j (0, 0)
  have hR : ∑ l : Fin k, pent (A.getD l (0, 0)) i * pent x l =
      ∑ l ∈ Finset.range k, pent (A.getD l (0, 0)) i * pent x l :=
    Fin.sum_univ_eq_sum_range (fun l => pent (A.getD l (0, 0)) i * pent x l) k
  rw [hR, ← Finset.sum_range_add_sum_Ico _ hA]
  have hIco : ∑ l ∈ Finset.Ico A.length k, pent (A.getD l (0, 0)) i * pent x l = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [List.getD_eq_default _ _ (Finset.mem_Ico.1 hl).1, pent_zero, zero_mul]
  rw [hIco, add_zero]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem pairMat_idF4 (n : ℕ) : pairMat n n (idF4 n) = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.one_apply]
  have hj : (idF4 n).getD j (0, 0) = (2 ^ (j : ℕ), 0) := by
    rw [idF4, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  simp only [pairMat, Matrix.of_apply, pent, hj, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    exact FieldFour.ext (decide_eq_true rfl) rfl
  · have : (j : ℕ) ≠ i := fun h' => h (Fin.ext h'.symm)
    rw [if_neg h]
    exact FieldFour.ext (decide_eq_false this) rfl

theorem getD_mod_of_eqF4 {m : ℕ} : ∀ {X Y : List (ℕ × ℕ)}, eqF4 m X Y = true → ∀ j,
    (X.getD j (0, 0)).1 % 2 ^ m = (Y.getD j (0, 0)).1 % 2 ^ m ∧
      (X.getD j (0, 0)).2 % 2 ^ m = (Y.getD j (0, 0)).2 % 2 ^ m
  | [], Y, h, j => by
    simp only [eqF4, List.all_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
    rw [List.getD_nil]
    by_cases hj : j < Y.length
    · rw [List.getD_eq_getElem _ _ hj]
      obtain ⟨h1, h2⟩ := h _ (List.getElem_mem hj)
      exact ⟨by simp [h1], by simp [h2]⟩
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hj)]
      exact ⟨rfl, rfl⟩
  | x :: xs, Y, h, j => by
    simp only [eqF4, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases j with
    | zero => cases Y <;> exact ⟨by simpa using h1, by simpa using h2⟩
    | succ j =>
      obtain ⟨e1, e2⟩ := getD_mod_of_eqF4 h3 j
      cases Y <;> exact ⟨by simpa using e1, by simpa using e2⟩

theorem pairMat_eq_of_eqF4 {m n : ℕ} {X Y : List (ℕ × ℕ)} (h : eqF4 m X Y = true) :
    pairMat m n X = pairMat m n Y := by
  refine Matrix.ext fun i j => ?_
  obtain ⟨h1, h2⟩ := getD_mod_of_eqF4 h j
  have e1 := congrArg (fun x => x.testBit i) h1
  have e2 := congrArg (fun x => x.testBit i) h2
  simp only [Nat.testBit_mod_two_pow, i.2, decide_true, Bool.true_and] at e1 e2
  exact FieldFour.ext e1 e2

theorem map_fst_trStepF4 : ∀ (rs : List (ℕ × ℕ)) (c : ℕ × ℕ),
    (trStepF4 rs c).map Prod.fst = trStep (rs.map Prod.fst) c.1
  | [], _ => rfl
  | r :: rs, c => by
    rw [trStepF4, List.map_cons, map_fst_trStepF4 rs, List.map_cons, trStep]

theorem map_snd_trStepF4 : ∀ (rs : List (ℕ × ℕ)) (c : ℕ × ℕ),
    (trStepF4 rs c).map Prod.snd = trStep (rs.map Prod.snd) c.2
  | [], _ => rfl
  | r :: rs, c => by
    rw [trStepF4, List.map_cons, map_snd_trStepF4 rs, List.map_cons, trStep]

theorem map_fst_trF4 (m : ℕ) : ∀ X : List (ℕ × ℕ),
    (trF4 m X).map Prod.fst = trM m (X.map Prod.fst)
  | [] => by simp [trF4, trM]
  | c :: X => by
    change (trStepF4 (trF4 m X) c).map Prod.fst = trStep (trM m (X.map Prod.fst)) c.1
    rw [map_fst_trStepF4, map_fst_trF4 m X]

theorem map_snd_trF4 (m : ℕ) : ∀ X : List (ℕ × ℕ),
    (trF4 m X).map Prod.snd = trM m (X.map Prod.snd)
  | [] => by simp [trF4, trM]
  | c :: X => by
    change (trStepF4 (trF4 m X) c).map Prod.snd = trStep (trM m (X.map Prod.snd)) c.2
    rw [map_snd_trStepF4, map_snd_trF4 m X]

theorem length_trF4 (m : ℕ) (X : List (ℕ × ℕ)) : (trF4 m X).length = m := by
  rw [← List.length_map (f := Prod.fst), map_fst_trF4, length_trM]

theorem getD_fst (X : List (ℕ × ℕ)) (j : ℕ) :
    (X.getD j (0, 0)).1 = (X.map Prod.fst).getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases X[j]? <;> rfl

theorem getD_snd (X : List (ℕ × ℕ)) (j : ℕ) :
    (X.getD j (0, 0)).2 = (X.map Prod.snd).getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases X[j]? <;> rfl

theorem pairMat_trF4 (m n : ℕ) (X : List (ℕ × ℕ)) :
    pairMat n m (trF4 m X) = (pairMat m n X).transpose := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.transpose_apply]
  simp only [pairMat, Matrix.of_apply, pent]
  rw [getD_fst, getD_snd, map_fst_trF4, map_snd_trF4, testBit_trM m _ j.2, testBit_trM m _ j.2,
    ← getD_fst, ← getD_snd]

theorem pairMat_ofF2 (m n : ℕ) (X : List ℕ) :
    pairMat m n (ofF2 X) = (maskMat m n X).map ofPrime := by
  refine Matrix.ext fun i j => ?_
  have hg : (ofF2 X).getD j (0, 0) = (X.getD j 0, 0) := by
    rw [ofF2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases X[j]? <;> rfl
  simp only [pairMat, Matrix.of_apply, Matrix.map_apply, maskMat_apply, hg, pent,
    Nat.zero_testBit]
  cases (X.getD j 0).testBit i <;> first | rfl | decide

theorem pairMat_frobF4 (m n : ℕ) (X : List (ℕ × ℕ)) :
    pairMat m n (frobF4 X) = (pairMat m n X).map frob := by
  refine Matrix.ext fun i j => ?_
  have hg : (frobF4 X).getD j (0, 0) =
      ((X.getD j (0, 0)).1 ^^^ (X.getD j (0, 0)).2, (X.getD j (0, 0)).2) := by
    rw [frobF4, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases X[j]? <;> rfl
  simp only [pairMat, Matrix.of_apply, Matrix.map_apply, hg]
  exact FieldFour.ext
    (Nat.testBit_xor (X.getD (j : ℕ) (0, 0)).1 (X.getD (j : ℕ) (0, 0)).2 i) rfl

theorem planes_zero : ∀ k, planes k 0 = (0, 0)
  | 0 => rfl
  | k + 1 => by simp [planes, planes_zero k]

theorem testBit_planes : ∀ (k r j : ℕ), j < k →
    (planes k r).1.testBit j = r.testBit (2 * j) ∧
      (planes k r).2.testBit j = r.testBit (2 * j + 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, r, 0, _ => by
    change (r % 2 + 2 * (planes k (r / 4)).1).testBit 0 = _ ∧
      (r / 2 % 2 + 2 * (planes k (r / 4)).2).testBit 0 = _
    refine ⟨?_, ?_⟩
    · rw [testBit_bit_zero' (Nat.mod_lt _ (by norm_num)), Nat.mul_zero, Nat.testBit_zero]
    · rw [testBit_bit_zero' (Nat.mod_lt _ (by norm_num)), Nat.mul_zero, Nat.zero_add,
        Nat.testBit_add_one, Nat.testBit_zero]
  | k + 1, r, j + 1, h => by
    have ih := testBit_planes k (r / 4) j (by omega)
    change (r % 2 + 2 * (planes k (r / 4)).1).testBit (j + 1) = _ ∧
      (r / 2 % 2 + 2 * (planes k (r / 4)).2).testBit (j + 1) = _
    rw [testBit_bit_succ' (Nat.mod_lt _ (by norm_num)),
      testBit_bit_succ' (Nat.mod_lt _ (by norm_num)), ih.1, ih.2]
    have e : r / 4 = r / 2 ^ 2 := rfl
    rw [e, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    constructor <;> congr 1 <;> omega

theorem getD_map_planes (n : ℕ) (rows : List ℕ) (i : ℕ) :
    (rows.map (planes n)).getD i (0, 0) = planes n (rows.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases rows[i]? with
  | none => exact (planes_zero n).symm
  | some r => rfl

theorem pent_planes (n w : ℕ) (j : Fin n) : pent (planes n w) j = (decVecF4 n w)[j] := by
  obtain ⟨h1, h2⟩ := testBit_planes n w j j.2
  simp only [decVecF4, Fin.getElem_fin, Vector.getElem_ofFn]
  exact FieldFour.ext h1 h2

theorem untab_decF4 (m n : ℕ) (rows : List ℕ) :
    untab (decF4 m n rows) = (pairMat n m (rowsF4 n rows)).transpose := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.transpose_apply]
  simp only [untab, decF4, pairMat, rowsF4, Matrix.of_apply, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_ofFn]
  rw [getD_map_planes]
  obtain ⟨h1, h2⟩ := testBit_planes n (rows.getD i 0) j j.2
  exact FieldFour.ext h1.symm h2.symm

theorem untab_decF4_cols (m n : ℕ) (rows : List ℕ) :
    untab (decF4 m n rows) = pairMat m n (colsF4 n rows) := by
  rw [untab_decF4, colsF4, pairMat_trF4]

theorem testBit_col0F4 : ∀ (Q : List ℕ) (l : ℕ),
    (col0F4 Q).1.testBit l = (Q.getD l 0).testBit 0 ∧
      (col0F4 Q).2.testBit l = (Q.getD l 0).testBit 1
  | [], l => by simp [col0F4]
  | r :: Q, 0 => by
    change (r % 2 + 2 * (col0F4 Q).1).testBit 0 = _ ∧ (r / 2 % 2 + 2 * (col0F4 Q).2).testBit 0 = _
    refine ⟨?_, ?_⟩
    · rw [testBit_bit_zero' (Nat.mod_lt _ (by norm_num)), List.getD_cons_zero, Nat.testBit_zero]
    · rw [testBit_bit_zero' (Nat.mod_lt _ (by norm_num)), List.getD_cons_zero,
        testBit_eq_decide r 1, Nat.pow_one]
  | r :: Q, l + 1 => by
    change (r % 2 + 2 * (col0F4 Q).1).testBit (l + 1) = _ ∧
      (r / 2 % 2 + 2 * (col0F4 Q).2).testBit (l + 1) = _
    rw [testBit_bit_succ' (Nat.mod_lt _ (by norm_num)),
      testBit_bit_succ' (Nat.mod_lt _ (by norm_num)), List.getD_cons_succ]
    exact testBit_col0F4 Q l

theorem col0F4_eq (n : ℕ) [NeZero n] (Q : List ℕ) (l : Fin n) :
    (decF4 n n Q)[l][(0 : Fin n)] = pent (col0F4 Q) l := by
  obtain ⟨h1, h2⟩ := testBit_col0F4 Q l
  simp only [decF4, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, Fin.val_zero,
    Nat.mul_zero, Nat.zero_add]
  exact FieldFour.ext h1.symm h2.symm

theorem subOK_of_subF4 {m d : ℕ} {Ka Kb : Vector (Vector FieldFour m) m}
    {B : Vector (Vector FieldFour d) m} {P : Vector (Vector FieldFour m) d}
    {Ka' Kb' B' P' : List (ℕ × ℕ)} {Ks : List (List (ℕ × ℕ))}
    (hKa : untab Ka = pairMat m m Ka') (hKb : untab Kb = pairMat m m Kb')
    (hB : untab B = pairMat m d B') (hP : untab P = pairMat d m P')
    (h : subF4 m d B' P' Ks = true) (ha : Ka' ∈ Ks) (hb : Kb' ∈ Ks) :
    subOK Ka Kb B P = true := by
  simp only [subF4, subStepF4, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hBl, hPl⟩, hPB⟩, hKs⟩ := h
  have step : ∀ {K : Vector (Vector FieldFour m) m} {K' : List (ℕ × ℕ)},
      untab K = pairMat m m K' → K' ∈ Ks →
        untab (mulT K B) = untab (mulT B (mulT P (mulT K B))) := by
    intro K K' hK hK'
    obtain ⟨hl, he⟩ := hKs K' hK'
    rw [untab_mulT, untab_mulT, untab_mulT, untab_mulT, hK, hB, hP, ← pairMat_mulF4 _ _ hl,
      ← pairMat_mulF4 _ _ hPl, ← pairMat_mulF4 _ _ hBl]
    exact pairMat_eq_of_eqF4 he
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true]
  refine ⟨?_, step hKa ha, step hKb hb⟩
  rw [untab_mulT, hP, hB, ← pairMat_mulF4 _ _ hPl, pairMat_eq_of_eqF4 hPB, pairMat_idF4]

def pvec (n : ℕ) (x : ℕ × ℕ) : Fin n → FieldFour := fun i => pent x i

theorem pvec_zero (n : ℕ) : pvec n (0, 0) = 0 := funext fun i => pent_zero i

theorem pvec_xorP (n : ℕ) (x y : ℕ × ℕ) : pvec n (xorP x y) = pvec n x + pvec n y :=
  funext fun i => pent_xorP x y i

theorem pvec_smulP (n : ℕ) (s₀ s₁ : Bool) (c : ℕ × ℕ) :
    pvec n (smulP s₀ s₁ c) = (⟨s₀, s₁⟩ : FieldFour) • pvec n c :=
  funext fun i => pent_smulP s₀ s₁ c i

theorem pvec_actF4_mulVec {n : ℕ} (A : List (ℕ × ℕ)) (hA : A.length ≤ n) (x : ℕ × ℕ) :
    pvec n (actF4 A x) = pairMat n n A *ᵥ pvec n x := by
  funext i
  exact congrFun (congrFun (pairMat_mulF4 (m := n) (n := 1) A [x] hA) i) 0

theorem pairMat_map {m k n : ℕ} {M : Matrix (Fin m) (Fin k) FieldFour} {f : ℕ × ℕ → ℕ × ℕ}
    (hf : ∀ x, pvec m (f x) = M *ᵥ pvec k x) (X : List (ℕ × ℕ)) :
    pairMat m n (X.map f) = M * pairMat k n X :=
  colMat_map (pvec_zero m) (pvec_zero k) hf X

theorem pairMat_diag0F4 (n : ℕ) [NeZero n] :
    pairMat n n (diag0F4 n) = Matrix.diagonal fun j : Fin n => if j = 0 then 0 else 1 :=
  colMat_diag0 (dec := pvec n) (d₀ := (0, 0)) (pvec_zero n) (pairMat_idF4 n)

theorem genF4_eq (Ga Gb : List (ℕ × ℕ)) (z : ℕ) :
    genF4 Ga Gb z = if (z == 2) = true then Gb else Ga := by
  rw [genF4, beq_two_eq]
  cases z == 2 <;> rfl

theorem ofCode4_beq (c : ℕ) :
    (⟨Nat.beq (c % 2) 1, Nat.beq (c / 2 % 2) 1⟩ : FieldFour) = ofCode4 c := by
  rw [beq_mod_two, beq_mod_two, ← Nat.testBit_add_one]
  rfl

theorem pvec_sumTF4 {n : ℕ} {Ma Mb : Vector (Vector FieldFour n) n} {Ha Hb : List (ℕ × ℕ)}
    (hw : ∀ (W : List ℕ) y, pvec n (wordTF4 Ha Hb W y) =
      (untab (CFSG.Quasithin.B45Mat.wordT Ma Mb (boolWord W)))ᵀ *ᵥ pvec n y) :
    ∀ (L : List (List ℕ × ℕ)) (y : ℕ × ℕ), pvec n (sumTF4 Ha Hb L y) =
      (untab (sumTerms ((L.map fun p => (boolWord p.1, ofCode4 p.2)).map
        fun t => (t.2, CFSG.Quasithin.B45Mat.wordT Ma Mb t.1))))ᵀ *ᵥ pvec n y
  | [], y => by
    change pvec n (0, 0) = _
    rw [List.map_nil, List.map_nil, untab_sumTerms_nil, Matrix.transpose_zero, Matrix.zero_mulVec,
      pvec_zero]
  | t :: L, y => by
    change pvec n (xorP (smulP (Nat.beq (t.2 % 2) 1) (Nat.beq (t.2 / 2 % 2) 1)
      (wordTF4 Ha Hb t.1 y)) (sumTF4 Ha Hb L y)) = _
    simp only [List.map_cons, untab_sumTerms_cons, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.add_mulVec, Matrix.smul_mulVec]
    rw [pvec_xorP, pvec_smulP, hw, pvec_sumTF4 hw L y, ofCode4_beq]

theorem pairMat_spinF4M {n : ℕ} {Ma Mb : Vector (Vector FieldFour n) n} {Ga Gb : List (ℕ × ℕ)}
    (hact : ∀ z x, pvec n (actF4 (genF4 Ga Gb z) x) = untab (genT Ma Mb (z == 2)) *ᵥ pvec n x)
    {x₀ : ℕ × ℕ} {u : Vector FieldFour n} (hu : pvec n x₀ = fun i => u[i])
    {prog : List (ℕ × ℕ)} (hn : prog.length + 1 = n) :
    (spinF4M Ga Gb x₀ prog).length = n ∧
      pairMat n n (spinF4M Ga Gb x₀ prog) =
        untab (colTab (spinVecs Ma Mb u (boolProg prog)) u) := by
  obtain ⟨h1, h2⟩ := colMat_spin (pvec n) (0, 0) (fun z x => actF4 (genF4 Ga Gb z) x)
    (fun b y => mulVecT (genT Ma Mb b) y) x₀ u hu (fun z x y hxy =>
      (by rw [mulVecT_spec, ← hxy]; exact hact z x :
        pvec n (actF4 (genF4 Ga Gb z) x) = fun i => (mulVecT (genT Ma Mb (z == 2)) y)[i]))
    prog hn
  refine ⟨h1, Matrix.ext fun i j => ?_⟩
  rw [untab_colTab_apply, spinVecs, boolProg, List.foldl_map]
  exact h2 i j

theorem pairMat_spinF4M_dual {n : ℕ} {Ma Mb : Vector (Vector FieldFour n) n}
    {Ha Hb : List (ℕ × ℕ)}
    (hact : ∀ z x, pvec n (actF4 (genF4 Ha Hb z) x) =
      (untab (genT Ma Mb (z == 2)))ᵀ *ᵥ pvec n x)
    {x₀ : ℕ × ℕ} {u : Vector FieldFour n} (hu : pvec n x₀ = fun i => u[i])
    {prog : List (ℕ × ℕ)} (hn : prog.length + 1 = n) :
    (spinF4M Ha Hb x₀ prog).length = n ∧
      pairMat n n (spinF4M Ha Hb x₀ prog) =
        (untab (rowTab (dualVecs Ma Mb u (boolProg prog)) u))ᵀ := by
  obtain ⟨h1, h2⟩ := colMat_spin (pvec n) (0, 0) (fun z x => actF4 (genF4 Ha Hb z) x)
    (fun b y => vecMulT y (genT Ma Mb b)) x₀ u hu (fun z x y hxy =>
      (by rw [vecMulT_spec, ← hxy, ← Matrix.mulVec_transpose]; exact hact z x :
        pvec n (actF4 (genF4 Ha Hb z) x) = fun i => (vecMulT y (genT Ma Mb (z == 2)))[i]))
    prog hn
  refine ⟨h1, Matrix.ext fun i j => ?_⟩
  rw [Matrix.transpose_apply, untab_rowTab_apply, dualVecs, boolProg, List.foldl_map]
  exact h2 i j

theorem norF4_sound {n : ℕ} [NeZero n] {tw : List (List ℕ)} {tc : List ℕ}
    {Q Qi R Si Ti : List ℕ} {w : ℕ} {spin dual : List (ℕ × ℕ)} {Ga Gb : List (ℕ × ℕ)}
    {Ma Mb : Vector (Vector FieldFour n) n} (ha : untab Ma = pairMat n n Ga)
    (hb : untab Mb = pairMat n n Gb) (h : norF4 n tw tc Q Qi R Si Ti w spin dual Ga Gb = true) :
    (spinF4 n tw tc Q Qi R Si Ti w spin dual).check Ma Mb = true := by
  simp only [norF4, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hGa, hGb⟩, hQl⟩, hsp⟩, hdu⟩, hQQi⟩, hR⟩, hS⟩, hz₁⟩, hz₂⟩, hT⟩ := h
  have hQl' : (rowsF4 n Q).length ≤ n := by rw [rowsF4, List.length_map]; exact hQl
  have hact : ∀ z x, pvec n (actF4 (genF4 Ga Gb z) x) =
      untab (genT Ma Mb (z == 2)) *ᵥ pvec n x := by
    intro z x
    rw [genF4_eq, genT]
    split_ifs
    · rw [pvec_actF4_mulVec _ hGb, hb]
    · rw [pvec_actF4_mulVec _ hGa, ha]
  have hactT : ∀ z x, pvec n (actF4 (genF4 (trF4 n Ga) (trF4 n Gb) z) x) =
      (untab (genT Ma Mb (z == 2)))ᵀ *ᵥ pvec n x := by
    intro z x
    rw [genF4_eq, genT]
    split_ifs
    · rw [pvec_actF4_mulVec _ (le_of_eq (length_trF4 n Gb)), pairMat_trF4, hb]
    · rw [pvec_actF4_mulVec _ (le_of_eq (length_trF4 n Ga)), pairMat_trF4, ha]
  have hsum := pvec_sumTF4 (Ma := Ma) (Mb := Mb)
    (dec_foldl_word (pvec n) (fun z x => actF4 (genF4 (trF4 n Ga) (trF4 n Gb) z) x) Ma Mb hactT)
    (tw.zip tc)
  have hwv : pvec n (planes n w) = fun i => (decVecF4 n w)[i] := funext fun i => pent_planes n w i
  simp only [SpinData.check, spinF4, Bool.and_eq_true]
  refine ⟨⟨⟨⟨decide_eq_true ?_, decide_eq_true ?_⟩, decide_eq_true ?_⟩, decide_eq_true ?_⟩,
    decide_eq_true ?_⟩
  · have e := pairMat_mulF4 (m := n) (n := n) (rowsF4 n Q) (rowsF4 n Qi) hQl'
    rw [pairMat_eq_of_eqF4 hQQi, pairMat_idF4] at e
    have e' := congrArg Matrix.transpose e
    rw [Matrix.transpose_one, Matrix.transpose_mul] at e'
    rw [untab_mulT, untab_decF4, untab_decF4]
    exact e'.symm
  · have hf := fun x : ℕ × ℕ =>
      (pvec_actF4_mulVec (rowsF4 n Q) hQl' (sumTF4 (trF4 n Ga) (trF4 n Gb) (tw.zip tc) x)).trans
        ((congrArg (pairMat n n (rowsF4 n Q) *ᵥ ·) (hsum x)).trans (Matrix.mulVec_mulVec _ _ _))
    have e := pairMat_map (n := n) hf (rowsF4 n R)
    rw [pairMat_eq_of_eqF4 hR, pairMat_diag0F4] at e
    have e' := congrArg Matrix.transpose e
    rw [Matrix.diagonal_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, ← Matrix.mul_assoc] at e'
    rw [untab_mulT, untab_mulT, untab_decF4, untab_decF4]
    exact e'.symm
  · have hu : pvec n (col0F4 Q) =
        fun i => (Vector.ofFn fun l : Fin n => (decF4 n n Q)[l][(0 : Fin n)])[i] := by
      funext i
      simp only [pvec, Fin.getElem_fin, Vector.getElem_ofFn]
      exact (col0F4_eq n Q i).symm
    obtain ⟨-, hSM⟩ := pairMat_spinF4M hact hu hsp
    have e := pairMat_mulF4 (m := n) (n := n) (trF4 n (rowsF4 n Si))
      (spinF4M Ga Gb (col0F4 Q) spin) (le_of_eq (length_trF4 n _))
    rw [pairMat_eq_of_eqF4 hS, pairMat_idF4, hSM, pairMat_trF4] at e
    rw [untab_mulT, untab_decF4]
    exact e.symm
  · intro j
    have hbz : pvec n (sumTF4 (trF4 n Ga) (trF4 n Gb) (tw.zip tc) (planes n w)) = 0 := by
      funext i
      have h1 := congrArg (fun x => x.testBit i) hz₁
      have h2 := congrArg (fun x => x.testBit i) hz₂
      simp only [Nat.testBit_mod_two_pow, i.2, decide_true, Bool.true_and,
        Nat.zero_testBit] at h1 h2
      simp only [pvec, pent, h1, h2]
      rfl
    refine (congrFun (vecMulT_spec _ _) j).trans ?_
    rw [← hwv, ← Matrix.mulVec_transpose]
    exact congrFun ((hsum (planes n w)).symm.trans hbz) j
  · obtain ⟨hUl, hUM⟩ := pairMat_spinF4M_dual hactT hwv hdu
    have e := pairMat_mulF4 (m := n) (n := n) _ (rowsF4 n Ti) (le_of_eq hUl)
    rw [pairMat_eq_of_eqF4 hT, pairMat_idF4, hUM] at e
    have e' := congrArg Matrix.transpose e
    rw [Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose] at e'
    rw [untab_mulT, untab_decF4]
    exact e'.symm

theorem pent_traceGo : ∀ (i : ℕ) (Y : List (ℕ × ℕ)),
    pent (traceGo i Y) 0 = ∑ l ∈ Finset.range Y.length, pent (Y.getD l (0, 0)) (i + l)
  | _, [] => by
    simp only [traceGo, List.length_nil, Finset.range_zero, Finset.sum_empty]
    exact pent_zero 0
  | i, c :: cs => by
    rw [traceGo, pent_xorP, pent_traceGo (i + 1) cs, List.length_cons, Finset.sum_range_succ',
      add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [List.getD_cons_succ]
      congr 1
      omega
    · rw [List.getD_cons_zero, Nat.add_zero]
      exact FieldFour.ext (testBit_mod_two_zero _ _) (testBit_mod_two_zero _ _)

theorem trace_pairMat (n : ℕ) (X : List (ℕ × ℕ)) :
    Matrix.trace (pairMat n n X) = pent (traceF4 n X) 0 := by
  rw [traceF4, pent_traceGo]
  simp only [Nat.zero_add, Matrix.trace, Matrix.diag, pairMat, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun l => pent (X.getD l (0, 0)) l) n]
  have hl : (X.take n).length ≤ n := List.length_take_le _ _
  rw [← Finset.sum_range_add_sum_Ico _ hl]
  have hIco : ∑ l ∈ Finset.Ico (X.take n).length n, pent (X.getD l (0, 0)) l = 0 := by
    refine Finset.sum_eq_zero fun l hl' => ?_
    have h1 := Finset.mem_Ico.1 hl'
    have h2 : X.length ≤ l := by
      rw [List.length_take] at h1
      omega
    rw [List.getD_eq_default _ _ h2, pent_zero]
  rw [hIco, add_zero]
  refine Finset.sum_congr rfl fun l hl' => ?_
  have h1 : l < n := lt_of_lt_of_le (Finset.mem_range.1 hl') hl
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h1]

theorem traceK_sound {n c : ℕ} {X : List (ℕ × ℕ)} (h : traceK n X c = true) :
    Matrix.trace (pairMat n n X) = ofCode4 c := by
  simp only [traceK, Bool.and_eq_true, Nat.beq_eq] at h
  rw [trace_pairMat]
  refine FieldFour.ext ?_ ?_
  · change (traceF4 n X).1.testBit 0 = c.testBit 0
    rw [h.1, Nat.testBit_zero, Nat.testBit_zero, Nat.mod_mod]
  · change (traceF4 n X).2.testBit 0 = c.testBit 1
    rw [h.2, Nat.testBit_zero, Nat.mod_mod, testBit_eq_decide c 1, Nat.pow_one]

end CFSG.KC.B45M12

end
