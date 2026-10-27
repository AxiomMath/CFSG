module

public import Certificates.Data.Kernel.EvenSporG24Hex.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelHex

public section

namespace CFSG.KC.EvenSporG24Hex

open CFSG.EvenSporadicStandard.G24Model CFSG.Fischer Matrix

theorem dig_zero_add {a b : ℕ} (ha : a < 4) : dig (a + 4 * b) 0 = a := by
  simp only [dig, pow_zero, Nat.div_one]
  omega

theorem dig_succ (x i : ℕ) : dig x (i + 1) = dig (x / 4) i := by
  simp only [dig, pow_succ', Nat.div_div_eq_div_mul]

theorem dig_succ_add {a b : ℕ} (ha : a < 4) (i : ℕ) : dig (a + 4 * b) (i + 1) = dig b i := by
  rw [dig_succ]
  congr 1
  omega

theorem hor_succ (g : ℕ → ℕ) (n : ℕ) : hor g (n + 1) = g 0 + 4 * hor (fun i => g (i + 1)) n :=
  rfl

theorem hor_lt : ∀ (n : ℕ) (g : ℕ → ℕ), (∀ i < n, g i < 4) → hor g n < 4 ^ n
  | 0, _, _ => by simp [hor]
  | n + 1, g, h => by
    rw [hor_succ, pow_succ]
    have h0 := h 0 (Nat.zero_lt_succ n)
    have h1 := hor_lt n (fun i => g (i + 1)) fun i hi => h (i + 1) (by omega)
    omega

theorem dig_hor : ∀ (n : ℕ) (g : ℕ → ℕ), (∀ i < n, g i < 4) → ∀ i < n, dig (hor g n) i = g i
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, g, h, i, hi => by
    rw [hor_succ]
    rcases i with _ | i
    · exact dig_zero_add (h 0 (by omega))
    · rw [dig_succ_add (h 0 (by omega))]
      exact dig_hor n (fun i => g (i + 1)) (fun j hj => h (j + 1) (by omega)) i (by omega)

theorem hor_congr : ∀ (n : ℕ) (g g' : ℕ → ℕ), (∀ i < n, g i = g' i) → hor g n = hor g' n
  | 0, _, _, _ => rfl
  | n + 1, g, g', h => by
    rw [hor_succ, hor_succ, h 0 (by omega),
      hor_congr n (fun i => g (i + 1)) (fun i => g' (i + 1)) fun i hi => h (i + 1) (by omega)]

theorem eq_of_dig : ∀ (n x y : ℕ), x < 4 ^ n → y < 4 ^ n → (∀ i < n, dig x i = dig y i) → x = y
  | 0, x, y, hx, hy, _ => by simp at hx hy; omega
  | n + 1, x, y, hx, hy, h => by
    have h0 : x % 4 = y % 4 := by simpa [dig] using h 0 (by omega)
    have hq : x / 4 = y / 4 := by
      refine eq_of_dig n (x / 4) (y / 4) ?_ ?_ fun i hi => ?_
      · rw [pow_succ] at hx; omega
      · rw [pow_succ] at hy; omega
      · rw [← dig_succ, ← dig_succ]; exact h (i + 1) (by omega)
    omega

theorem four_pow : (4 : ℕ) ^ 14 = 2 ^ 28 := by norm_num

theorem dig_xor (a b i : ℕ) : dig (a ^^^ b) i = dig a i ^^^ dig b i := by
  have h4 : (4 : ℕ) ^ i = 2 ^ (2 * i) := by rw [pow_mul]; norm_num
  have h2 : (4 : ℕ) = 2 ^ 2 := by norm_num
  simp only [dig, h4]
  rw [h2, Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

@[expose] def gv (v : Vec) (i : ℕ) : ℕ := if h : i < 14 then (v ⟨i, h⟩).code.val else 0

theorem sum_hor : ∀ (n : ℕ) (f : Fin n → ℕ),
    ∑ i : Fin n, f i * 4 ^ (i : ℕ) = hor (fun i => if h : i < n then f ⟨i, h⟩ else 0) n
  | 0, f => by simp [hor]
  | n + 1, f => by
    rw [Fin.sum_univ_succ, hor_succ]
    have e : ∑ i : Fin n, f i.succ * 4 ^ ((i.succ : Fin (n + 1)) : ℕ) =
        4 * ∑ i : Fin n, f i.succ * 4 ^ (i : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [e, sum_hor n (fun i => f i.succ)]
    congr 1
    · simp
    · congr 1
      exact hor_congr n _ _ fun i hi => by
        simp only [hi, dif_pos, Nat.add_lt_add_iff_right]
        rfl

theorem vecCode_eq (v : Vec) : vecCode v = hor (gv v) 14 := by
  unfold vecCode
  exact sum_hor 14 fun i => (v i).code.val

theorem gv_lt (v : Vec) (i : ℕ) : gv v i < 4 := by
  unfold gv
  split
  · exact (v _).code.isLt
  · omega

theorem dig_vecCode (v : Vec) {i : ℕ} (hi : i < 14) : dig (vecCode v) i = gv v i := by
  rw [vecCode_eq]
  exact dig_hor 14 _ (fun j _ => gv_lt v j) i hi

theorem vecCode_lt (v : Vec) : vecCode v < 4 ^ 14 := by
  rw [vecCode_eq]
  exact hor_lt 14 _ fun j _ => gv_lt v j

theorem f4_ext {x y : F4} (h : x.code.val = y.code.val) : x = y := by
  cases x
  cases y
  simp only [F4.mk.injEq]
  exact Fin.ext h

theorem vecCode_inj {v w : Vec} (h : vecCode v = vecCode w) : v = w := by
  funext i
  have := dig_vecCode v i.isLt
  rw [h, dig_vecCode w i.isLt] at this
  simp only [gv, i.isLt, dif_pos] at this
  exact f4_ext this.symm

theorem code_add : ∀ x y : F4, (x + y).code.val = x.code.val ^^^ y.code.val := by decide

theorem code_mul : ∀ x y : F4, (x * y).code.val = mulN x.code.val y.code.val := by decide

theorem code_f4 (c : ℕ) : (f4 c).code.val = c % 4 := rfl

theorem mulN_lt (s c : ℕ) : mulN s c < 4 := by
  unfold mulN
  generalize (s % 2 * (c % 2) + s / 2 % 2 * (c / 2 % 2)) = A
  generalize (s % 2 * (c / 2 % 2) + s / 2 % 2 * (c % 2) + s / 2 % 2 * (c / 2 % 2)) = B
  omega

theorem vecCode_zero : vecCode (0 : Vec) = 0 := by
  rw [vecCode_eq]
  have : gv 0 = fun _ => 0 := by
    funext i
    unfold gv
    split <;> rfl
  rw [this]
  rfl

theorem scaleD_dig (s x : ℕ) {i : ℕ} (hi : i < 14) : dig (scaleD s x) i = mulN s (dig x i) :=
  dig_hor 14 _ (fun j _ => mulN_lt s _) i hi

theorem scaleD_lt (s x : ℕ) : scaleD s x < 2 ^ 28 := by
  rw [← four_pow]
  exact hor_lt 14 _ fun j _ => mulN_lt s _

theorem scaleD_congr (s : ℕ) {x y : ℕ} (h : ∀ i < 14, dig x i = dig y i) :
    scaleD s x = scaleD s y :=
  hor_congr 14 _ _ fun i hi => by rw [h i hi]

theorem gv_decode (n : ℕ) {i : ℕ} (hi : i < 14) : gv (decodeVec n) i = dig n i := by
  simp only [gv, hi, dif_pos, decodeVec, code_f4, dig]

theorem vecCode_comb {c d : ℕ} (hc : c < 4) (hd : d < 4) (u w : Vec) :
    vecCode (comb c d u w) = scaleD c (vecCode u) ^^^ scaleD d (vecCode w) := by
  refine eq_of_dig 14 _ _ (vecCode_lt _)
    (by rw [four_pow]; exact Nat.xor_lt_two_pow (scaleD_lt _ _) (scaleD_lt _ _)) fun i hi => ?_
  rw [dig_vecCode _ hi, dig_xor, scaleD_dig _ _ hi, scaleD_dig _ _ hi, dig_vecCode _ hi,
    dig_vecCode _ hi]
  simp only [gv, hi, dif_pos, comb, code_add, code_mul, code_f4, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hd]

theorem map_comb (U W : ℕ) :
    ((List.range 4).flatMap fun c => (List.range 4).filterMap fun d =>
        if c = 0 ∧ d = 0 then none else some (comb c d (decodeVec U) (decodeVec W))).map vecCode =
      codesK U W := by
  unfold codesK
  rw [List.map_flatMap]
  refine List.flatMap_congr fun c hc => ?_
  rw [List.map_filterMap]
  refine List.filterMap_congr fun d hd => ?_
  rw [List.mem_range] at hc hd
  split
  · rfl
  · simp only [Option.map_some, vecCode_comb hc hd]
    have hU : ∀ i < 14, dig (vecCode (decodeVec U)) i = dig U i := fun i hi => by
      rw [dig_vecCode _ hi, gv_decode _ hi]
    have hW : ∀ i < 14, dig (vecCode (decodeVec W)) i = dig W i := fun i hi => by
      rw [dig_vecCode _ hi, gv_decode _ hi]
    rw [scaleD_congr c hU, scaleD_congr d hW]

theorem map_lineVecs (k : ℕ) : (lineVecs k).map vecCode = codesK (lineU k) (lineW k) :=
  map_comb (lineU k) (lineW k)

theorem codesK_length (U W : ℕ) : (codesK U W).length = 15 := by
  simp [codesK, List.range_succ]

theorem codesK_lt (U W : ℕ) : ∀ x ∈ codesK U W, x < 2 ^ 28 := by
  intro x hx
  simp only [codesK, List.mem_flatMap, List.mem_filterMap] at hx
  obtain ⟨c, -, d, -, h⟩ := hx
  split at h
  · cases h
  · cases h
    exact Nat.xor_lt_two_pow (scaleD_lt _ _) (scaleD_lt _ _)

theorem insN_eq (a : ℕ) : ∀ l : List ℕ, insN a l = l.orderedInsert (· ≤ ·) a
  | [] => by rw [insN, List.orderedInsert_nil]
  | b :: l => by
    rw [insN, List.orderedInsert_cons, insN_eq a l]

theorem isortN_eq : ∀ l : List ℕ, isortN l = l.insertionSort (· ≤ ·)
  | [] => by rw [isortN, List.insertionSort_nil]
  | b :: l => by rw [isortN, List.insertionSort_cons, isortN_eq l, insN_eq]

theorem isortN_perm (l : List ℕ) : List.Perm (isortN l) l := by
  rw [isortN_eq]
  exact List.perm_insertionSort _ l

theorem pairwise_of_strictInc : ∀ l : List ℕ, strictInc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    have hp := pairwise_of_strictInc (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) hp
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons hp hx)

theorem nodup_of_strictInc {l : List ℕ} (h : strictInc (isortN l) = true) : l.Nodup :=
  (isortN_perm l).nodup_iff.1 ((pairwise_of_strictInc _ h).imp fun h => ne_of_lt h)

theorem fld_eq (w P k : ℕ) : fld w P k = P / 2 ^ (w * k) % 2 ^ w := by
  rw [fld, Nat.shiftRight_eq_div_pow]

theorem fld_pk {w : ℕ} : ∀ (l : List ℕ), (∀ x ∈ l, x < 2 ^ w) → ∀ q, fld w (pk w l) q = l.getD q 0
  | [], _, q => by simp [fld_eq, pk]
  | x :: l, h, q => by
    have hx := h x (by simp)
    rcases q with _ | q
    · simp only [fld_eq, pk, Nat.mul_zero, pow_zero, Nat.div_one, List.getD_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    · rw [List.getD_cons_succ, ← fld_pk l (fun y hy => h y (by simp [hy])) q]
      simp only [fld_eq, pk]
      congr 1
      rw [Nat.mul_succ, pow_add, Nat.mul_comm (2 ^ (w * q)), ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem pk_lt {w : ℕ} : ∀ (l : List ℕ), (∀ x ∈ l, x < 2 ^ w) → pk w l < 2 ^ (w * l.length)
  | [], _ => by simp [pk]
  | x :: l, h => by
    have hx := h x (by simp)
    have hl := pk_lt l fun y hy => h y (by simp [hy])
    simp only [pk, List.length_cons, Nat.mul_succ, pow_add]
    have : 2 ^ w * pk w l + 2 ^ w ≤ 2 ^ (w * l.length) * 2 ^ w := by
      rw [Nat.mul_comm (2 ^ (w * l.length))]
      have := Nat.mul_le_mul_left (2 ^ w) (Nat.succ_le_of_lt hl)
      rw [Nat.mul_succ] at this
      exact this
    omega

theorem mem_of_memP {x : ℕ} {l : List ℕ} (hl : l.length = 15) (hlt : ∀ y ∈ l, y < 2 ^ 28)
    (h : memP x (pk 28 l) = true) : x ∈ l := by
  simp only [memP, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨q, hq, e⟩ := h
  rw [fld_pk l hlt, List.getD_eq_getElem _ _ (by omega)] at e
  rw [← e]
  exact List.getElem_mem _

theorem xorN_congr : ∀ (n : ℕ) (f g : ℕ → ℕ), (∀ b < n, f b = g b) → xorN f n = xorN g n
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    simp only [xorN, xorN_congr n f g fun b hb => h b (by omega), h n (by omega)]

theorem dig_xorN (f : ℕ → ℕ) (i : ℕ) : ∀ n, dig (xorN f n) i = xorN (fun b => dig (f b) i) n
  | 0 => by simp [xorN, dig]
  | n + 1 => by simp only [xorN, dig_xor, dig_xorN f i n]

theorem xorN_lt {m : ℕ} (f : ℕ → ℕ) : ∀ n, (∀ b < n, f b < 2 ^ m) → xorN f n < 2 ^ m
  | 0, _ => by simp [xorN]
  | n + 1, h => Nat.xor_lt_two_pow (xorN_lt f n fun b hb => h b (by omega)) (h n (by omega))

theorem code_sum : ∀ (n : ℕ) (f : Fin n → F4),
    (∑ b, f b).code.val = xorN (fun b => if h : b < n then (f ⟨b, h⟩).code.val else 0) n
  | 0, f => by simp [xorN]; rfl
  | n + 1, f => by
    rw [Fin.sum_univ_castSucc, code_add, code_sum n, xorN]
    congr 1
    · exact xorN_congr n _ _ fun b hb => by simp [hb, Nat.lt_succ_of_lt hb]
    · rw [dif_pos (Nat.lt_succ_self n)]
      rfl

theorem csOf_length (E : List ℕ) : (csOf E).length = 56 := by simp [csOf]

theorem csOf_lt (E : List ℕ) : ∀ x ∈ csOf E, x < 2 ^ 28 := by
  intro x hx
  simp only [csOf, List.mem_map] at hx
  obtain ⟨q, -, rfl⟩ := hx
  rw [← four_pow]
  exact hor_lt 14 _ fun a _ => mulN_lt _ _

theorem fld_csOf (E : List ℕ) {b s : ℕ} (hb : b < 14) (hs : s < 4) {a : ℕ} (ha : a < 14) :
    dig (fld 28 (pk 28 (csOf E)) (4 * b + s)) a = mulN (E.getD (14 * a + b) 0 % 4) s := by
  rw [fld_pk _ (csOf_lt E), List.getD_eq_getElem _ _ (by rw [csOf_length]; omega)]
  simp only [csOf, List.getElem_map, List.getElem_range]
  rw [dig_hor 14 _ (fun j _ => mulN_lt _ _) a ha]
  have h1 : (4 * b + s) / 4 = b := by omega
  have h2 : (4 * b + s) % 4 = s := by omega
  rw [h1, h2]

theorem vecCode_mulVec (j : Fin 16) (E : List ℕ)
    (hE : ∀ a < 14, ∀ b < 14, E.getD (14 * a + b) 0 = genEntry j a b) (v : Vec) :
    vecCode (Gmat j *ᵥ v) = mulP (pk 28 (csOf E)) (vecCode v) := by
  refine eq_of_dig 14 _ _ (vecCode_lt _) ?_ fun a ha => ?_
  · rw [four_pow]
    exact xorN_lt _ 14 fun b _ => Nat.mod_lt _ (by positivity)
  rw [dig_vecCode _ ha, mulP, dig_xorN]
  simp only [gv, ha, dif_pos, Matrix.mulVec, dotProduct, code_sum]
  refine xorN_congr 14 _ _ fun b hb => ?_
  rw [dif_pos hb, dig_vecCode _ hb, fld_csOf E hb (gv_lt v b) ha, code_mul, hE a ha b hb]
  simp only [Gmat, Matrix.of_apply, code_f4, gv, hb, dif_pos]

theorem mulP_congr (C : ℕ) {x y : ℕ} (h : ∀ i < 14, dig x i = dig y i) : mulP C x = mulP C y :=
  xorN_congr 14 _ _ fun b hb => by rw [h b hb]

theorem getD_toArray (L : List ℕ) (i : ℕ) : L.toArray.getD i 0 = L.getD i 0 := by
  simp only [Array.getD, List.size_toArray, List.getElem_toArray]
  split <;> simp_all [List.getD_eq_getElem]

theorem getD_take (L : List ℕ) {i m : ℕ} (h : i < m) : (L.take m).getD i 0 = L.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem getD_drop (L : List ℕ) (m i : ℕ) : (L.drop m).getD i 0 = L.getD (m + i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_ilv : ∀ (U W : List ℕ) (k : ℕ), k < U.length → k < W.length →
    (ilv U W).getD (2 * k) 0 = U.getD k 0 ∧ (ilv U W).getD (2 * k + 1) 0 = W.getD k 0
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h => absurd h (Nat.not_lt_zero _)
  | u :: U, w :: W, k, hu, hw => by
    rcases k with _ | k
    · simp [ilv]
    · have := getD_ilv U W k (by simpa using hu) (by simpa using hw)
      have e1 : 2 * (k + 1) = 2 * k + 2 := by ring
      have e2 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
      simpa [ilv, e1, e2] using this

theorem getD_flatten {s : ℕ} : ∀ (L : List (List ℕ)), (∀ x ∈ L, x.length = s) →
    ∀ j < L.length, ∀ e < s, L.flatten.getD (s * j + e) 0 = (L.getD j []).getD e 0
  | [], _, j, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | x :: L, h, j, hj, e, he => by
    have hx := h x (by simp)
    rw [List.flatten_cons]
    rcases j with _ | j
    · simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : e < x.length)]
    · simp only [List.getD_cons_succ]
      rw [← getD_flatten L (fun y hy => h y (by simp [hy])) j (by simpa using hj) e he]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [hx]; nlinarith), hx]
      congr 2
      rw [Nat.mul_succ]
      omega

theorem lineKeys_get {k : ℕ} (hk : k < nLines) : lineKeys[k]! = keyOfSet (lineOf ⟨k, hk⟩) := by
  rw [getElem!_pos lineKeys k (by simp [lineKeys, hk])]
  simp [lineKeys, Array.getElem_ofFn]

theorem lineLists_get {k : ℕ} (hk : k < nLines) :
    lineLists[k]! = (lineVecs k).map vecList := by
  rw [getElem!_pos lineLists k (by simp [lineLists, hk])]
  simp [lineLists, Array.getElem_ofFn]

theorem keyOfSet_lineOf (k : Fin nLines) (h : (codesK (lineU k) (lineW k)).Nodup) :
    keyOfSet (lineOf k) = isortN (codesK (lineU k) (lineW k)) := by
  unfold keyOfSet lineOf
  have hi : (lineVecs k).toFinset.image vecCode = ((lineVecs k).map vecCode).toFinset := by
    ext x
    simp
  rw [hi, map_lineVecs,
    List.toFinset_eq_of_perm _ _ (isortN_perm (codesK (lineU k) (lineW k))).symm]
  refine (List.toFinset_sort (· ≤ ·) ((isortN_perm _).nodup_iff.2 h)).2 ?_
  rw [isortN_eq]
  exact List.pairwise_insertionSort _ _

theorem eq_of_eqL : ∀ {a b : List ℕ}, eqL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h
  | x :: l, y :: m, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eq_of_eqL h.2]

theorem hexOK_of {T U W : List ℕ} {GE PG : List (List ℕ)} {LC : ℕ} (hT : tbl = T.toArray)
    (hd : dataOK T U W GE PG = true) (hl : linesOK U W = true) (hk : keysOK U W = true)
    (hc : lcOK U W LC = true) (hj : ∀ j < 16, hexJ U W GE PG LC j = true) : hexOK = true := by
  simp only [dataOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hUl, hWl⟩, hUW⟩, hGl⟩, hGs⟩, hGE⟩, hPl⟩, hPs⟩, hPG⟩ := hd
  replace hUW := eq_of_eqL hUW
  replace hGE := eq_of_eqL hGE
  replace hPG := eq_of_eqL hPG
  have hTd : ∀ i, tbl.getD i 0 = T.getD i 0 := fun i => by rw [hT, getD_toArray]
  have hU : ∀ k < 1365, lineU k = U.getD k 0 := fun k hk => by
    rw [lineU, hTd, ← getD_take T (by omega : 2 * k < 2730), hUW]
    exact (getD_ilv U W k (by omega) (by omega)).1
  have hW : ∀ k < 1365, lineW k = W.getD k 0 := fun k hk => by
    rw [lineW, hTd, ← getD_take T (by omega : 2 * k + 1 < 2730), hUW]
    exact (getD_ilv U W k (by omega) (by omega)).2
  have hG : ∀ j < 16, ∀ a < 14, ∀ b < 14, (GE.getD j []).getD (14 * a + b) 0 = genEntry j a b :=
    fun j hj a ha b hb => by
      have e : 2 * nLines + 196 * j + 14 * a + b = 2730 + (196 * j + (14 * a + b)) := by
        simp only [nLines]; omega
      rw [genEntry, e, hTd, ← getD_flatten GE (fun x hx => by simpa using hGs x hx) j (by omega)
        (14 * a + b) (by omega), ← hGE, getD_take _ (by omega), getD_drop]
  have hP : ∀ j < 16, ∀ k < 1365, pgNum j k = (PG.getD j []).getD k 0 % 1365 :=
    fun j hj k hk => by
      have e : 2 * nLines + 16 * 196 + nLines * j + k = 5866 + (1365 * j + k) := by
        simp only [nLines]; omega
      rw [pgNum, e, hTd, ← getD_flatten PG (fun x hx => by simpa using hPs x hx) j (by omega) k hk,
        ← hPG, getD_take _ (by omega), getD_drop]
  have hcodes : ∀ k < 1365, (lineVecs k).map vecCode = codesK (U.getD k 0) (W.getD k 0) :=
    fun k hk => by rw [map_lineVecs, hU k hk, hW k hk]
  simp only [linesOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hl
  have hnd : ∀ k < 1365, (codesK (U.getD k 0) (W.getD k 0)).Nodup := fun k hk =>
    nodup_of_strictInc (hl k hk).1
  have hlt : ∀ x ∈ (List.range 1365).map fun k => pk 28 (codesK (U.getD k 0) (W.getD k 0)),
      x < 2 ^ 420 := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    have := pk_lt _ (codesK_lt (U.getD k 0) (W.getD k 0))
    rwa [codesK_length] at this
  simp only [lcOK, beq_iff_eq] at hc
  have hB : ∀ p < 1365, fld 420 LC p = pk 28 (codesK (U.getD p 0) (W.getD p 0)) := fun p hp => by
    rw [hc, fld_pk _ hlt, List.getD_eq_getElem _ _ (by simpa using hp)]
    simp
  unfold hexOK
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨fun k => ⟨?_, ?_⟩, fun k k' hne heq => ?_⟩, ?_⟩
  · have hm := hcodes k k.isLt
    have hn : (lineVecs k).Nodup := List.Nodup.of_map vecCode (hm ▸ hnd k k.isLt)
    rw [lineOf, List.toFinset_card_of_nodup hn, ← List.length_map (f := vecCode), hm,
      codesK_length]
  · intro h0
    have h1 : vecCode 0 ∈ codesK (U.getD k 0) (W.getD k 0) := by
      rw [← hcodes k k.isLt]; exact List.mem_map_of_mem h0
    rw [vecCode_zero] at h1
    have h2 := (hl k k.isLt).2 0 ((isortN_perm _).mem_iff.2 h1)
    simp at h2
  · rw [lineKeys_get k.isLt, lineKeys_get k'.isLt, keyOfSet_lineOf _ (by
        rw [hU k k.isLt, hW k k.isLt]; exact hnd k k.isLt), keyOfSet_lineOf _ (by
        rw [hU k' k'.isLt, hW k' k'.isLt]; exact hnd k' k'.isLt), hU k k.isLt, hW k k.isLt,
      hU k' k'.isLt, hW k' k'.isLt] at heq
    have hkn := (isortN_perm _).nodup_iff.1
      ((pairwise_of_strictInc _ hk).imp fun h => ne_of_lt h)
    have e : keyN U W k = keyN U W k' := by simp only [keyN, heq]
    have hk1 : (k : ℕ) < ((List.range 1365).map (keyN U W)).length := by simpa using k.isLt
    have hk2 : (k' : ℕ) < ((List.range 1365).map (keyN U W)).length := by simpa using k'.isLt
    have e' : ((List.range 1365).map (keyN U W))[(k : ℕ)] =
        ((List.range 1365).map (keyN U W))[(k' : ℕ)] := by simpa using e
    exact hne (Fin.ext ((List.Nodup.getElem_inj_iff hkn).1 e'))
  · rw [List.all_eq_true]
    intro j _
    have hJ := hj j j.isLt
    simp only [hexJ, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hJ
    rw [List.all_eq_true]
    intro k _
    obtain ⟨hJu, hJw⟩ := hJ k k.isLt
    have hp : (pgFin j k : ℕ) = (PG.getD j []).getD k 0 % 1365 := hP j j.isLt k k.isLt
    have hplt : (pgFin j k : ℕ) < 1365 := (pgFin j k).isLt
    have key : ∀ n : ℕ, memP (mulP (pk 28 (csOf (GE.getD j []))) n)
        (fld 420 LC ((PG.getD j []).getD k 0 % 1365)) = true →
        imgIn (Gmat j) (decodeVec n) lineLists[(pgFin j k : ℕ)]! = true := by
      intro n hn
      rw [← hp, hB _ hplt] at hn
      have hm := mem_of_memP (codesK_length _ _) (codesK_lt _ _) hn
      rw [← mulP_congr _ (fun i hi => by rw [dig_vecCode _ hi, gv_decode _ hi]),
        ← vecCode_mulVec j _ (hG j j.isLt), ← hcodes _ hplt] at hm
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      rw [vecCode_inj e] at hy
      unfold imgIn
      rw [decide_eq_true_eq, lineLists_get hplt]
      exact List.mem_map_of_mem hy
    have eu : uVec k = decodeVec (U.getD k 0) := by rw [uVec, hU k k.isLt]
    have ew : wVec k = decodeVec (W.getD k 0) := by rw [wVec, hW k k.isLt]
    rw [Bool.and_eq_true, eu, ew]
    exact ⟨key _ hJu, key _ hJw⟩

end CFSG.KC.EvenSporG24Hex
