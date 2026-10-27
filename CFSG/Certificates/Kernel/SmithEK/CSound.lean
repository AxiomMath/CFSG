module

public import CFSG.LargeExtraspecial.SMod20BasicCheck
public import CFSG.Certificates.Kernel.SmithEK.LaneSound
public import CFSG.Certificates.Kernel.U6Gen
public import CFSG.Certificates.Kernel.SmithEK.SpanSound

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE CFSG.Sporadic.Th.Native

theorem rowsC_sound {C : List (List Nat)} {R : Nat → Nat} (hl : C.length = 693)
    (hc : ∀ k < 693, (C.getD k []).length = 20 ∧ ∀ m < 20, (C.getD k []).getD m 0 < 2 ^ 20)
    (h : rowsC (pkW 400 (List.replicate 693 1) * l20) (pkW 400 (List.replicate 693 1))
      (pkW 20 ((List.range 20).map (2 ^ ·))) (pkW 400 (C.map (pkW 20))) (qsOf C) R C
      (C.map (pkW 20)) 0 = true) :
    ∀ j < 693, (∀ m < 20, applyL (C.getD j []) ((C.getD j []).getD m 0) = 2 ^ m) ∧
      ∀ a < 693, fldR R j a < 693 ∧ ∀ m < 20,
        applyL (C.getD j []) (applyL (C.getD a []) ((C.getD j []).getD m 0)) =
          (C.getD (fldR R j a) []).getD m 0 := by
  exact rowsC_lanes hl hc h

theorem ofFn_getC {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) {i : Nat} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem uPos_le' (x : Nat) : uPos[x]! ≤ uPts.size := by
  by_cases hx : x < 4096
  · unfold uPos
    rw [ofFn_getC _ hx]
    have := List.idxOf_le_length (a := x) (l := uPts.toList)
    simpa using this
  · rw [getElem!_neg (uPos ()) x (by simp [uPos]; omega)]
    exact Nat.zero_le _

theorem ptImg_eq {R : Nat → Nat} (hn : uPts.size = 693)
    (hR : ∀ m < 693, ∀ q < 693,
      ap (CFSG.KC.U6.tvTabsG uPts uPos)[m]! q = CFSG.KLie.CT.fget (R m) q 10)
    {j a : Nat} (hj : j < 693) (ha : a < 693) : ptImg j a = fldR R j a := by
  have e := hR j hj a ha
  unfold CFSG.KC.U6.tvTabsG at e
  rw [ofFn_getC _ hj] at e
  unfold ap CFSG.KC.U6.tvTableG at e
  rw [ofFn_getC _ ha, UInt32.toNat_ofNat', Nat.mod_eq_of_lt
    (lt_of_le_of_lt ((uPos_le' _).trans hn.le) (by norm_num))] at e
  unfold ptImg fldR
  rw [e, CFSG.KC.U6.Snd.fget_eq, Nat.mul_comm a 10]
  all_goals norm_num

theorem bounds_of {C : List (List Nat)} {R : Nat → Nat} (h : chkCF C R = true) :
    C.length = 693 ∧
      ∀ k < 693, (C.getD k []).length = 20 ∧ ∀ m < 20, (C.getD k []).getD m 0 < 2 ^ 20 := by
  unfold chkCF at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hc⟩, -⟩ := h
  refine ⟨hl, fun k hk => ?_⟩
  have hmem : C.getD k [] ∈ C := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  obtain ⟨h20, hlt⟩ := hc _ hmem
  exact ⟨h20, fun m hm => hlt _ (getD_mem (by rw [h20]; exact hm))⟩

theorem rows_of {C : List (List Nat)} {R : Nat → Nat} (h : chkCF C R = true) :
    ∀ j < 693, (∀ m < 20, applyL (C.getD j []) ((C.getD j []).getD m 0) = 2 ^ m) ∧
      ∀ a < 693, fldR R j a < 693 ∧ ∀ m < 20,
        applyL (C.getD j []) (applyL (C.getD a []) ((C.getD j []).getD m 0)) =
          (C.getD (fldR R j a) []).getD m 0 := by
  obtain ⟨hl, hc⟩ := bounds_of h
  unfold chkCF at h
  simp only [Bool.and_eq_true] at h
  exact rowsC_sound hl hc h.2

theorem chkTvInv_of {C : List (List Nat)} {R : Nat → Nat}
    (hT : ∀ k, tvArr[k]! = (C.getD k []).toArray) (h : chkCF C R = true) : chkTvInv = true := by
  obtain ⟨-, hc⟩ := bounds_of h
  have hr := rows_of h
  unfold chkTvInv
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  intro k hk
  rw [hT k]
  refine ⟨by rw [List.size_toArray]; exact (hc k hk).1, fun m hm => ?_⟩
  rw [getElem!_toArray, applyCols_toArray]
  exact ⟨(hc k hk).2 m hm, (hr k hk).1 m hm⟩

theorem chkTvConj_of {C : List (List Nat)} {R : Nat → Nat}
    (hT : ∀ k, tvArr[k]! = (C.getD k []).toArray) (hn : uPts.size = 693)
    (hR : ∀ m < 693, ∀ q < 693,
      ap (CFSG.KC.U6.tvTabsG uPts uPos)[m]! q = CFSG.KLie.CT.fget (R m) q 10)
    (h : chkCF C R = true) : chkTvConj = true := by
  have hr := rows_of h
  unfold chkTvConj
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  rw [List.all_eq_true]
  intro a ha
  have ha' := List.mem_range.1 ha
  dsimp only
  rw [ptImg_eq hn hR hj' ha', hT j, hT a, hT (fldR R j a)]
  obtain ⟨hb, hm⟩ := (hr j hj').2 a ha'
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hb, fun m hm' => ?_⟩
  rw [getElem!_toArray, getElem!_toArray, applyCols_toArray, applyCols_toArray, beq_iff_eq]
  exact hm m (List.mem_range.1 hm')

theorem wordImg_eq {R : Nat → Nat}
    (hb : ∀ j < 693, ∀ b < 693, ptImg j b = fldR R j b ∧ fldR R j b < 693) :
    ∀ (w : List Nat) (a : Nat), a < 693 → (∀ j ∈ w, j < 693) → wordImg w a = wordR R w a := by
  intro w
  induction w with
  | nil =>
    intro a _ _
    unfold wordImg wordR
    rw [List.foldl_nil, List.foldl_nil]
  | cons j w ih =>
    intro a ha hw
    have hj := hw j List.mem_cons_self
    have e := hb j hj a ha
    have e2 := ih _ e.2 fun i hi => hw i (List.mem_cons_of_mem _ hi)
    unfold wordImg wordR at e2 ⊢
    rw [List.foldl_cons, List.foldl_cons, e.1]
    exact e2

theorem ptWK_get {R : Nat → Nat} : ∀ (W : List (List Nat)) (a : Nat), ptWK R W a = true →
    ∀ i < W.length, (W.getD i []).all (fun j => decide (j < 693)) = true ∧
      wordR R (W.getD i []) (a + i) = 0
  | [], _, _, i, hi => absurd hi (by simp)
  | w :: W, a, h, i, hi => by
    have h' : ((w.all (fun j => decide (j < 693)) && wordR R w a == 0) && ptWK R W (a + 1)) =
        true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    rcases i with _ | i
    · exact ⟨h'.1.1, h'.1.2⟩
    · have e := ptWK_get W (a + 1) h'.2 i (by simpa using hi)
      rw [List.getD_cons_succ, show a + (i + 1) = a + 1 + i by omega]
      exact e

theorem pairWK_get {R : Nat → Nat} {p0 : Nat} : ∀ (W : List (List Nat)) (P : List Nat) (l : Nat),
    pairWK R p0 W P l = true → ∀ i < W.length,
      (CFSG.F4.Native.hermC p0 (P.getD i 0) = 0 ∨
        ((W.getD i []).all (fun j => decide (j < 693) && fldR R j 0 == 0) = true ∧
          wordR R (W.getD i []) (l + i) = 1))
  | [], _, _, _, i, hi => absurd hi (by simp)
  | w :: W, P, l, h, i, hi => by
    have h' : ((CFSG.F4.Native.hermC p0 (P.headD 0) == 0 ||
        (w.all (fun j => decide (j < 693) && fldR R j 0 == 0) && wordR R w l == 1)) &&
        pairWK R p0 W P.tail (l + 1)) = true := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h'
    rcases i with _ | i
    · have hP0 : P.getD 0 0 = P.headD 0 := by cases P <;> rfl
      simp only [List.getD_cons_zero, add_zero, hP0]
      exact h'.1
    · have e := pairWK_get W P.tail (l + 1) h'.2 i (by simpa using hi)
      rw [List.getD_cons_succ, show l + (i + 1) = l + 1 + i by omega,
        show P.getD (i + 1) 0 = P.tail.getD i 0 by
          cases P <;> simp]
      exact e

theorem arr_getD {α : Type} [Inhabited α] (A : Array α) (i : Nat) :
    A[i]! = A.toList.getD i default := by
  rcases A with ⟨l⟩
  simp [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem chkPtWords_of {R : Nat → Nat}
    (hb : ∀ j < 693, ∀ b < 693, ptImg j b = fldR R j b ∧ fldR R j b < 693)
    (hl : ptWords.toList.length = 693) (h : ptWK R ptWords.toList 0 = true) :
    chkPtWords = true := by
  unfold chkPtWords
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  intro a ha
  obtain ⟨h1, h2⟩ := ptWK_get _ 0 h a (by omega)
  rw [arr_getD]
  refine ⟨List.all_eq_true.1 h1, ?_⟩
  rw [wordImg_eq hb _ a ha, ← h2, zero_add]
  · rfl
  · intro j hj
    have := List.all_eq_true.1 h1 j hj
    simpa using this

theorem chkPairWords_of {R : Nat → Nat} {P : List Nat}
    (hb : ∀ j < 693, ∀ b < 693, ptImg j b = fldR R j b ∧ fldR R j b < 693)
    (hP : uPts () = P.toArray) (hl : pairWords.toList.length = 693)
    (h : pairWK R (P.getD 0 0) pairWords.toList P 0 = true) : chkPairWords = true := by
  unfold chkPairWords
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  intro l hl'
  rw [hP, getElem!_toArray, getElem!_toArray, arr_getD]
  rcases pairWK_get _ _ 0 h l (by omega) with e | ⟨h1, h2⟩
  · exact Or.inl e
  · refine Or.inr ⟨?_, ?_⟩
    · intro j hj
      have := List.all_eq_true.1 h1 j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      exact ⟨decide_eq_true this.1, by rw [(hb j this.1 0 (by norm_num)).1]; exact this.2⟩
    · rw [wordImg_eq hb _ l hl', ← h2, zero_add]
      · rfl
      · intro j hj
        have := List.all_eq_true.1 h1 j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1

theorem planeWK_get {TC : List Nat} {w0 : Nat} : ∀ (W : List (List Nat)) (V : List Nat),
    planeWK TC w0 W V = true → ∀ i < W.length,
      (W.getD i []).all (fun k => decide (k < 693)) = true ∧ vwalk TC (W.getD i []) (V.getD i 0) = w0
  | [], _, _, i, hi => absurd hi (by simp)
  | w :: W, V, h, i, hi => by
    have h' : ((w.all (fun k => decide (k < 693)) && vwalk TC w (V.headD 0) == w0) &&
        planeWK TC w0 W V.tail) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    rcases i with _ | i
    · have hV0 : V.getD 0 0 = V.headD 0 := by cases V <;> rfl
      simp only [List.getD_cons_zero, hV0]
      exact h'.1
    · have e := planeWK_get W V.tail h'.2 i (by simpa using hi)
      rw [List.getD_cons_succ, show V.getD (i + 1) 0 = V.tail.getD i 0 by cases V <;> simp]
      exact e

theorem planeWordImg_eq {TC : List Nat}
    (hA : ∀ k < 693, ∀ i < 891, planeImg k i < 891 ∧
      wtArr[planeImg k i]! = applyCols tvArr[k]! wtArr[i]!)
    (hC : ∀ k < 693, ∀ v, fld k (c8ap TC v) = applyCols tvArr[k]! v) :
    ∀ (w : List Nat) (i : Nat), i < 891 → (∀ k ∈ w, k < 693) →
      planeWordImg w i < 891 ∧ wtArr[planeWordImg w i]! = vwalk TC w wtArr[i]! := by
  intro w
  induction w with
  | nil =>
    intro i hi _
    unfold planeWordImg vwalk
    rw [List.foldl_nil, List.foldl_nil]
    exact ⟨hi, rfl⟩
  | cons k w ih =>
    intro i hi hw
    have hk := hw k List.mem_cons_self
    obtain ⟨h1, h2⟩ := hA k hk i hi
    have e := ih _ h1 fun j hj => hw j (List.mem_cons_of_mem _ hj)
    unfold planeWordImg vwalk at e ⊢
    rw [List.foldl_cons, List.foldl_cons, hC k hk, ← h2]
    exact e

theorem chkPlaneWords_of {TC V : List Nat} (hW : chkW = true) (hT : chkT = true)
    (hC : ∀ k < 693, ∀ v, fld k (c8ap TC v) = applyCols tvArr[k]! v)
    (hV : ∀ i < 891, V.getD i 0 = wtArr[i]!) (hl : planeWords.toList.length = 891)
    (h : planeWK TC (V.getD 0 0) planeWords.toList V = true) : chkPlaneWords = true := by
  have hidx : ∀ j < 891, wtIdx[wtArr[j]!]! = j := by
    unfold chkW at hW
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hW
    exact hW.1.1
  have hA : ∀ k < 693, ∀ i < 891, planeImg k i < 891 ∧
      wtArr[planeImg k i]! = applyCols tvArr[k]! wtArr[i]! := by
    intro k hk i hi
    unfold chkT at hT
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hT
    obtain ⟨⟨h1, h2⟩, -⟩ := hT k hk i hi
    exact ⟨h1, h2⟩
  unfold chkPlaneWords
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  intro i hi
  obtain ⟨h1, h2⟩ := planeWK_get _ _ h i (by omega)
  rw [arr_getD]
  refine ⟨List.all_eq_true.1 h1, ?_⟩
  have hw : ∀ k ∈ planeWords.toList.getD i default, k < 693 := by
    intro k hk
    have := List.all_eq_true.1 h1 k hk
    simpa using this
  obtain ⟨hlt, he⟩ := planeWordImg_eq hA hC _ i hi hw
  rw [hV i hi, hV 0 (by norm_num)] at h2
  have e : wtArr[planeWordImg (planeWords.toList.getD i default) i]! = wtArr[0]! := by
    rw [he]
    exact h2
  rw [← hidx _ hlt, e, hidx 0 (by norm_num)]

end CFSG.SmithE.K
