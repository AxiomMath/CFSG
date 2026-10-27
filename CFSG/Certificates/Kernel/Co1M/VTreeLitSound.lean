module

public import CFSG.Certificates.Kernel.J4Q.RepVOrb
public import Certificates.Data.Kernel.Co1M.VTreeLit
import CFSG.Certificates.Kernel.J4Q.VOrbTree

public section

namespace CFSG.KC.Co1M

open CFSG.KC.J4Q CFSG.KC.LQT.Syl CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.OddCentNative


private theorem andB_true (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem dropK_eq : ∀ (n : Nat) (l : List Nat), dropK n l = l.drop n
  | 0, l => rfl
  | n + 1, l => by
    change List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) (dropK n l) = _
    rw [dropK_eq n l, ← List.tail_drop]
    cases l.drop n <;> rfl

private theorem headK_drop (n : Nat) (l : List Nat) : headK (l.drop n) = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases l.drop n <;> rfl

private theorem vtGo_sound (rm : Nat) (Rs : List (List Nat)) (P : List Nat) :
    ∀ (ch : List Nat) (ci k : Nat), vtGo rm Rs ch (P.drop ci) ci k = true →
      ∀ j < ch.length, Nat.shiftRight (ch.getD j 0) 114 < k + j ∧
        Nat.land (Nat.shiftRight (ch.getD j 0) 112) 3 < Rs.length ∧
        vecLJ (P.getD (Nat.shiftRight (ch.getD j 0) 114) 0)
          (Rs.getD (Nat.land (Nat.shiftRight (ch.getD j 0) 112) 3) []) = Nat.land (ch.getD j 0) rm
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | e :: ch, ci, k, h, j, hj => by
    change andB (Nat.ble ci (Nat.shiftRight e 114)) (andB (Nat.blt (Nat.shiftRight e 114) k)
      (andB (Nat.blt (Nat.land (Nat.shiftRight e 112) 3) Rs.length)
        (andB (Nat.beq (vecLJ (headK (dropK (Nat.shiftRight e 114 - ci) (P.drop ci)))
          (Rs.getD (Nat.land (Nat.shiftRight e 112) 3) [])) (Nat.land e rm))
          (vtGo rm Rs ch (dropK (Nat.shiftRight e 114 - ci) (P.drop ci)) (Nat.shiftRight e 114)
            (k + 1))))) = true at h
    simp only [andB_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hd : dropK (Nat.shiftRight e 114 - ci) (P.drop ci) = P.drop (Nat.shiftRight e 114) := by
      rw [dropK_eq, List.drop_drop, Nat.add_sub_cancel' h1]
    rw [hd] at h4 h5
    cases j with
    | zero =>
      refine ⟨by simpa using h2, h3, ?_⟩
      rw [← headK_drop]
      exact h4
    | succ j =>
      obtain ⟨ha, hb, hc⟩ := vtGo_sound rm Rs P ch _ (k + 1) h5 j (by simpa using hj)
      exact ⟨by simp only [List.getD_cons_succ]; omega, hb, hc⟩

private theorem flatten_index {B : Nat} : ∀ {chs : List (List Nat)},
    (∀ i, i + 1 < chs.length → (chs.getD i []).length = B) →
    ∀ t < chs.flatten.length, ∃ i < chs.length, ∃ j < (chs.getD i []).length,
      t = B * i + j ∧ chs.flatten.getD t 0 = (chs.getD i []).getD j 0
  | [], _, t, ht => by simp at ht
  | c :: cs, hB, t, ht => by
    rw [List.flatten_cons, List.length_append] at ht
    by_cases htc : t < c.length
    · refine ⟨0, by simp, t, by simpa using htc, by simp, ?_⟩
      rw [List.flatten_cons, List.getD_append _ _ _ _ htc]
      rfl
    · have hcs : cs ≠ [] := by
        rintro rfl
        simp at ht
        omega
      have hcB : c.length = B := by
        have := hB 0 (by simpa using List.length_pos_of_ne_nil hcs)
        simpa using this
      obtain ⟨i, hi, j, hj, he, hg⟩ := flatten_index (chs := cs)
        (fun i hi => by simpa using hB (i + 1) (by simpa using hi)) (t - c.length) (by omega)
      refine ⟨i + 1, by simpa using hi, j, by simpa using hj, ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by omega)]
        simpa using hg

private theorem vecLFrom_eq (x : Nat) (g : Nat → Nat) : ∀ (rs : List Nat) (k acc : Nat),
    (∀ i < rs.length, rs.getD i 0 = g (k + i)) →
    vecLFrom x rs k acc =
      (List.range' k rs.length).foldl (fun acc j => if x.testBit j then acc ^^^ g j else acc) acc
  | [], _, _, _ => rfl
  | r :: t, k, acc, h => by
    have hr : r = g k := by simpa using h 0 (by simp)
    have ht : ∀ i < t.length, t.getD i 0 = g (k + 1 + i) := by
      intro i hi
      have := h (i + 1) (by simpa using hi)
      rw [List.getD_cons_succ] at this
      rw [this, Nat.add_right_comm, Nat.add_assoc]
    rw [List.length_cons, List.range'_succ, List.foldl_cons]
    have hst : vecLFrom x (r :: t) k acc =
        vecLFrom x t (k + 1) (if x.testBit k then acc ^^^ r else acc) := by
      change Bool.rec (motive := fun _ => Nat) (vecLFrom x t (k + 1) acc)
        (CFSG.KC.Loop.strictN (Nat.xor acc r) (vecLFrom x t (k + 1)))
        (Nat.beq (Nat.land (Nat.shiftRight x k) 1) 1) = _
      have hs : ∀ y, CFSG.KC.Loop.strictN y (vecLFrom x t (k + 1)) = vecLFrom x t (k + 1) y := by
        intro y
        cases y <;> rfl
      rw [hs]
      have hb : Nat.beq (Nat.land (Nat.shiftRight x k) 1) 1 = x.testBit k := by
        have hm : Nat.land (Nat.shiftRight x k) 1 = x / 2 ^ k % 2 := by
          change (x >>> k) &&& 1 = _
          rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
        rw [Nat.testBit_eq_decide_div_mod_eq, hm, Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
      rw [hb]
      cases x.testBit k <;> rfl
    rw [hst, vecLFrom_eq x g t (k + 1) _ ht, hr]


private theorem vecLJ_eq_vecMulN (R : Array Nat) (hR : R.size = 24) (x : Nat) :
    vecLJ x R.toList = vecMulN 24 R x := by
  change vecLFrom x R.toList 0 0 = _
  rw [vecLFrom_eq x (fun j : Nat => R[j]?.getD 0) R.toList 0 0 (fun i _ => by
    simp [List.getD_eq_getElem?_getD])]
  simp [vecMulN, hR, List.range_eq_range']

private theorem foldl_lt {f : Nat → Nat → Nat} {n : Nat} : ∀ (l : List Nat) (acc : Nat),
    acc < 2 ^ n → (∀ j ∈ l, ∀ a < 2 ^ n, f a j < 2 ^ n) → l.foldl f acc < 2 ^ n
  | [], _, h, _ => h
  | j :: l, acc, h, hf => foldl_lt l _ (hf j (by simp) acc h)
      (fun j' hj' => hf j' (List.mem_cons_of_mem _ hj'))

private theorem vecMulN_lt (R : Array Nat) (hR : ∀ j : Nat, R[j]?.getD 0 < 2 ^ 24) (v : Nat) :
    vecMulN 24 R v < 2 ^ 24 :=
  foldl_lt _ 0 (by decide) fun j _ a ha => by
    split
    · exact Nat.xor_lt_two_pow ha (hR j)
    · exact ha

private theorem transposeRows_lt (M : Array Nat) (j : Nat) :
    (transposeRows 24 M)[j]?.getD 0 < 2 ^ 24 := by
  by_cases hj : j < 24
  · have hget : (transposeRows 24 M)[j]? = some (ofBits 24 fun i => (M[i]?.getD 0).testBit j) := by
      simp [transposeRows, hj]
    rw [hget, Option.getD_some]
    refine foldl_lt _ 0 (by decide) fun i hi a ha => ?_
    split
    · refine Nat.or_lt_two_pow ha ?_
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.pow_lt_pow_right (by decide) (List.mem_range.1 hi)
    · exact ha
  · have hnone : (transposeRows 24 M)[j]? = none := by
      simp [transposeRows]
      omega
    rw [hnone]
    decide

private theorem strictInc_of_pairwise : ∀ {l : List Nat}, l.Pairwise (· < ·) → strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    have hab : a < b := List.rel_of_pairwise_cons h (by simp)
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨hab, strictInc_of_pairwise h.of_cons⟩

private theorem distinctKeys_of_nodup {l : List Nat} (h : l.Nodup) : distinctKeys l = true := by
  have hp := List.mergeSort_perm l keyLe
  have hs : (l.mergeSort keyLe).Pairwise (fun a b => keyLe a b = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by
      simp only [keyLe, decide_eq_true_iff] at *
      omega) (fun a b => by simp only [keyLe, Bool.or_eq_true, decide_eq_true_iff]; omega) l
  have hn : (l.mergeSort keyLe).Nodup := hp.nodup_iff.2 h
  refine strictInc_of_pairwise ((hs.and hn).imp fun ⟨hab, hne⟩ => ?_)
  simp only [keyLe, decide_eq_true_iff] at hab
  omega

private theorem toArray_getElem! (l : List Nat) (i : Nat) : l.toArray[i]! = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, getElem!_def]
  cases l[i]? <;> rfl

theorem vtLit_size (rm root : Nat) (EN : List Nat) :
    (vtLit rm root EN).pts.size = EN.length + 1 := by
  simp [vtLit, vptsK]

theorem vtLit_sound {Gr : Array (Array Nat)} {Rs : List (List Nat)} {rm : Nat}
    (_hrm : rm = 2 ^ 112 - 1) (_hR : Rs = Gr.toList.map fun M => (transposeRows 24 M).toList)
    (_hv : ∀ M ∈ Gr.toList, validRows M = true) (_hs : Gr.size * 1024 ≤ 131072)
    {root : Nat} (_hroot : root < 2 ^ 24)
    {chs : List (List Nat)} {p0s : List Nat} {SPch : List (List Nat)}
    (_hchs : ∀ i, i + 1 < chs.length → (chs.getD i []).length = 1024)
    (_hlast : ∀ ch ∈ chs, ch.length ≤ 1024)
    (_htree : ∀ i < chs.length, vtChunkK rm Rs (vptsK rm root chs.flatten) (chs.getD i [])
      (p0s.getD i 0) (1 + 1024 * i) = true)
    (_hsinc : sincK SPch.flatten 0 = true) (_hsl : SPch.flatten.length = chs.flatten.length + 1)
    (_hspl : ∀ sc ∈ SPch, sc.length ≤ 1024)
    (_hin : ∀ pc ∈ pchK rm root chs, inSK pc SPch.flatten = true)
    (_hsp : ∀ sc ∈ SPch, spInK sc (pchK rm root chs) = true) :
    vtreeOK Gr root (vtLit rm root chs.flatten) = true := by
  set A := vptsK rm root chs.flatten with hA
  have hAP : (pchK rm root chs).flatten = A := by
    simp only [pchK, List.flatten_cons, List.singleton_append, hA, vptsK, List.map_flatten]
  have hAl : A.length = chs.flatten.length + 1 := by
    rw [hA, vptsK, List.length_cons, List.length_map]
  have hnd : A.Nodup := by
    have hpts := VOrbTree.checked_points_spec (Pch := pchK rm root chs)
      (cap := chs.flatten.length + 1) (by rw [hAP, hAl]) _hsl _hsinc _hsp
    rw [hAP] at hpts
    exact hpts.2.1
  set Gt := Gr.map (transposeRows 24) with hGtd
  have hRl : Rs.length = Gr.size := by simp [_hR]
  have hGt : ∀ l (hl : l < Gr.size), Gt[l]! = transposeRows 24 Gr[l] := by
    intro l hl
    rw [getElem!_pos Gt l (by simpa [Gt] using hl)]
    simp [Gt]
  have hRg : ∀ l < Gr.size, Rs.getD l [] = (Gt[l]!).toList := by
    intro l hl
    rw [hGt l hl, List.getD_eq_getElem _ _ (by omega)]
    simp [_hR]
  have htr : ∀ k, k < chs.flatten.length →
      Nat.shiftRight (chs.flatten.getD k 0) 114 < k + 1 ∧
      Nat.land (Nat.shiftRight (chs.flatten.getD k 0) 112) 3 < Gr.size ∧
      Nat.land (chs.flatten.getD k 0) rm = vecMulN 24 Gt[Nat.land (Nat.shiftRight (chs.flatten.getD k 0) 112) 3]!
        (A.getD (Nat.shiftRight (chs.flatten.getD k 0) 114) 0) := by
    intro k hk
    obtain ⟨i, hi, j, hj, hkij, hg⟩ := flatten_index _hchs k hk
    have ht := _htree i hi
    unfold vtChunkK at ht
    rw [dropK_eq] at ht
    obtain ⟨h1, h2, h3⟩ := vtGo_sound rm Rs _ _ _ _ ht j hj
    rw [← hg] at h1 h2 h3
    refine ⟨by omega, by omega, ?_⟩
    rw [← h3, hRg _ (by omega), vecLJ_eq_vecMulN _ (by rw [hGt _ (by omega)]; simp [transposeRows])]
  have hlt : ∀ l < Gr.size, ∀ j : Nat, (Gt[l]!)[j]?.getD 0 < 2 ^ 24 := by
    intro l hl j
    rw [hGt l hl]
    exact transposeRows_lt _ j
  have hAk : ∀ k, k < chs.flatten.length → A.getD (k + 1) 0 = Nat.land (chs.flatten.getD k 0) rm := by
    intro k hk
    rw [hA, vptsK, List.getD_cons_succ, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk),
      List.getD_eq_getElem _ _ hk, List.getElem_map]
  set T := vtLit rm root chs.flatten with hT
  have hTs : T.pts.size = A.length := by rw [hT, vtLit, List.size_toArray]
  have h0 : decide (0 < T.pts.size) = true := by rw [hTs, hAl, decide_eq_true_iff]; omega
  have h1 : (T.par.size == T.pts.size) = true := by
    rw [hTs, hAl, beq_iff_eq, hT, vtLit, List.size_toArray, List.length_cons, List.length_map]
  have h2 : (T.lab.size == T.pts.size) = true := by
    rw [hTs, hAl, beq_iff_eq, hT, vtLit, List.size_toArray, List.length_cons, List.length_map]
  have h4 : distinctKeys T.pts.toList = true := by
    rw [hT, vtLit, List.toList_toArray, ← hA]
    exact distinctKeys_of_nodup hnd
  have h3 : (List.range T.pts.size).all (vtreePointOK Gt root T) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, hTs] at hi
    rw [hT, vtLit, ← hA]
    revert hi
    intro hi
    rw [hAl] at hi
    unfold vtreePointOK
    simp only [toArray_getElem!, Bool.and_eq_true, decide_eq_true_iff, Array.size_map]
    rcases i with _ | k
    · refine ⟨by rw [hA, vptsK]; simpa using _hroot, by simp [hA, vptsK]⟩
    · have hk : k < chs.flatten.length := by omega
      obtain ⟨h1, h2, h3⟩ := htr k hk
      have hpar : (0 :: chs.flatten.map fun e => Nat.shiftRight e 114).getD (k + 1) 0 =
          Nat.shiftRight (chs.flatten.getD k 0) 114 := by
        rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk),
          List.getD_eq_getElem _ _ hk, List.getElem_map]
      have hlab : (0 :: chs.flatten.map fun e => Nat.land (Nat.shiftRight e 112) 3).getD (k + 1) 0 =
          Nat.land (Nat.shiftRight (chs.flatten.getD k 0) 112) 3 := by
        rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk),
          List.getD_eq_getElem _ _ hk, List.getElem_map]
      rw [hAk k hk, hpar, hlab]
      refine ⟨?_, ?_⟩
      · rw [h3]
        exact vecMulN_lt _ (hlt _ h2) _
      · simp only [Nat.add_one_ne_zero, beq_iff_eq, if_false, Bool.and_eq_true,
          decide_eq_true_iff, beq_iff_eq]
        exact ⟨⟨h1, by rw [hGtd, Array.size_map]; exact h2⟩, h3⟩
  unfold vtreeOK
  rw [h0, h1, h2, h3, h4]
  rfl

end CFSG.KC.Co1M

end
