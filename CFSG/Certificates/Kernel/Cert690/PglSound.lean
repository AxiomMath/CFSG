module

public import Certificates.Data.Kernel.Cert690.Pgl
public import CFSG.Certificates.Kernel.Cert690.CBaseSound
public import CFSG.Certificates.Kernel.Cert690.BfsSound
public import CFSG.Certificates.Kernel.Cert690.TreeSound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

theorem firstMap_spec (f : ℕ → ℕ) : ∀ n,
    (∀ y, ((List.range n).foldl (fun (m : Std.HashMap ℕ ℕ) i =>
        if m.contains (f i) then m else m.insert (f i) i) {}).contains y =
      (List.range n).any (fun i => f i == y)) ∧
    ∀ y d, ((List.range n).foldl (fun (m : Std.HashMap ℕ ℕ) i =>
        if m.contains (f i) then m else m.insert (f i) i) {}).getD y d =
      ((List.range n).find? (fun i => f i == y)).getD d
  | 0 => ⟨fun y => by simp, fun y d => by simp⟩
  | n + 1 => by
    obtain ⟨hc, hg⟩ := firstMap_spec f n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun (m : Std.HashMap ℕ ℕ) i =>
      if m.contains (f i) then m else m.insert (f i) i) {} = m at hc hg
    have hany1 : ∀ y, (List.range n ++ [n]).any (fun i => f i == y) =
        ((List.range n).any (fun i => f i == y) || (f n == y)) := fun y => by simp
    have hfind1 : ∀ y, (List.range n ++ [n]).find? (fun i => f i == y) =
        ((List.range n).find? (fun i => f i == y)).or
          (if f n = y then some n else none) := fun y => by
      rw [List.find?_append]
      by_cases hy : f n = y <;> simp [hy]
    have hnone : ∀ y, (List.range n).any (fun i => f i == y) = false →
        (List.range n).find? (fun i => f i == y) = none := fun y h => by
      rw [List.find?_eq_none]
      intro x hx
      have := List.any_eq_false.1 h x hx
      simpa using this
    have hsome : ∀ y, (List.range n).find? (fun i => f i == y) = none →
        (List.range n).any (fun i => f i == y) = false := fun y h => by
      rw [List.find?_eq_none] at h
      rw [List.any_eq_false]
      intro x hx
      simpa using h x hx
    refine ⟨fun y => ?_, fun y d => ?_⟩
    · rw [hany1]
      by_cases hm : m.contains (f n) = true
      · rw [if_pos hm, hc]
        by_cases hy : f n = y
        · subst hy
          rw [← hc, hm]
          rfl
        · simp [hy]
      · rw [if_neg hm, Std.HashMap.contains_insert, hc, Bool.or_comm]
    · rw [hfind1]
      by_cases hm : m.contains (f n) = true
      · rw [if_pos hm, hg]
        cases hfr : (List.range n).find? (fun i => f i == y) with
        | some i => rfl
        | none =>
          have hy : f n ≠ y := by
            intro e
            subst e
            have := hsome _ hfr
            rw [← hc, hm] at this
            exact absurd this (by simp)
          rw [if_neg hy]
          rfl
      · rw [if_neg hm, Std.HashMap.getD_insert, hg]
        by_cases hy : f n = y
        · subst hy
          have hfr : (List.range n).find? (fun i => f i == f n) = none :=
            hnone _ (by rw [← hc]; simpa using hm)
          rw [hfr, if_pos rfl, if_pos (by simp)]
          rfl
        · rw [if_neg (by simpa using hy), if_neg hy]
          cases (List.range n).find? (fun i => f i == y) <;> rfl

theorem firstMap_getD (f : ℕ → ℕ) (n y d : ℕ) :
    ((List.range n).foldl (fun (m : Std.HashMap ℕ ℕ) i =>
        if m.contains (f i) then m else m.insert (f i) i) {}).getD y d =
      ((List.range n).find? (fun i => f i == y)).getD d :=
  (firstMap_spec f n).2 y d

theorem lookup_zip_getElem {E V : List ℕ} (hE : E.Nodup) (hl : V.length = E.length) {i : ℕ}
    (hi : i < E.length) : (E.zip V).lookup E[i] = some V[i] := by
  induction E generalizing V i with
  | nil => simp at hi
  | cons x E ih =>
    cases V with
    | nil => simp at hl
    | cons v V =>
      simp only [List.zip_cons_cons, List.length_cons, Nat.add_right_cancel_iff] at hl ⊢
      rw [List.nodup_cons] at hE
      cases i with
      | zero => simp [lookup_cons']
      | succ i =>
        have hi' : i < E.length := by simpa using hi
        have hne : E[i] ≠ x := fun e => hE.1 (e ▸ List.getElem_mem hi')
        simp only [List.getElem_cons_succ]
        rw [lookup_cons', if_neg hne]
        exact ih hE.2 hl hi'

theorem lookup_zip_none {E V : List ℕ} {c : ℕ} (hc : c ∉ E) : (E.zip V).lookup c = none :=
  lookup_none fun a ha => fun e => hc (e ▸ (List.of_mem_zip ha).1)

theorem invMapOf_getD {E V : List ℕ} (hE : E.Nodup) (hl : V.length = E.length) (c d : ℕ) :
    (invMapOf E.toArray V.toArray).getD c d = lookD E V c d := by
  unfold invMapOf lookD
  have key : ∀ k ≤ E.length, ((List.range k).foldl
      (fun m i => m.insert (E.toArray[i]!) (V.toArray[i]!)) ({} : Std.HashMap ℕ ℕ)).getD c d =
      if c ∈ E.take k then V.getD (E.idxOf c) d else d := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < E.length := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getD_insert, ih (by omega), List.getElem!_toArray, List.getElem!_toArray,
        getElem!_pos E k hk', getElem!_pos V k (by rw [hl]; exact hk')]
      have htk : E.take (k + 1) = E.take k ++ [E[k]] := by
        rw [List.take_succ, List.getElem?_eq_getElem hk']
        rfl
      by_cases h : E[k] = c
      · subst h
        have hm : E[k] ∈ E.take (k + 1) := by
          rw [htk]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        rw [if_pos (by simp), if_pos hm, hE.idxOf_getElem k hk',
          List.getD_eq_getElem _ _ (by rw [hl]; exact hk')]
      · rw [if_neg (by simpa using h)]
        have e : (c ∈ E.take (k + 1)) ↔ (c ∈ E.take k) := by
          rw [htk, List.mem_append, List.mem_singleton]
          exact ⟨fun h' => h'.resolve_right (fun e => h e.symm), Or.inl⟩
        by_cases hc : c ∈ E.take k
        · rw [if_pos hc, if_pos (e.2 hc)]
        · rw [if_neg hc, if_neg (fun h' => hc (e.1 h'))]
  rw [List.size_toArray, key E.length le_rfl, List.take_length]
  by_cases hc : c ∈ E
  · rw [if_pos hc]
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    rw [lookup_zip_getElem hE hl hi, hE.idxOf_getElem i hi,
      List.getD_eq_getElem _ _ (by rw [hl]; exact hi)]
    rfl
  · rw [if_neg hc, lookup_zip_none hc]
    rfl

theorem idxMapOf_getD' {C : Array ℕ} (h : C.toList.Nodup) (x : ℕ) :
    (idxMapOf C).getD x C.size = C.toList.idxOf x := by
  have := idxMapOf_getD h x
  rwa [Array.toArray_toList, Array.length_toList] at this

theorem mulIdxTable_eq {C : Array ℕ} (h : C.toList.Nodup) :
    mulIdxTable C (idxMapOf C) = mulIdxTableK C := by
  unfold mulIdxTable mulIdxTableK
  simp only [idxMapOf_getD' h, mul_eq_mulF]

theorem conjIdxTable_eq {C : Array ℕ} (h : C.toList.Nodup) (K invK : Array ℕ) :
    conjIdxTable C K invK (idxMapOf C) = conjIdxTableK C K invK := by
  unfold conjIdxTable conjIdxTableK
  simp only [idxMapOf_getD' h, mul_eq_mulF]

theorem centralMaskTable_eq (C K : Array ℕ) : centralMaskTable C K = centralMaskTableK C K := by
  unfold centralMaskTable centralMaskTableK
  simp only [mul_eq_mulF]

theorem codePow_go_eq (a : ℕ) : ∀ n acc, codePow.go a n acc = powGoF a n acc
  | 0, _ => rfl
  | n + 1, acc => by rw [codePow.go, powGoF, mul_eq_mulF, codePow_go_eq a n]

theorem pow2K_eq (a : ℕ) : pow2K a = pow2F a := by
  unfold pow2K pow2F codePow
  rw [codePow_go_eq, one_eq_oneF]

theorem isInvCode_eq (x : ℕ) : isInvCode x = isInvF x := by
  unfold isInvCode isInvF
  rw [mul_eq_mulF, one_eq_oneF]

theorem array_map_eq {α β : Type} (f : α → β) (A : Array α) : A.map f = (A.toList.map f).toArray := by
  cases A
  simp

theorem testBit_badMaskK (B : Array Bool) : ∀ n i,
    (badMaskK B n).testBit i = (decide (i < n) && !B[i]!)
  | 0, i => by simp [badMaskK]
  | n + 1, i => by
    have ih := testBit_badMaskK B n i
    unfold badMaskK at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split
    · rename_i hb
      rw [ih]
      by_cases hi : i = n
      · subst hi
        simp [hb]
      · have : (decide (i < n + 1)) = decide (i < n) := by
          by_cases h' : i < n <;> simp [h'] <;> omega
        rw [this]
    · rename_i hb
      have h1 : Nat.testBit 1 (i - n) = decide (i - n = 0) := by
        rw [Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero, decide_eq_true_iff]
      rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft, h1]
      by_cases hi : i = n
      · subst hi
        simp [hb]
      · by_cases h' : i < n
        · simp [h', hi, show i < n + 1 by omega]
        · have : ¬ i < n + 1 := by omega
          simp only [h', this, decide_false, Bool.false_and, Bool.false_or, Bool.and_eq_false_iff,
            decide_eq_false_iff_not]
          right
          omega

theorem maskAllTrue_eq (B : Array Bool) (m n : ℕ) :
    maskAllTrue B m n = (m &&& badMaskK B n == 0) := by
  unfold maskAllTrue
  rw [Bool.eq_iff_iff, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, testBit_badMaskK, Nat.zero_testBit]
    by_cases hi : i < n
    · have := h i (List.mem_range.2 hi)
      cases hm : m.testBit i <;> cases hb : B[i]! <;> simp_all
    · simp [hi]
  · intro h i hi
    have := congrArg (fun x => Nat.testBit x i) h
    simp only [Nat.testBit_and, testBit_badMaskK, Nat.zero_testBit, decide_eq_true
      (List.mem_range.1 hi), Bool.true_and] at this
    cases hm : m.testBit i <;> cases hb : B[i]! <;> simp_all

theorem and_comm_beq0 (x : Bool) (a b : ℕ) : (x && (a &&& b == 0)) = ((a &&& b == 0) && x) :=
  Bool.and_comm _ _

theorem and_comm_beq0' (x y z : Bool) (a b : ℕ) :
    ((x && y && (a &&& b == 0)) && z) = ((a &&& b == 0) && (x && y && z)) := by
  cases x <;> cases y <;> cases z <;> simp

theorem filter_size (A : Array ℕ) (p : ℕ → Bool) : (A.filter p).size = (A.toList.filter p).length := by
  rw [← Array.length_toList, Array.toList_filter]

theorem nodup_filter {E : Array ℕ} (h : E.toList.Nodup) (p : ℕ → Bool) :
    (E.filter p).toList.Nodup := by
  rw [Array.toList_filter]
  exact h.filter p

theorem invArr_eq (E : List ℕ) : invArr E.toArray = (invsL E).toArray := by
  unfold invArr invsL
  simp only [List.map_toArray, List.size_toArray, codeInv_eq]

theorem invArr_eq' (C : Array ℕ) : invArr C = (invsL C.toList).toArray := by
  rw [← invArr_eq, Array.toArray_toList]

section

variable {K K0 : List ℕ} {P P0 : List (ℕ × ℕ)}
  (hK : enumData kPGLGens = (K.toArray, P.toArray))
  (hK0 : enumData kPGL0Gens = (K0.toArray, P0.toArray))
include hK hK0

theorem pgl_elems : (pglData ()).elems = K.toArray := by unfold pglData; rw [hK]

theorem pgl_par : (pglData ()).par = P.toArray := by unfold pglData; rw [hK]

theorem pgl_elems0 : (pglData ()).elems0 = K0.toArray := by unfold pglData; rw [hK0]

theorem pgl_par0 : (pglData ()).par0 = P0.toArray := by unfold pglData; rw [hK0]

theorem pgl_invs : (pglData ()).invs = (invsL K).toArray := by
  simp only [pglData, hK, invArr_eq]

theorem pgl_invs0 : (pglData ()).invs0 = (invsL K0).toArray := by
  simp only [pglData, hK0, invArr_eq]

theorem pgl_invMap (hnd : K.Nodup) (g d : ℕ) :
    (pglData ()).invMap.getD g d = lookD K (invsL K) g d := by
  have e : (pglData ()).invMap = invMapOf K.toArray (invsL K).toArray := by
    simp only [pglData, hK, invArr_eq]
  rw [e, invMapOf_getD hnd (by simp [invsL])]

theorem pgl_involutions : (pglData ()).involutions = (involL K).toArray := by
  simp only [pglData, hK, invsOf, involL, List.filter_toArray, isInvCode_eq]

theorem pgl_outers : (pglData ()).outers = (outersL K K0).toArray := by
  simp only [pglData, hK, hK0, invsOf, outersL, involL, List.filter_toArray, isInvCode_eq,
    List.contains_toArray]

theorem pgl_commWit : (pglData ()).commWit = (commWitL K).toArray := by
  simp only [pglData, hK, invArr_eq, commWitL, findCommutator, findCommK, List.size_toArray,
    List.getElem!_toArray, mul_eq_mulF]

theorem pgl_w9 : (pglData ()).w9 = w9K K := by
  simp only [pglData, hK, w9K, List.size_toArray, List.getElem!_toArray, act_eq_actF]
  congr 1
  funext v
  split
  · rfl
  · rw [firstMap_getD (fun i => actF K[i]! 2)]

theorem pgl_w12 : (pglData ()).w12 = (w12L K K0).toArray := by
  simp only [pglData, hK, hK0, invArr_eq, w12L, List.size_toArray, List.getElem!_toArray,
    mul_eq_mulF, invsOf, List.filter_toArray, List.filter_toArray', isInvCode_eq,
    List.contains_toArray, array_map_eq, List.toList_toArray, outersL, involL]
  congr 1
  apply List.map_congr_left
  intro u _
  rw [firstMap_getD (fun i => mulF (mulF K[i]! (List.filter (fun u => !K0.contains u)
    (List.filter isInvF K))[0]!) (invsL K)[i]!)]

end

section

variable (D : PGLData)

theorem pglF1Of_eq : pglF1Of D = (enumOK kPGLGens D.elems D.par &&
    enumOK kPGL0Gens D.elems0 D.par0 && pglF1K D.elems D.invs D.elems0 D.invs0) := by
  unfold pglF1Of pglF1K
  simp only [mul_eq_mulF, one_eq_oneF, Bool.and_assoc]

theorem pglF4Of_eq {iv : ℕ → ℕ} (hiv : ∀ g, D.invMap.getD g 0 = iv g) :
    pglF4Of D = pglF4K D.elems D.elems0 D.invs iv D.commWit := by
  unfold pglF4Of pglF4K
  simp only [hiv, mul_eq_mulF, one_eq_oneF, ← Array.all_toList, ← Array.contains_toList]
  rfl

theorem pglF5Of_eq : pglF5Of D = pglF5K D.f5Wit := rfl

theorem pglF6Of_eq : pglF6Of D = pglF6K := by
  unfold pglF6Of pglF6K mapsInto mapsIntoK
  simp only [act_eq_actF]

theorem pglF7Of_eq : pglF7Of D = pglF7K D.elems D.elems0 := by
  unfold pglF7Of pglF7K mapsIntoList mapsIntoListK
  simp only [act_eq_actF, ← Array.all_toList, ← Array.contains_toList]

theorem spanArr_eq (S : List ℕ) : spanArr S = spanK S := by
  unfold spanArr spanK
  simp only [← Array.contains_toList, array_map_eq]

theorem pglF8Of_eq : pglF8Of D = pglF8K D.elems0 := by
  unfold pglF8Of pglF8K sameSet sameSetK
  simp only [act_eq_actF, array_map_eq, spanArr_eq, ← Array.all_toList, ← Array.contains_toList]

theorem pglF9Of_eq : pglF9Of D = pglF9K D.elems D.w9 := by
  unfold pglF9Of pglF9K
  simp only [act_eq_actF]

theorem pglInvolutionsOK_eq : pglInvolutionsOK D = pglInvolutionsK D.elems D.involutions := by
  unfold pglInvolutionsOK pglInvolutionsK
  simp only [isInvCode_eq, ← Array.all_toList, ← Array.contains_toList]

theorem pglOutersOK_eq : pglOutersOK D = pglOutersK D.elems D.elems0 D.outers := by
  unfold pglOutersOK pglOutersK
  simp only [isInvCode_eq, ← Array.all_toList, ← Array.contains_toList]

theorem pglF10Of_eq (hnd : D.elems.toList.Nodup) : pglF10Of D = pglF10K D.elems D.invs := by
  unfold pglF10Of pglF10K f10At f10Vecs
  simp only [mulIdxTable_eq (nodup_filter hnd _), conjIdxTable_eq (nodup_filter hnd _),
    idxMapOf_getD' (nodup_filter hnd _), centralMaskTable_eq, pow2K_eq, array_map_eq,
    act_eq_actF, mul_eq_mulF, one_eq_oneF, card_hashSet, maskAllTrue_eq, ← Array.all_toList,
    ← Array.any_toList, ← Array.contains_toList]
  simp only [and_comm_beq0]

theorem pglF11Of_eq (hnd : D.elems.toList.Nodup) :
    pglF11Of D = pglF11K D.elems D.elems0 D.outers := by
  unfold pglF11Of pglF11K f11At
  simp only [pglOutersOK_eq, mulIdxTable_eq (nodup_filter hnd _),
    conjIdxTable_eq (nodup_filter hnd _), idxMapOf_getD' (nodup_filter hnd _), pow2K_eq,
    array_map_eq, invArr_eq', mul_eq_mulF, one_eq_oneF, card_hashSet, maskAllTrue_eq,
    ← Array.all_toList, ← Array.any_toList, ← Array.contains_toList]
  simp only [and_comm_beq0']

theorem pglF12Of_eq :
    pglF12Of D = pglF12K D.elems D.elems0 D.invs D.involutions D.outers D.w12 := by
  unfold pglF12Of pglF12K
  simp only [pglInvolutionsOK_eq, pglOutersOK_eq, mul_eq_mulF]

theorem pglF13Of_eq : pglF13Of D = pglF13K D.elems D.elems0 := by
  unfold pglF13Of pglF13K
  simp only [← Array.all_toList]
  simp only [filter_size, Array.toList_filter, act_eq_actF, mul_eq_mulF, one_eq_oneF]

end

end CFSG.KC.C690

end
