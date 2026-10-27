module

public import Certificates.Data.Kernel.M24G.Orbits
public import Certificates.Data.Kernel.M24G.TrioSexts
public import CFSG.Certificates.Kernel.M24G.ListChecksSound
public import CFSG.Certificates.Kernel.M24G.DualSound

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem getD_eq_getElem' {α : Type} {L : List α} {i : Nat} (d : α) (hi : i < L.length) :
    L.getD i d = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem getD_mem_of_lt {α : Type} [Inhabited α] {L : List α} {j : Nat} (hj : j < L.length) :
    L.getD j default ∈ L := by
  rw [getD_eq_getElem' _ hj]
  exact List.getElem_mem hj

theorem testBit_foldl_or : ∀ (L : List Nat) (acc q : Nat),
    (L.foldl (fun m x => m ||| (1 <<< x)) acc).testBit q = (acc.testBit q || L.contains q)
  | [], acc, q => by simp
  | x :: L, acc, q => by
    rw [List.foldl_cons, testBit_foldl_or L, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.contains_cons]
    by_cases h : x = q
    · subst h
      simp
    · have h' : (q == x) = false := beq_eq_false_iff_ne.2 (Ne.symm h)
      simp [h, h']

theorem testBit_maskL (L : List Nat) (q : Nat) : (maskL L).testBit q = L.contains q := by
  rw [maskL, testBit_foldl_or]
  simp

theorem contains_cls (n : Nat) (f : Nat → List Bool) (i : Nat) {q : Nat} (hq : q < n) :
    ((((List.range n).map fun p => (p, f p)).filter fun e => e.2.getD i false).map
      (·.1)).contains q = (f q).getD i false := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem]
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨e, ⟨⟨p, hp, rfl⟩, he⟩, rfl⟩
    exact he
  · intro h
    exact ⟨(q, f q), ⟨⟨q, hq, rfl⟩, h⟩, rfl⟩

theorem lookW_eq {α : Type} [Inhabited α] [BEq α] [LawfulBEq α] {n w : Nat} {enc : α → Nat}
    {dec : Nat → α} {L : List α} (h : lookOK n w enc dec L = true) :
    lookW n w enc dec L = fun i => L.getD i default := by
  unfold lookOK at h
  rw [Bool.and_eq_true, beq_iff_eq, allIdx_iff] at h
  funext i
  unfold lookW
  by_cases hi : i < n
  · rw [if_pos hi]
    have := h.2 i (h.1 ▸ hi)
    rw [Nat.zero_add, beq_iff_eq] at this
    exact this
  · rw [if_neg hi]

theorem reachOK_of_reachK {n : Nat} {steps : List (Nat → Nat)} {p : Nat} {c : List Nat}
    {r : List Nat × List Nat × List Nat} (h : reachK n steps p c r = true) :
    Native.reachOK n steps p c = true := by
  obtain ⟨L, par, gen⟩ := r
  unfold reachK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hr, hlt⟩, hc⟩ := h
  obtain ⟨-, hb, hpl, hgl, ht, -⟩ := replay_facts hr
  have hr' : replayOK (fun i : Nat => i) steps p 5000 L par gen (posTree id L) = true := hr
  unfold Native.reachOK
  rw [bfs_eq_of_replayOK hr']
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.size_toArray]
  have hL : 0 < L.length := by
    cases L with
    | nil => simp at hb
    | cons _ _ => simp
  refine ⟨⟨⟨⟨⟨hL, ?_⟩, hpl⟩, hgl⟩, ?_⟩, ?_⟩
  · cases L with
    | nil => simp at hb
    | cons x L =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      rw [toArray_getElem!_eq_getD, List.getD_cons_zero, hb]
  · unfold Native.allLt
    rw [range_all_iff]
    intro j hj
    simp only [toArray_getElem!_eq_getD, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq]
    refine ⟨of_decide_eq_true (List.all_eq_true.1 hlt _ (getD_mem_of_lt hj)), ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact Or.inl rfl
    · obtain ⟨q1, q2, q3⟩ := ht j hj0 hj
      refine Or.inr ⟨⟨q1, q2⟩, ?_⟩
      rw [getD_eq_getElem' _ hj]
      exact q3
  · rw [List.all_eq_true] at hc ⊢
    intro q hq
    have := hc q hq
    rw [testBit_maskL] at this
    rw [Bool.eq_iff_iff] at this ⊢
    simp only [List.contains_iff_mem, Array.contains_iff_mem, List.mem_toArray] at this ⊢
    exact this

theorem classOrbitCheck_of_classOrbitK {n : Nat} {cls : List (List Nat)} {sizes : List Nat}
    {steps : List (Nat → Nat)} {runs : List (List Nat × List Nat × List Nat)}
    (h : classOrbitK n cls sizes steps runs = true) :
    Native.classOrbitCheck n cls sizes steps = true := by
  unfold classOrbitK at h
  unfold Native.classOrbitCheck
  simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨⟨⟨h1, hr⟩, h2⟩, h3⟩ := h
  refine ⟨⟨h1, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at h2 ⊢
    intro p hp
    have e := h2 p hp
    rw [List.filter_map, List.length_map] at e
    have e' : (cls.filter fun c => c.contains p) = cls.filter fun c => (maskL c).testBit p :=
      List.filter_congr fun c _ => (testBit_maskL c p).symm
    rw [e']
    exact e
  · rw [List.all_eq_true] at h3 ⊢
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < ((cls.zip sizes).zip runs).length := by
      simp only [List.length_zip] at hi ⊢
      omega
    have e := h3 _ (List.getElem_mem hi')
    rw [List.getElem_zip] at e
    revert e
    generalize (cls.zip sizes)[i] = y
    obtain ⟨c, k⟩ := y
    intro e
    simp only [Bool.and_eq_true, beq_iff_eq] at e ⊢
    refine ⟨e.1, ?_⟩
    have e2 := e.2
    cases c with
    | nil => simp at e2
    | cons p c => exact reachOK_of_reachK e2

theorem trioItem_lt {t : Nat × Nat × Nat} (h : trioItem t = true) :
    ∀ x ∈ Native.octsT t, x < 2 ^ 24 := by
  unfold trioItem at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hlt : t.1 ||| t.2.1 ||| t.2.2 < 2 ^ 24 := by
    rw [h.2]
    decide
  intro x hx
  simp only [Native.octsT, List.mem_cons, List.not_mem_nil, or_false] at hx
  refine Nat.lt_pow_two_of_testBit x fun i hi => ?_
  have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hi))
  simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this
  rcases hx with rfl | rfl | rfl
  · exact this.1.1
  · exact this.1.2
  · exact this.2

theorem imgTrio_lt' {g : Array Nat} (hg : ∀ x ∈ g.toList, x < 24) (t : Nat × Nat × Nat) :
    ∀ x ∈ Native.octsT (Native.imgTrio g t), x < 2 ^ 24 := by
  intro x hx
  rcases mem_sort3 hx with rfl | rfl | rfl <;> exact img_lt hg _

theorem imgTrio_eq {g : Array Nat} (hg : ∀ x ∈ g.toList, x < 24) :
    Native.imgTrio g = imgTrioF g.toList := by
  funext x
  simp only [Native.imgTrio, imgTrioF, img_eq_imgF g hg]

theorem imgSext_eq {g : Array Nat} (hg : ∀ x ∈ g.toList, x < 24) :
    Native.imgSext g = imgSextF g.toList := by
  funext s
  have hf : Native.img g = imgF (imgTab g.toList) := funext (img_eq_imgF g hg)
  simp only [Native.imgSext, imgSextF, sortL_eq_sortN, hf]

theorem trioSteps_eq_trioStepsK {TL : List (Nat × Nat × Nat)}
    (hT : Native.trioList () = TL.toArray)
    (hpos : posOK Native.key3 TL (posTree Native.key3 TL) = true) (hTl : TL.length = 3795)
    (hTi : TL.all trioItem = true) {gs : List (Array Nat)}
    (hg : ∀ g ∈ gs, ∀ x ∈ g.toList, x < 24) :
    Native.trioSteps gs = trioStepsK TL (fun i => TL.getD i default) gs := by
  simp only [Native.trioSteps, trioStepsK]
  refine List.map_congr_left fun g hgs => ?_
  funext i
  rw [trioIdx_eq_idxNat, hT, toArray_getElem!_eq_getD,
    idxNat_eq_idxK hpos (by rw [hTl]; rfl) fun y hy e =>
      key3_inj (trioItem_lt (List.all_eq_true.1 hTi y hy)) (imgTrio_lt' (hg g hgs) _) e,
    imgTrio_eq (hg g hgs)]

theorem sextSteps_eq_sextStepsK {SL : List (List Nat)}
    (hS : Native.sextList () = SL.toArray)
    (hpos : posOK Native.keyL SL (posTree Native.keyL SL) = true) (hSl : SL.length = 1771)
    (hSi : SL.all sextItem = true) {gs : List (Array Nat)}
    (hg : ∀ g ∈ gs, ∀ x ∈ g.toList, x < 24) :
    Native.sextSteps gs = sextStepsK SL (fun i => SL.getD i default) gs := by
  simp only [Native.sextSteps, sextStepsK]
  refine List.map_congr_left fun g hgs => ?_
  funext i
  rw [hS, toArray_getElem!_eq_getD]
  by_cases hi : i < Native.nSext
  · rw [if_pos hi]
    have hi' : i < SL.length := by
      rw [hSl]
      exact hi
    obtain ⟨yl, yb⟩ := sextItem_facts (List.all_eq_true.1 hSi _ (getD_mem_of_lt hi'))
    have il : (Native.imgSext g (SL.getD i default)).length = 6 := by
      rw [Native.imgSext, length_sortL, List.length_map, yl]
    have ib : ∀ B ∈ Native.imgSext g (SL.getD i default), B < 2 ^ 24 := by
      intro B hB
      rw [Native.imgSext, mem_sortL, List.mem_map] at hB
      obtain ⟨b, -, rfl⟩ := hB
      exact img_lt (hg g hgs) _
    rw [sextIdx_eq_idxNat, hS, idxNat_eq_idxK hpos (by rw [hSl]; rfl) fun y hy e => by
      obtain ⟨zl, zb⟩ := sextItem_facts (List.all_eq_true.1 hSi y hy)
      exact keyL_inj y _ (by rw [zl, il]) zb ib e, imgSext_eq (hg g hgs)]
  · rw [if_neg hi]

theorem tsRows_lt {TL : List (Nat × Nat × Nat)} {SL : List (List Nat)} {TS : List (List Nat)}
    (h : tsRowsOK TL SL TS = true) {p : Nat} (hp : p < 3795) :
    ∀ q ∈ TS.getD p default, q < 1771 := by
  unfold tsRowsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hTl, hSl⟩, hr⟩ := h
  have hp' : p < (TL.zip TS).length := by
    rw [List.length_zip, hTl, hSl]
    omega
  have e := hr _ (List.getElem_mem hp')
  rw [List.getElem_zip] at e
  unfold tsRowOK at e
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at e
  intro q hq
  rw [getD_eq_getElem' _ (by omega)] at hq
  exact (e.2 q hq).1

theorem deltaCheck_eq : Native.deltaCheck () =
    deltaCkF (fun p => (Native.trioList ())[p]!) (fun p => (Native.trioSexts ())[p]!)
      (fun cls => Native.classOrbitCheck Native.nTrio cls [1, 42, 56, 1008, 2688]
        (Native.trioSteps Native.lTabs)) := rfl

theorem deltaCkF_mono {tr : Nat → Nat × Nat × Nat} {ts : Nat → List Nat}
    {orb orb' : List (List Nat) → Bool} (h : ∀ cls, orb' cls = true → orb cls = true)
    (h' : deltaCkF tr ts orb' = true) : deltaCkF tr ts orb = true := by
  simp only [deltaCkF, Bool.and_eq_true] at h' ⊢
  exact ⟨⟨⟨h'.1.1.1, h _ h'.1.1.2⟩, h'.1.2⟩, h'.2⟩

theorem sextFactsCheck_eq : Native.sextFactsCheck () =
    sextFactsF (fun q => (Native.sextList ())[q]!) (fun p => (Native.trioList ())[p]!)
      (fun p => (Native.trioSexts ())[p]!)
      (fun q => (xiBF (fun q => (Native.sextList ())[q]!) 0 q).getD 1 false)
      (Native.uTabs.all fun g => Native.imgSext g Native.baseSext == Native.baseSext)
      (fun cls => Native.classOrbitCheck Native.nSext cls [1, 90, 240, 1440]
        (Native.sextSteps Native.uTabs))
      (fun cls => Native.classOrbitCheck Native.nTrio cls [15, 180, 720, 2880]
        (Native.trioSteps Native.uTabs)) := rfl

theorem sextFactsF_mono {sl : Nat → List Nat} {tr : Nat → Nat × Nat × Nat} {ts : Nat → List Nat}
    {xi1 : Nat → Bool} {u0 u0' : Bool} {orbS orbT orbS' orbT' : List (List Nat) → Bool}
    (hu : u0' = true → u0 = true) (hS : ∀ cls, orbS' cls = true → orbS cls = true)
    (hT : ∀ cls, orbT' cls = true → orbT cls = true)
    (h' : sextFactsF sl tr ts xi1 u0' orbS' orbT' = true) :
    sextFactsF sl tr ts xi1 u0 orbS orbT = true := by
  simp only [sextFactsF, Bool.and_eq_true] at h' ⊢
  exact ⟨⟨hu h'.1.1, hS _ h'.1.2⟩, hT _ h'.2⟩

theorem sextFactsF_xi1 {sl : Nat → List Nat} {tr : Nat → Nat × Nat × Nat} {ts : Nat → List Nat}
    {xi1 xi1' : Nat → Bool} {u0 : Bool} {orbS orbT : List (List Nat) → Bool}
    (h : ∀ p < Native.nTrio, ∀ q ∈ ts p, xi1 q = xi1' q) :
    sextFactsF sl tr ts xi1 u0 orbS orbT = sextFactsF sl tr ts xi1' u0 orbS orbT := by
  have hK : ((List.range Native.nTrio).map fun p => (p, kappaBF sl tr ts xi1 0 p)) =
      (List.range Native.nTrio).map fun p => (p, kappaBF sl tr ts xi1' 0 p) := by
    refine List.map_congr_left fun p hp => ?_
    have e : (ts p).any xi1 = (ts p).any xi1' := any_congr_mem (h p (List.mem_range.1 hp))
    simp only [kappaBF, e]
  simp only [sextFactsF, hK]

theorem xiCls_mask (sl : Nat → List Nat) {q : Nat} (hq : q < Native.nSext) :
    (maskL ((xiCls sl).getD 1 [])).testBit q = (xiBF sl 0 q).getD 1 false := by
  rw [testBit_maskL]
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  rw [xiCls, h4]
  simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
  rw [contains_cls _ _ _ hq]

end CFSG.KC.M24G
