module

public import CFSG.Certificates.Kernel.M24G.GeomFacts
public import CFSG.Certificates.Kernel.M24G.BfsReplaySound
public import CFSG.Certificates.Kernel.M24G.StepsSound
public import Certificates.Data.Kernel.M24G.ListChecks
public import Mathlib.Algebra.Order.Group.Nat

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem mem_iff_idxK {α : Type} {key : α → Nat} {L : List α} {pos : KTree (Nat × Nat)}
    (h : posOK key L pos = true) {n : Nat} (hn : L.length = n) (k : Nat) :
    idxK pos n k < n ↔ ∃ y ∈ L, key y = k := by
  rw [idxK_lt_iff h hn]
  constructor
  · rintro ⟨i, hi, e⟩
    exact ⟨L[i], List.getElem_mem hi, e⟩
  · rintro ⟨y, hy, e⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    exact ⟨i, hi, e⟩

theorem idxK_mem {α : Type} {key : α → Nat} {L : List α} {pos : KTree (Nat × Nat)}
    (h : posOK key L pos = true) {n : Nat} (hn : L.length = n) {y : α} (hy : y ∈ L) :
    idxK pos n (key y) < n :=
  (mem_iff_idxK h hn _).2 ⟨y, hy, rfl⟩

section Oct

variable {O oP oG : List Nat} {posO : KTree (Nat × Nat)}
  (hO : replayOK id (Native.genTabs.map Native.img) 255 1000 O oP oG posO = true)
  (hOl : O.length = 759) (hOi : O.all octItem = true)

include hO in
theorem octData_of : Native.octData () = (O.toArray, oP.toArray, oG.toArray) :=
  bfs_eq_of_replayOK hO

include hO in
theorem octList_of : Native.octList () = O.toArray := by
  unfold Native.octList
  rw [octData_of hO]

include hO hOl in
theorem octIdx_of (m : Nat) : Native.octIdx m = idxK posO 759 m := by
  rw [octIdx_eq_idxNat, octList_of hO]
  exact idxNat_eq_idxK (key := id) (replay_facts hO).1 hOl (fun y _ e => e)

include hOi in
theorem oct_lt {x : Nat} (hx : x ∈ O) : x < 2 ^ 24 := by
  have := List.all_eq_true.1 hOi x hx
  simp only [octItem, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

include hO hOl in
theorem img_mem_oct {g : Array Nat} (hg : g ∈ Native.genTabs) {x : Nat} (hx : x ∈ O) :
    Native.img g x ∈ O := by
  obtain ⟨-, -, -, -, -, hc⟩ := replay_facts hO
  obtain ⟨i, hi, e⟩ := hc (by omega) x hx (Native.img g) (List.mem_map_of_mem hg)
  have e' : O[i] = Native.img g x := e
  rw [← e']
  exact List.getElem_mem hi

include hO hOl in
theorem octIdx_lt_iff (m : Nat) : Native.octIdx m < Native.nOct ↔ m ∈ O := by
  rw [octIdx_of hO hOl]
  have := mem_iff_idxK (key := id) (replay_facts hO).1 hOl m
  simp only [id] at this
  have hn : Native.nOct = 759 := rfl
  rw [hn, this]
  exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun h => ⟨m, h, rfl⟩⟩

include hO hOl hOi in
theorem octCheck_of : Native.octCheck () = true := by
  obtain ⟨hpos, hb, -, -, -, -⟩ := replay_facts hO
  unfold Native.octCheck
  simp only [octList_of hO, octData_of hO, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [hOl, Native.nOct]
  · cases O with
    | nil => simp at hOl
    | cons x O' =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      rfl
  · unfold Native.allLt
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    have hi' : i < O.length := by rw [hOl]; exact hi
    rw [toArray_getElem! O hi']
    have hit := List.all_eq_true.1 hOi O[i] (List.getElem_mem hi')
    unfold octItem at hit
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hit ⊢
    refine ⟨⟨hit, ?_⟩, fun g hg => ?_⟩
    · rw [octIdx_of hO hOl]
      exact idxK_getElem (key := id) hpos 759 hi'
    · exact (octIdx_lt_iff hO hOl _).2 (img_mem_oct hO hOl hg (List.getElem_mem hi'))
  · refine treeOK_of_replay hO _ fun p hp => ?_
    rw [octIdx_of hO hOl]
    exact idxK_getElem (key := id) hpos 759 hp

end Oct

theorem mem_genTabs_map {β : Type} {f : Array Nat → β} {s : β} (hs : s ∈ Native.genTabs.map f) :
    ∃ g ∈ Native.genTabs, f g = s := List.mem_map.1 hs

section Trio

variable {O oP oG : List Nat} {posO : KTree (Nat × Nat)}
  (hO : replayOK id (Native.genTabs.map Native.img) 255 1000 O oP oG posO = true)
  (hOl : O.length = 759) (hOi : O.all octItem = true) (hB : baseOK posO = true)
  {T : List (Nat × Nat × Nat)} {tP tG : List Nat} {posT : KTree (Nat × Nat)}
  (hT : replayOK Native.key3 (Native.genTabs.map Native.imgTrio) Native.baseTrio 5000 T tP tG posT =
    true)
  (hTl : T.length = 3795) (hTi : T.all trioItem = true) (hP : pairsOK O posT = true)

include hT in
theorem trioData_of : Native.trioData () = (T.toArray, tP.toArray, tG.toArray) :=
  bfs_eq_of_replayOK hT

include hT in
theorem trioList_of : Native.trioList () = T.toArray := by
  unfold Native.trioList
  rw [trioData_of hT]

include hO hOl hB hT in
theorem trio_octs {t : Nat × Nat × Nat} (ht : t ∈ T) : ∀ x ∈ Native.octsT t, x ∈ O := by
  refine replay_induction hT (fun t => ∀ x ∈ Native.octsT t, x ∈ O) ?_ ?_ t ht
  · have hb := hB
    unfold baseOK at hb
    rw [Bool.and_eq_true] at hb
    intro x hx
    have := List.all_eq_true.1 hb.1 x hx
    rw [decide_eq_true_eq] at this
    obtain ⟨y, hy, e⟩ := (mem_iff_idxK (key := id) (replay_facts hO).1 hOl x).1 this
    exact e ▸ hy
  · intro t ih s hs x hx
    obtain ⟨g, hg, rfl⟩ := mem_genTabs_map hs
    rcases mem_sort3 hx with rfl | rfl | rfl
    · exact img_mem_oct hO hOl hg (ih _ (by simp [Native.octsT]))
    · exact img_mem_oct hO hOl hg (ih _ (by simp [Native.octsT]))
    · exact img_mem_oct hO hOl hg (ih _ (by simp [Native.octsT]))

include hO hOl hOi hB hT in
theorem trio_lt {t : Nat × Nat × Nat} (ht : t ∈ T) : ∀ x ∈ Native.octsT t, x < 2 ^ 24 :=
  fun x hx => oct_lt hOi (trio_octs hO hOl hB hT ht x hx)

include hO hOl hOi hB hT hTl in
theorem trioIdx_of (t : Nat × Nat × Nat) (ht : ∀ x ∈ Native.octsT t, x < 2 ^ 24) :
    Native.trioIdx t = idxK posT 3795 (Native.key3 t) := by
  rw [trioIdx_eq_idxNat, trioList_of hT]
  exact idxNat_eq_idxK (replay_facts hT).1 hTl
    (fun y hy e => key3_inj (trio_lt hO hOl hOi hB hT hy) ht e)

theorem imgTrio_lt {g : Array Nat} (hg : g ∈ Native.genTabs) (t : Nat × Nat × Nat) :
    ∀ x ∈ Native.octsT (Native.imgTrio g t), x < 2 ^ 24 := by
  intro x hx
  rcases mem_sort3 hx with rfl | rfl | rfl <;> exact img_lt (genTabs_lt g hg) _

theorem full_lt : Native.full < 2 ^ 24 := by decide

include hO hOl hOi hB hT hTl hTi hP in
theorem trioCheck_of : Native.trioCheck () = true := by
  obtain ⟨hpos, hb, -, -, -, hc⟩ := replay_facts hT
  unfold Native.trioCheck
  simp only [trioList_of hT, trioData_of hT, octList_of hO, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [hTl, Native.nTrio]
  · cases T with
    | nil => simp at hTl
    | cons x T' =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      simp
  · unfold Native.allLt
    rw [List.all_eq_true]
    intro p hp
    rw [List.mem_range] at hp
    have hp' : p < T.length := by rw [hTl]; exact hp
    rw [toArray_getElem! T hp']
    have hm := List.getElem_mem hp'
    have hit := List.all_eq_true.1 hTi T[p] hm
    have hoc := trio_octs hO hOl hB hT hm
    have hlt := trio_lt hO hOl hOi hB hT hm
    unfold trioItem at hit
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hit ⊢
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, d1⟩, d2⟩, d3⟩, f⟩ := hit
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, ?_⟩, ?_⟩, ?_⟩, d1⟩, d2⟩, d3⟩, f⟩, ?_⟩, fun g hg => ?_⟩
    · exact (octIdx_lt_iff hO hOl _).2 (hoc _ (by simp [Native.octsT]))
    · exact (octIdx_lt_iff hO hOl _).2 (hoc _ (by simp [Native.octsT]))
    · exact (octIdx_lt_iff hO hOl _).2 (hoc _ (by simp [Native.octsT]))
    · rw [trioIdx_of hO hOl hOi hB hT hTl _ hlt]
      exact idxK_getElem hpos 3795 hp'
    · rw [trioIdx_of hO hOl hOi hB hT hTl _ (imgTrio_lt hg _)]
      obtain ⟨i, hi, e⟩ := hc (by omega) _ hm _ (List.mem_map_of_mem hg)
      rw [← e, idxK_getElem hpos 3795 hi]
      have hn : Native.nTrio = 3795 := rfl
      omega
  · refine treeOK_of_replay hT _ fun p hp => ?_
    rw [trioIdx_of hO hOl hOi hB hT hTl _ (trio_lt hO hOl hOi hB hT (List.getElem_mem hp))]
    exact idxK_getElem hpos 3795 hp
  · unfold Native.allLt
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    have hi' : i < O.length := by rw [hOl]; exact hi
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    have hj' : j < O.length := by rw [hOl]; exact hj
    rw [toArray_getElem! O hi', toArray_getElem! O hj']
    have ha := oct_lt hOi (List.getElem_mem hi')
    have hb := oct_lt hOi (List.getElem_mem hj')
    have hc3 := Nat.xor_lt_two_pow (Nat.xor_lt_two_pow full_lt ha) hb
    rw [trioIdx_of hO hOl hOi hB hT hTl _ (fun x hx => by
      rcases mem_sort3 hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc3)]
    exact List.all_eq_true.1 (List.all_eq_true.1 hP _ (List.getElem_mem hi')) _
      (List.getElem_mem hj')

end Trio

section Sext

variable {O oP oG : List Nat} {posO : KTree (Nat × Nat)}
  (hO : replayOK id (Native.genTabs.map Native.img) 255 1000 O oP oG posO = true)
  (hOl : O.length = 759) (hOi : O.all octItem = true) (hB : baseOK posO = true)
  {S : List (List Nat)} {sP sG : List Nat} {posS : KTree (Nat × Nat)}
  (hS : replayOK Native.keyL (Native.genTabs.map Native.imgSext) Native.baseSext 3000 S sP sG posS =
    true)
  (hSl : S.length = 1771) (hSi : S.all sextItem = true) (hTet : tetsOK O posS = true)

include hS in
theorem sextData_of : Native.sextData () = (S.toArray, sP.toArray, sG.toArray) :=
  bfs_eq_of_replayOK hS

include hS in
theorem sextList_of : Native.sextList () = S.toArray := by
  unfold Native.sextList
  rw [sextData_of hS]

theorem sextItem_facts {s : List Nat} (h : sextItem s = true) :
    s.length = 6 ∧ ∀ B ∈ s, B < 2 ^ 24 := by
  unfold sextItem at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, fun B hB => (h.1.1.2 B hB).2⟩

include hO hOl hB hS in
theorem sext_octs {s : List Nat} (hs : s ∈ S) : ∀ B ∈ s, ∀ B' ∈ s, B ≠ B' → B ||| B' ∈ O := by
  refine replay_induction hS (fun s => ∀ B ∈ s, ∀ B' ∈ s, B ≠ B' → B ||| B' ∈ O) ?_ ?_ s hs
  · have hb := hB
    unfold baseOK at hb
    rw [Bool.and_eq_true] at hb
    intro B hB' B' hB'' hne
    have := List.all_eq_true.1 (List.all_eq_true.1 hb.2 B hB') B' hB''
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with e | this
    · exact absurd e hne
    · obtain ⟨y, hy, e⟩ := (mem_iff_idxK (key := id) (replay_facts hO).1 hOl _).1 this
      exact e ▸ hy
  · intro s ih st hst B hB B' hB' hne
    obtain ⟨g, hg, rfl⟩ := mem_genTabs_map hst
    unfold Native.imgSext at hB hB'
    rw [mem_sortL, List.mem_map] at hB hB'
    obtain ⟨b, hb, rfl⟩ := hB
    obtain ⟨b', hb', rfl⟩ := hB'
    rw [← img_or]
    exact img_mem_oct hO hOl hg (ih b hb b' hb' fun e => hne (e ▸ rfl))

include hS hSl hSi in
theorem sextIdx_of (s : List Nat) (hl : s.length = 6) (hb : ∀ B ∈ s, B < 2 ^ 24) :
    Native.sextIdx s = idxK posS 1771 (Native.keyL s) := by
  rw [sextIdx_eq_idxNat, sextList_of hS]
  refine idxNat_eq_idxK (replay_facts hS).1 hSl fun y hy e => ?_
  obtain ⟨yl, yb⟩ := sextItem_facts (List.all_eq_true.1 hSi y hy)
  exact keyL_inj y s (yl.trans hl.symm) yb hb e

theorem imgSext_facts {g : Array Nat} (hg : g ∈ Native.genTabs) {s : List Nat} (hl : s.length = 6) :
    (Native.imgSext g s).length = 6 ∧ ∀ B ∈ Native.imgSext g s, B < 2 ^ 24 := by
  unfold Native.imgSext
  refine ⟨by rw [length_sortL, List.length_map, hl], fun B hB => ?_⟩
  rw [mem_sortL, List.mem_map] at hB
  obtain ⟨b, -, rfl⟩ := hB
  exact img_lt (genTabs_lt g hg) _

theorem filter_pair0 (O : List Nat) {t m : Nat} (h : t &&& m = m) :
    O.filter (fun o => o &&& t == t) =
      (O.filter fun o => o &&& m == m).filter (fun o => o &&& t == t) := by
  rw [List.filter_filter]
  refine List.filter_congr fun o _ => ?_
  by_cases ho : o &&& t = t
  · have e : o &&& m = m := by rw [← h, ← Nat.and_assoc, ho]
    simp [ho, e]
  · simp [ho]

theorem tetrads0_of : Native.tetrads0 () = (List.range 24).flatMap tetsA := rfl

include hO hOl hOi hS hSl hSi hTet in
theorem tets_of : ((Native.tetrads0 ()).all fun t =>
    ((Native.octList ()).toList.filter (fun o => o &&& t == t)).length == 5 &&
      decide (Native.sextIdx (Native.sextOf t) < Native.nSext)) = true := by
  rw [tetrads0_of, List.all_flatMap, List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro t ht
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 hTet a ha) t ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  obtain ⟨⟨tlt, tm⟩, h2⟩ := h1
  unfold tetOK at h2
  rw [← filter_pair0 O tm] at h2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2 ⊢
  unfold Native.sextOf
  rw [octList_of hO, List.toList_toArray, sortL_eq_sortN]
  refine ⟨h2.1, ?_⟩
  have hl : (sortN (t :: (O.filter (fun o => o &&& t == t)).map (· ^^^ t))).length = 6 := by
    rw [← sortL_eq_sortN, length_sortL, List.length_cons, List.length_map, h2.1]
  rw [sextIdx_of hS hSl hSi _ hl]
  · exact h2.2
  · intro B hB
    rw [← sortL_eq_sortN, mem_sortL, List.mem_cons] at hB
    rcases hB with rfl | hB
    · exact tlt
    · rw [List.mem_map] at hB
      obtain ⟨o, ho, rfl⟩ := hB
      exact Nat.xor_lt_two_pow (oct_lt hOi (List.mem_of_mem_filter ho)) tlt

include hO hOl hOi hB hS hSl hSi hTet in
theorem sextCheck_of : Native.sextCheck () = true := by
  obtain ⟨hpos, hb, -, -, -, hc⟩ := replay_facts hS
  have ht := tets_of hO hOl hOi hS hSl hSi hTet
  unfold Native.sextCheck
  simp only [sextList_of hS, sextData_of hS, octList_of hO] at ht ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ht⟩
  · simp [hSl, Native.nSext]
  · cases S with
    | nil => simp at hSl
    | cons x S' =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      simp
  · unfold Native.allLt
    rw [List.all_eq_true]
    intro q hq
    rw [List.mem_range] at hq
    have hq' : q < S.length := by rw [hSl]; exact hq
    rw [toArray_getElem! S hq']
    have hm := List.getElem_mem hq'
    have hit := List.all_eq_true.1 hSi S[q] hm
    obtain ⟨hl, hlt⟩ := sextItem_facts hit
    have hoc := sext_octs hO hOl hB hS hm
    unfold sextItem at hit
    rw [sortL_eq_sortN]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true] at hit ⊢
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := hit
    refine ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, fun B hB B' hB' => ?_⟩, ?_⟩, fun g hg => ?_⟩
    · rcases a6 B hB B' hB' with e | e
      · exact Or.inl e
      · by_cases hne : B = B'
        · exact Or.inl hne
        · exact Or.inr ⟨e, (octIdx_lt_iff hO hOl _).2 (hoc B hB B' hB' hne)⟩
    · rw [sextIdx_of hS hSl hSi _ hl hlt]
      exact idxK_getElem hpos 1771 hq'
    · obtain ⟨il, ib⟩ := imgSext_facts hg hl
      rw [sextIdx_of hS hSl hSi _ il ib]
      obtain ⟨i, hi, e⟩ := hc (by omega) _ hm _ (List.mem_map_of_mem hg)
      rw [← e, idxK_getElem hpos 1771 hi]
      have hn : Native.nSext = 1771 := rfl
      omega
  · refine treeOK_of_replay hS _ fun p hp => ?_
    obtain ⟨hl, hlt⟩ := sextItem_facts (List.all_eq_true.1 hSi _ (List.getElem_mem hp))
    rw [sextIdx_of hS hSl hSi _ hl hlt]
    exact idxK_getElem hpos 1771 hp

end Sext

theorem listChecks_of_replay {O oP oG : List Nat} {posO : KTree (Nat × Nat)}
    {T : List (Nat × Nat × Nat)} {tP tG : List Nat} {posT : KTree (Nat × Nat)}
    {S : List (List Nat)} {sP sG : List Nat} {posS : KTree (Nat × Nat)}
    (hO : replayOK id (Native.genTabs.map Native.img) 255 1000 O oP oG posO = true)
    (hT : replayOK Native.key3 (Native.genTabs.map Native.imgTrio) Native.baseTrio 5000 T tP tG
      posT = true)
    (hS : replayOK Native.keyL (Native.genTabs.map Native.imgSext) Native.baseSext 3000 S sP sG
      posS = true)
    (hOl : O.length = 759) (hTl : T.length = 3795) (hSl : S.length = 1771)
    (hOi : O.all octItem = true) (hTi : T.all trioItem = true) (hSi : S.all sextItem = true)
    (hB : baseOK posO = true) (hP : pairsOK O posT = true) (hTet : tetsOK O posS = true) :
    Native.listChecks () = true := by
  unfold Native.listChecks
  rw [octCheck_of hO hOl hOi, trioCheck_of hO hOl hOi hB hT hTl hTi hP,
    sextCheck_of hO hOl hOi hB hS hSl hSi hTet]
  rfl

end CFSG.KC.M24G
