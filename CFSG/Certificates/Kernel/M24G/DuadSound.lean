module

public import Certificates.Data.Kernel.M24G.Duad
import CFSG.Certificates.Kernel.M24G.BfsReplaySound
import CFSG.Certificates.Kernel.M24G.ReplayFacts
import CFSG.Certificates.Kernel.M24G.IdxSound
import CFSG.Certificates.Kernel.M24G.FixOctSound
import CFSG.Certificates.Kernel.M24G.ImgSound
import CFSG.Certificates.Kernel.M24G.ToddSound

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem duad_toArray_getD {α : Type} [Inhabited α] (l : List α) (i : Nat) :
    l.toArray[i]! = l.getD i default := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem duad_getD_lt {α : Type} (l : List α) (d : α) {n : Nat} (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem treeValid_of_replay {α : Type} [Inhabited α] [DecidableEq α] {i2 : DecidableEq α}
    {key : α → Nat} {steps : List (α → α)} {base : α} {fuel : Nat} {L : List α}
    {par gen : List Nat} {pos : KTree (Nat × Nat)}
    (h : replayOK key steps base fuel L par gen pos = true) (valid : α → Bool)
    (hv : ∀ y ∈ L, valid y = true) :
    @Native.treeValid α _ i2 valid steps base (L.toArray, par.toArray, gen.toArray) = true := by
  obtain ⟨-, hhead, hpl, hgl, htree, -⟩ := replay_facts h
  have hL : 0 < L.length := by
    cases L with
    | nil => cases hhead
    | cons _ _ => simp
  have h0 : L.toArray[0]! = base := by
    cases L with
    | nil => cases hhead
    | cons x l =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      rw [duad_toArray_getD, List.getD_cons_zero, hhead]
  unfold Native.treeValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.size_toArray, allLt_iff',
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨hL, h0⟩, hpl⟩, hgl⟩, fun j hj => ⟨?_, ?_⟩⟩
  · rw [duad_toArray_getD, duad_getD_lt _ _ hj]
    exact hv _ (List.getElem_mem hj)
  · rcases Nat.eq_zero_or_pos j with rfl | hp0
    · exact Or.inl rfl
    · obtain ⟨q1, q2, q3⟩ := htree j hp0 hj
      refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
      · rw [get!_toArray_nat]
        exact q1
      · rw [get!_toArray_nat]
        exact q2
      · rw [get!_toArray_nat, get!_toArray_nat, duad_toArray_getD, duad_toArray_getD,
          duad_getD_lt _ _ hj]
        exact q3

theorem nodup_map_of_posOK {α : Type} {key : α → Nat} {L : List α} {pos : KTree (Nat × Nat)}
    (h : posOK key L pos = true) : (L.map key).Nodup := by
  refine List.pairwise_iff_getElem.2 fun i j hi hj hij e => ?_
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map] at e
  have := posOK_inj h hi hj e
  omega

@[expose] def DuadV (t : Array Nat) : Prop := t.size = 24 ∧ ∀ x ∈ t.toList, x < 24

theorem duadV_of (t : Array Nat) (h : duadValidT t = true) : DuadV t := by
  unfold duadValidT at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem duad_foldl_inj : ∀ (l1 l2 : List Nat) (c1 c2 : Nat), l1.length = l2.length →
    (∀ x ∈ l1, x < 24) → (∀ x ∈ l2, x < 24) →
    l1.foldl (fun acc x => acc * 24 + x) c1 = l2.foldl (fun acc x => acc * 24 + x) c2 →
    c1 = c2 ∧ l1 = l2
  | [], [], c1, c2, _, _, _, h => ⟨by simpa using h, rfl⟩
  | x :: l1, y :: l2, c1, c2, hl, h1, h2, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨e, rfl⟩ := duad_foldl_inj l1 l2 _ _ (by simpa using hl)
      (fun z hz => h1 z (List.mem_cons_of_mem _ hz)) (fun z hz => h2 z (List.mem_cons_of_mem _ hz)) h
    have hx := h1 x List.mem_cons_self
    have hy := h2 y List.mem_cons_self
    have e2 : c1 = c2 ∧ x = y := by omega
    exact ⟨e2.1, by rw [e2.2]⟩
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl

theorem duadKeyF_inj {a b : Array Nat} (ha : DuadV a) (hb : DuadV b)
    (e : duadKeyF a = duadKeyF b) : a = b := by
  apply Array.toList_inj.1
  exact (duad_foldl_inj a.toList b.toList 0 0 (by rw [Array.length_toList, Array.length_toList,
    ha.1, hb.1]) ha.2 hb.2 e).2

theorem duad_getD_mem_or (l : List Nat) (k d : Nat) : l.getD k d ∈ l ∨ l.getD k d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => exact Or.inr rfl
  | some x => exact Or.inl (List.mem_of_getElem? h)

theorem duadV_mulTabF {a : Array Nat} (ha : DuadV a) (b : Array Nat) : DuadV (mulTabF a b) := by
  refine ⟨size_mulTabF a b, fun x hx => ?_⟩
  simp only [mulTabF, List.toList_toArray, List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  rcases duad_getD_mem_or a.toList (b.toList.getD i 0) 0 with h | h
  · exact ha.2 _ h
  · rw [h]
    omega

theorem duad_entry_lt {y : Array Nat} (hy : DuadV y) {i : Nat} (hi : i < 24) :
    y.toList.getD i 0 < 24 := by
  rcases duad_getD_mem_or y.toList i 0 with h | h
  · exact hy.2 _ h
  · rw [h]
    omega

theorem duad_getD_range {k : Nat} (hk : k < 24) : (List.range 24).getD k 0 = k := by
  rw [duad_getD_lt _ _ (by simpa using hk), List.getElem_range]

theorem duad_map_getD (y : List Nat) (hy : y.length = 24) :
    (List.range 24).map (fun i => y.getD i 0) = y := by
  apply List.ext_getElem (by simp [hy])
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, duad_getD_lt _ _ h2]

theorem duad_toArray_eq {y : Array Nat} (hy : DuadV y) :
    ((List.range 24).map (fun i => y.toList.getD i 0)).toArray = y := by
  rw [duad_map_getD y.toList (by rw [Array.length_toList, hy.1]), Array.toArray_toList]

theorem duadId_toList : (Native.duadId ()).toList = List.range 24 := by
  unfold Native.duadId
  rw [Array.toList_range]

theorem duadId_eq : Native.duadId () = Native.fixOctIdTab := by
  apply Array.toList_inj.1
  rw [duadId_toList]
  decide

theorem duadV_id : DuadV (Native.duadId ()) := by
  refine ⟨by rw [← Array.length_toList, duadId_toList, List.length_range], fun x hx => ?_⟩
  rw [duadId_toList] at hx
  exact List.mem_range.1 hx

theorem mulTabF_id_left {y : Array Nat} (hy : DuadV y) : mulTabF (Native.duadId ()) y = y := by
  unfold mulTabF
  rw [duadId_toList]
  rw [List.map_congr_left (fun i hi => duad_getD_range (duad_entry_lt hy (List.mem_range.1 hi)))]
  exact duad_toArray_eq hy

theorem mulTabF_id_right {g : Array Nat} (hg : DuadV g) : mulTabF g (Native.duadId ()) = g := by
  unfold mulTabF
  rw [duadId_toList]
  rw [List.map_congr_left (fun i hi => by rw [duad_getD_range (List.mem_range.1 hi)])]
  exact duad_toArray_eq hg

theorem mulTabF_getD (a b : Array Nat) {i : Nat} (hi : i < 24) :
    (mulTabF a b).toList.getD i 0 = a.toList.getD (b.toList.getD i 0) 0 := by
  unfold mulTabF
  rw [List.toList_toArray, duad_getD_lt _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]

theorem mulTabF_assoc (g x : Array Nat) {y : Array Nat} (hy : DuadV y) :
    mulTabF (mulTabF g x) y = mulTabF g (mulTabF x y) := by
  unfold mulTabF
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  have e := mulTabF_getD g x (duad_entry_lt hy hi')
  unfold mulTabF at e
  rw [e]
  have e2 := mulTabF_getD x y hi'
  unfold mulTabF at e2
  rw [e2]

open scoped CFSG.KC.M24G.FixOctEq

section Grp

variable {gens : List (Array Nat)} {fuel : Nat} {L : List (Array Nat)} {par gen : List Nat}
  {pos : KTree (Nat × Nat)}

theorem duad_gensV (hg : duadGensOK gens = true) : ∀ g ∈ gens, DuadV g := by
  unfold duadGensOK at hg
  rw [List.all_eq_true] at hg
  exact fun g h => duadV_of g (hg g h)

theorem duad_LV (hg : duadGensOK gens = true)
    (h : replayOK duadKeyF (duadStepsF gens) (Native.duadId ()) fuel L par gen pos = true) :
    ∀ y ∈ L, DuadV y := by
  refine replay_induction h DuadV duadV_id fun x _ s hs => ?_
  unfold duadStepsF at hs
  obtain ⟨g, hg', rfl⟩ := List.mem_map.1 hs
  exact duadV_mulTabF (duad_gensV hg g hg') x

theorem duad_closed (hg : duadGensOK gens = true)
    (h : replayOK duadKeyF (duadStepsF gens) (Native.duadId ()) fuel L par gen pos = true)
    (hf : L.length ≤ fuel) : ∀ x ∈ L, ∀ g ∈ gens, mulTabF g x ∈ L := by
  obtain ⟨-, -, -, -, -, hcl⟩ := replay_facts h
  intro x hx g hg'
  obtain ⟨i, hi, e⟩ := hcl hf x hx (mulTabF g) (List.mem_map.2 ⟨g, hg', rfl⟩)
  rw [← duadKeyF_inj (duad_LV hg h _ (List.getElem_mem hi))
    (duadV_mulTabF (duad_gensV hg g hg') x) e]
  exact List.getElem_mem hi

theorem duad_head (h : replayOK duadKeyF (duadStepsF gens) (Native.duadId ()) fuel L par gen pos
    = true) : Native.duadId () ∈ L := by
  obtain ⟨-, hhead, -⟩ := replay_facts h
  exact List.mem_of_mem_head? hhead

theorem duad_mul_mem (hg : duadGensOK gens = true)
    (h : replayOK duadKeyF (duadStepsF gens) (Native.duadId ()) fuel L par gen pos = true)
    (hf : L.length ≤ fuel) : ∀ x ∈ L, ∀ y ∈ L, mulTabF x y ∈ L := by
  have hV := duad_LV hg h
  refine replay_induction h (fun x => ∀ y ∈ L, mulTabF x y ∈ L)
    (fun y hy => by rw [mulTabF_id_left (hV y hy)]; exact hy) fun x hx s hs y hy => ?_
  unfold duadStepsF at hs
  obtain ⟨g, hg', rfl⟩ := List.mem_map.1 hs
  rw [mulTabF_assoc g x (hV y hy)]
  exact duad_closed hg h hf _ (hx y hy) g hg'

theorem duadComp_eq (a b : Array Nat) : Native.duadComp a b = mulTabF a b := by
  unfold Native.duadComp mulTabF
  rw [range24_map]
  simp only [get!_nat]

theorem duadKey_eq : Native.duadKey = duadKeyF := by
  funext t
  unfold Native.duadKey duadKeyF
  rw [Array.foldl_toList]

theorem duadSteps_eq (gens : List (Array Nat)) :
    (gens.map fun g t => Native.duadComp g t) = duadStepsF gens := by
  unfold duadStepsF
  congr 1
  funext g t
  exact duadComp_eq g t

theorem duadGrpData_eq {n : Nat}
    (h : replayOK duadKeyF (duadStepsF gens) (Native.duadId ()) (n + 5) L par gen pos = true) :
    Native.duadGrpData gens n = (L.toArray, par.toArray, gen.toArray) := by
  unfold Native.duadGrpData
  rw [duadKey_eq, duadSteps_eq]
  exact bfs_eq_of_replayOK h

theorem duad_arr_beq (a b : Array Nat) : (a == b) = duadEqT a b := by
  unfold duadEqT
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq, Array.toList_inj]

theorem duad_contains {M : List (Array Nat)} {x : Array Nat} (hx : x ∈ M) :
    M.toArray.contains x = true := by
  simpa using hx

theorem duadGrpCheck_of {n : Nat} (hg : duadGensOK gens = true)
    (h : replayOK duadKeyF (duadStepsF gens) Native.fixOctIdTab (n + 5) L par gen pos = true)
    (hn : L.length = n) (hinv : duadInvOK pos L = true) :
    Native.duadGrpCheck gens n = true := by
  rw [← duadId_eq] at h
  have hV := duad_LV hg h
  have hf : L.length ≤ n + 5 := by omega
  have hpos := (replay_facts h).1
  have hmem : ∀ i < n, L.toArray[i]! ∈ L := fun i hi => by
    rw [toArray_getElem! L (by omega)]
    exact List.getElem_mem _
  unfold Native.duadGrpCheck
  simp only [duadGrpData_eq h, duadComp_eq, Bool.and_eq_true, beq_iff_eq, List.size_toArray,
    decide_eq_true_eq, List.all_eq_true, allLt_iff']
  refine ⟨⟨⟨⟨⟨?_, hn⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have ht := treeValid_of_replay (i2 := FixOctEq.decEqArr) h Native.duadValidTab fun y hy => by
      unfold Native.duadValidTab
      rw [beq_iff_eq]
      exact (hV y hy).1
    convert ht using 2
    rfl
  · have := nodup_map_of_posOK hpos
    exact List.Nodup.of_map _ this
  · intro g hg'
    apply duad_contains
    have := duad_closed hg h hf _ (duad_head h) g hg'
    rwa [mulTabF_id_right (duad_gensV hg g hg')] at this
  · intro i hi j hj
    exact duad_contains (duad_mul_mem hg h hf _ (hmem i hi) _ (hmem j hj))
  · intro i hi
    have hx := hmem i hi
    unfold duadInvOK at hinv
    rw [List.all_eq_true] at hinv
    have hr := hinv _ hx
    unfold duadInvRow at hr
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hr
    obtain ⟨⟨hvy, k, hk⟩, he⟩ := hr
    obtain ⟨hkL, ek⟩ := (findK_eq_some duadKeyF hpos _ k).1 hk
    have e := duadKeyF_inj (hV _ (List.getElem_mem hkL)) (duadV_of _ hvy) ek
    have hany : (L.toArray.toList.any fun a => mulTabF L.toArray[i]! a == Native.duadId ()) =
        true := by
      rw [List.toList_toArray, List.any_eq_true]
      exact ⟨_, e ▸ List.getElem_mem hkL, by rw [duad_arr_beq, duadId_eq]; exact he⟩
    rw [Array.any_toList] at hany
    exact hany

theorem duad_length_filter_comp {β : Type} (I : List Nat) (get : Nat → β) (q : β → Bool) :
    (I.filter fun i => q (get i)).length = ((I.map get).filter q).length := by
  rw [List.filter_map, List.length_map]
  rfl

theorem duad_map_get (M : List (Array Nat)) :
    (List.range M.length).map (fun i => M.toArray[i]!) = M := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, toArray_getElem! M h2]

theorem duad_bad_len (I : List Nat) (get : Nat → Array Nat) :
    (I.filter fun i => decide (32 ≤ (I.filter fun j =>
      Native.duadComp (get i) (get j) == Native.duadComp (get j) (get i)).length)).length =
      (duadBadOn (I.map get)).length := by
  unfold duadBadOn
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro i _
  rw [Function.comp_apply, List.filter_map, List.length_map]
  simp only [Function.comp_def, duadComp_eq, duad_arr_beq]

theorem duadEaCheck_of {n : Nat}
    (h : replayOK duadKeyF (duadStepsF gens) Native.fixOctIdTab (n + 5) L par gen pos = true)
    (hn : L.length = n) (hea : duadEaF L = true) : Native.duadEaCheck gens n = true := by
  rw [← duadId_eq] at h
  have hI : (Native.duadInvs L.toArray n).map (fun i => L.toArray[i]!) = duadInvsF L := by
    simp only [Native.duadInvs, duadInvsF]
    conv_rhs => rw [← duad_map_get L, hn, List.filter_map]
    congr 1
    apply List.filter_congr
    intro i _
    simp only [Function.comp, duadComp_eq, duad_arr_beq, duadId_eq]
  have e := duad_bad_len (Native.duadInvs L.toArray n) (fun i => L.toArray[i]!)
  rw [hI] at e
  unfold duadEaF at hea
  have e2 : decide ((Native.duadBad L.toArray n).length < 32) =
      decide ((duadBadOn (duadInvsF L)).length < 32) := by
    rw [← e]
    rfl
  unfold Native.duadEaCheck
  rw [duadGrpData_eq h]
  exact e2.trans hea

end Grp

theorem duad_toddAct_eq (g : Array Nat) (hg : ∀ x ∈ g.toList, x < 24) :
    (fun m => Native.toddAct g m) = toddActF (imgTab g.toList) := by
  funext m
  unfold Native.toddAct toddActF
  rw [img_eq_imgF g hg]

theorem duadPpSteps_eq : (Native.duadPpGens.map fun g m => Native.toddAct g m) = duadPpStepsF := by
  unfold duadPpStepsF
  apply List.map_congr_left
  intro g hg
  exact duad_toddAct_eq g (by revert g; decide)

theorem duadPairOrbitCheck_of {pL pPar pGen : List Nat} {pos : KTree (Nat × Nat)}
    (h : replayOK (Native.duadPairKey (Native.duadT0 ())) duadPpStepsF (Native.duadF770 ()) 900
      pL pPar pGen pos = true) (hl : 770 ≤ pL.length) : Native.duadPairOrbitCheck () = true := by
  have hcc : ∀ c ∈ Native.ccEColsN, c < 2 ^ 11 := by decide
  have hv : ∀ y ∈ pL, y < 2048 := replay_induction h (· < 2048) (by decide) fun x _ s hs => by
    unfold duadPpStepsF at hs
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hs
    unfold toddActF
    exact actM_lt _ hcc _
  simp only [Native.duadPairOrbitCheck, duadPpSteps_eq, bfs_eq_of_replayOK h, Bool.and_eq_true,
    decide_eq_true_eq, List.size_toArray, List.toList_toArray]
  exact ⟨⟨treeValid_of_replay h _ fun y hy => decide_eq_true (hv y hy), hl⟩,
    nodup_map_of_posOK (replay_facts h).1⟩

theorem testBit_orMask (m : Nat) : ∀ l : List Nat, (orMask l).testBit m = l.contains m
  | [] => by simp [orMask]
  | c :: l => by
    rw [orMask, Nat.testBit_or, testBit_orMask m l, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.contains_cons]
    by_cases hc : c = m
    · subst hc
      simp
    · simp [hc, Ne.symm hc]

theorem duad_scTab_get (cl : Array Nat) {m : Nat} (hm : m < 2048) :
    (Native.scTab cl)[m]! = cl.toList.contains m := by
  unfold Native.scTab
  rw [getElem!_pos _ _ (by simpa using hm)]
  simp

theorem duadCoverCheck_of {SL : List (List Nat)} (hS : Native.sextList () = SL.toArray)
    (h : duadCoverF SL = true) : Native.duadCoverCheck () = true := by
  unfold duadCoverF duadCoverOn at h
  simp only [Native.duadCoverCheck]
  rw [allLt_iff'] at h ⊢
  intro m hm
  have hm' := h m hm
  rw [testBit_orMask, List.contains_append] at hm'
  rw [hS, duad_scTab_get _ (by omega), Native.clsTab]
  simpa [Bool.or_assoc] using hm'

end CFSG.KC.M24G
