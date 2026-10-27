module

public import Certificates.Data.Kernel.M24G.Syl
import CFSG.Certificates.Kernel.M24G.DuadSound
import CFSG.Certificates.Kernel.M24G.ReplayFacts
import CFSG.Certificates.Kernel.M24G.FixOctSound
import CFSG.Certificates.Kernel.M24G.StepsSound
import CFSG.Certificates.Kernel.M24G.ToddSound

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem syl_s0Tabs_lt : ∀ t ∈ Native.s0Tabs, ∀ x ∈ t.toList, x < 24 := by decide

theorem syl_toddAct_eq {a : Array Nat} (ha : a ∈ Native.s0Tabs) :
    Native.toddAct a = toddActF (imgTab a.toList) :=
  duad_toddAct_eq a (syl_s0Tabs_lt a ha)

theorem syl_s0Fix_of (h : sylS0FixOn Native.s0Tabs = true) : ∀ g ∈ Native.s0Tabs,
    Native.img g 255 = 255 ∧ Native.imgTrio g Native.baseTrio = Native.baseTrio ∧
      Native.imgSext g Native.baseSext = Native.baseSext ∧
      Native.imgSext g Native.pairPart = Native.pairPart := by
  intro g hg
  have hf : Native.img g = imgF (imgTab g.toList) := funext (img_eq_imgF g (syl_s0Tabs_lt g hg))
  unfold sylS0FixOn at h
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h g hg
  simp only [Native.imgTrio, Native.imgSext, sortL_eq_sortN, hf]
  exact ⟨e1, e2, e3, e4⟩

theorem syl_orbit_of {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {steps : List (α → α)} {base : α} {fuel n : Nat} {L : List α} {par gen : List Nat}
    {pos : KTree (Nat × Nat)} (valid : α → Bool)
    (h : replayOK key steps base fuel L par gen pos = true) (hn : n ≤ L.length)
    (hv : L.all valid = true) :
    ∃ r : Array α × Array Nat × Array Nat, Native.treeValid valid steps base r = true ∧
      n ≤ r.1.size ∧ (r.1.toList.map key).Nodup :=
  ⟨(L.toArray, par.toArray, gen.toArray),
    treeValid_of_replay h valid fun y hy => List.all_eq_true.1 hv y hy,
    by simpa using hn, by simpa using nodup_map_of_posOK (replay_facts h).1⟩

theorem syl_tripleSteps_eq : Native.s0Tabs.map Native.imgTriple = sylTripleSteps := by
  unfold sylTripleSteps
  refine List.map_congr_left fun g _ => ?_
  funext x
  simp only [Native.imgTriple, sylTripleF, arr_getElem!]

theorem syl_ospSteps_eq : Native.lTabs.map Native.imgOSP = sylOSPSteps := by
  unfold sylOSPSteps
  refine List.map_congr_left fun g hg => ?_
  funext x
  have hf : Native.img g = imgF (imgTab g.toList) := funext (img_eq_imgF g (lTabs_lt g hg))
  simp only [Native.imgOSP, sylOSPF, Native.imgSext, imgSextF, sortL_eq_sortN, hf]

theorem syl_spSteps_eq : Native.genTabs.map Native.stepSp = sylSpSteps := by
  unfold sylSpSteps
  refine List.map_congr_left fun g hg => ?_
  funext L
  have hf : Native.toddAct g = toddActF (imgTab g.toList) := duad_toddAct_eq g (genTabs_lt g hg)
  simp only [Native.stepSp, sylSpF, sortL_eq_sortN, hf]

theorem syl_tripleOrbit_of {fuel : Nat} {L : List (Nat × Nat × Nat)} {par gen : List Nat}
    {pos : KTree (Nat × Nat)}
    (h : replayOK Native.keyTriple sylTripleSteps (0, 8, 16) fuel L par gen pos = true)
    (hl : 1024 ≤ L.length) (hv : L.all Native.validTriple = true) :
    ∃ r : Array (Nat × Nat × Nat) × Array Nat × Array Nat,
      Native.treeValid Native.validTriple (Native.s0Tabs.map Native.imgTriple) (0, 8, 16) r =
        true ∧ 1024 ≤ r.1.size ∧ (r.1.toList.map Native.keyTriple).Nodup := by
  rw [syl_tripleSteps_eq]
  exact syl_orbit_of _ h hl hv

theorem syl_tupleOrbit_of {fuel : Nat} {L : List Native.OSP} {par gen : List Nat}
    {pos : KTree (Nat × Nat)}
    (h : replayOK Native.keyOSP sylOSPSteps Native.tup0 fuel L par gen pos = true)
    (hl : 63 ≤ L.length) (hv : L.all Native.validOSP = true) :
    ∃ r : Array Native.OSP × Array Nat × Array Nat,
      Native.treeValid Native.validOSP (Native.lTabs.map Native.imgOSP) Native.tup0 r = true ∧
        63 ≤ r.1.size ∧ (r.1.toList.map Native.keyOSP).Nodup := by
  rw [syl_ospSteps_eq]
  exact syl_orbit_of _ h hl hv

theorem syl_spaceOrbit_of {fuel : Nat} {L : List (List Nat)} {par gen : List Nat}
    {pos : KTree (Nat × Nat)}
    (h : replayOK Native.keySp sylSpSteps Native.vpList fuel L par gen pos = true)
    (hl : 3796 ≤ L.length) (hv : L.all Native.validSp = true) :
    ∃ r : Array (List Nat) × Array Nat × Array Nat,
      Native.treeValid Native.validSp (Native.genTabs.map Native.stepSp) Native.vpList r = true ∧
        3796 ≤ r.1.size ∧ (r.1.toList.map Native.keySp).Nodup := by
  rw [syl_spSteps_eq]
  exact syl_orbit_of _ h hl hv

theorem syl_all_s0BT (m : Nat) (p : Nat → Nat → Bool) :
    (sylS0BT.all fun bt => p (toddActF bt m) m) =
      Native.s0Tabs.all fun a => p (Native.toddAct a m) m := by
  unfold sylS0BT
  rw [List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun a ha => ?_
  simp only [Function.comp_apply, syl_toddAct_eq ha]

theorem syl_fixed_of (h : sylFixedOn sylS0BT = true) :
    (∀ m < 2048, (∀ a ∈ Native.s0Tabs, Native.toddAct a m = m) → m = 0 ∨ m = 31) ∧
      ∀ a ∈ Native.s0Tabs, Native.toddAct a 31 = 31 := by
  unfold sylFixedOn at h
  rw [Bool.and_eq_true, allLt_iff'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun m hm hfix => ?_, ?_⟩
  · have hall : (sylS0BT.all fun bt => toddActF bt m == m) = true := by
      rw [syl_all_s0BT m fun x y => x == y, List.all_eq_true]
      exact fun a ha => beq_iff_eq.2 (hfix a ha)
    have := h1 m hm
    rw [hall] at this
    simpa using this
  · rw [syl_all_s0BT 31 fun x y => x == y, List.all_eq_true] at h2
    exact fun a ha => beq_iff_eq.1 (h2 a ha)

theorem sylSeen_spec : ∀ (cs : List Nat) (M : Nat), sylSeen cs M = true →
    cs.Nodup ∧ ∀ c ∈ cs, M.testBit c = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | c :: cs, M, h => by
    rw [sylSeen, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hc, h⟩ := h
    obtain ⟨hnd, hbits⟩ := sylSeen_spec cs _ h
    have hne : ∀ c' ∈ cs, c' ≠ c ∧ M.testBit c' = false := by
      intro c' hc'
      have := hbits c' hc'
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.one_shiftLeft, Nat.testBit_two_pow] at this
      exact ⟨fun e => by simp [e] at this, this.1⟩
    refine ⟨List.nodup_cons.2 ⟨fun hm => (hne c hm).1 rfl, hnd⟩, fun c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hc
    · exact (hne c' hc').2

theorem syl_sext_get {SL : List (List Nat)} (hS : Native.sextList () = SL.toArray) {q : Nat}
    (hq : q < SL.length) : (Native.sextList ())[q]! = SL[q] := by
  rw [hS, toArray_getElem!_eq_getD, duad_getD_lt _ _ hq]

theorem syl_cls_of {SL : List (List Nat)} (hS : Native.sextList () = SL.toArray)
    (h : sylClsF SL = true) : (Native.sextList ()).size = 1771 ∧
      (∀ q < 1771, ∀ q' < q, Native.clsOf (Native.sextList ())[q]! ≠
        Native.clsOf (Native.sextList ())[q']!) ∧ Native.clsOf Native.baseSext = 31 := by
  unfold sylClsF at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hl, hs⟩, hb⟩ := h
  have hnd := (sylSeen_spec _ 0 hs).1
  refine ⟨by simp [hS, hl], fun q hq q' hq' e => ?_, hb⟩
  rw [syl_sext_get hS (by omega), syl_sext_get hS (by omega)] at e
  have e' : (SL.map Native.clsOf)[q]'(by simp; omega) =
      (SL.map Native.clsOf)[q']'(by simp; omega) := by
    simpa using e
  have := hnd.getElem_inj_iff.1 e'
  omega

theorem syl_TS_length {TS : List (List Nat)} (hTS : Native.trioSexts () = TS.toArray) :
    TS.length = 3795 := by
  have := congrArg Array.size hTS
  simp only [Native.trioSexts, Array.size_map, Array.size_range, List.size_toArray,
    Native.nTrio] at this
  exact this.symm

theorem syl_TS_get {TS : List (List Nat)} (hTS : Native.trioSexts () = TS.toArray) {p : Nat}
    (hp : p < 3795) : TS.getD p [] = (List.range Native.nSext).filter fun q =>
      Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! := by
  have e := congrArg (fun A : Array (List Nat) => A[p]!) hTS
  simp only [toArray_getElem!_eq_getD] at e
  have e' : TS.getD p [] = (Native.trioSexts ())[p]! := e.symm
  rw [e']
  unfold Native.trioSexts
  rw [getElem!_pos _ p (by simp [Native.nTrio, hp])]
  simp

theorem syl_through_eq {TS : List (List Nat)} (hTS : Native.trioSexts () = TS.toArray)
    (hT0 : (Native.trioList ())[0]! = Native.baseTrio) :
    Native.sextsThrough (Native.sextList ()) Native.baseTrio = TS.headD [] := by
  rw [List.headD_eq_getD, syl_TS_get hTS (by decide), hT0]
  rfl

theorem syl_trioDet_of {TS : List (List Nat)} (hTS : Native.trioSexts () = TS.toArray)
    (hT0 : (Native.trioList ())[0]! = Native.baseTrio) (h : sylTrioDetF TS = true) :
    ∀ p < 3795, (∀ q ∈ Native.sextsThrough (Native.sextList ()) Native.baseTrio,
      Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! = true) → p = 0 := by
  intro p hp hall
  unfold sylTrioDetF at h
  have hrow := (allIdx_iff _ TS 0).1 h p (by rw [syl_TS_length hTS]; exact hp)
  simp only [Nat.zero_add, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hrow
  rcases hrow with h0 | hne
  · exact h0
  · exfalso
    have hsub : ((TS.headD []).all fun q => (TS.getD p default).contains q) = true := by
      rw [List.all_eq_true]
      intro q hq
      rw [← syl_through_eq hTS hT0] at hq
      have hq' := hq
      simp only [Native.sextsThrough, List.mem_filter, List.mem_range] at hq'
      have e : TS.getD p default = TS.getD p [] := rfl
      rw [e, syl_TS_get hTS hp, List.contains_iff_mem, List.mem_filter, List.mem_range]
      exact ⟨hq'.1, hall q hq⟩
    rw [hsub] at hne
    exact Bool.noConfusion hne

theorem syl_v0_of {SL TS : List (List Nat)} (hS : Native.sextList () = SL.toArray)
    (hTS : Native.trioSexts () = TS.toArray) (hT0 : (Native.trioList ())[0]! = Native.baseTrio)
    (h : sylV0F SL TS = true) :
    Native.sortL (0 :: (Native.sextsThrough (Native.sextList ()) Native.baseTrio).map
      fun q => Native.clsOf (Native.sextList ())[q]!) = Native.v0List ∧
      Native.closedXor Native.v0List = true ∧ Native.closedXor Native.vpList = true := by
  unfold sylV0F at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, h2, h3⟩
  rw [sortL_eq_sortN, syl_through_eq hTS hT0, hS]
  simp only [toArray_getElem!_eq_getD]
  exact h1

theorem syl_eq_of_xor {x y : Nat} (h : x ^^^ y = 0) : x = y := by
  have := congrArg (· ^^^ y) h
  simpa [Nat.xor_assoc] using this

theorem syl_xor_ne {x y : Nat} (h : x ^^^ y ≠ 0) : x ≠ y := fun e => h (by rw [e, Nat.xor_self])

theorem syl_sp8_nodup {v w : Nat} (h1 : v ≠ 0) (h2 : v ≠ 31) (h3 : w ≠ 0) (h4 : w ≠ 31)
    (h5 : w ≠ v) (h6 : w ≠ 31 ^^^ v) : (Native.sp8 v w).Nodup := by
  have a0 : (31 : Nat) ≠ 0 := by decide
  have a2 : 31 ^^^ v ≠ 0 := fun e => h2 (syl_eq_of_xor e).symm
  have a4 : 31 ^^^ w ≠ 0 := fun e => h4 (syl_eq_of_xor e).symm
  have a5 : v ^^^ w ≠ 0 := fun e => h5 (syl_eq_of_xor e).symm
  have a6 : 31 ^^^ (v ^^^ w) ≠ 0 := by
    rw [← Nat.xor_assoc]
    exact fun e => h6 (syl_eq_of_xor e).symm
  have lc : ∀ a b c : Nat, a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := fun a b c => by
    rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]
  have cc : ∀ a b : Nat, a ^^^ (a ^^^ b) = b := fun a b => by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  simp only [Native.sp8, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  and_intros
  all_goals
    apply syl_xor_ne
    simp only [Nat.xor_assoc, Nat.xor_comm, lc, cc, Nat.xor_self, Nat.xor_zero,
      Nat.zero_xor] at a2 a4 a5 a6 ⊢ <;> assumption

theorem syl_mem_of_move {v w u : Nat} (hu : u ∈ Native.sp8 v w) (h0 : u ≠ 0) (h1 : u ≠ 31)
    (h2 : u ≠ v) (h3 : u ≠ 31 ^^^ v) : w ∈ [u, u ^^^ 31, u ^^^ v, u ^^^ 31 ^^^ v] := by
  have lc : ∀ a b c : Nat, a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := fun a b c => by
    rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]
  have cc : ∀ a b : Nat, a ^^^ (a ^^^ b) = b := fun a b => by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  simp only [Native.sp8, List.mem_cons, List.not_mem_nil, or_false] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases hu with e | e | e | e | e | e | e | e
  · exact absurd e h0
  · exact absurd e h1
  · exact absurd e h2
  · exact absurd e h3
  · exact Or.inl e.symm
  · subst e
    refine Or.inr (Or.inl ?_)
    simp only [Nat.xor_assoc, Nat.xor_comm, lc, cc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor]
  · subst e
    refine Or.inr (Or.inr (Or.inl ?_))
    simp only [Nat.xor_assoc, Nat.xor_comm, lc, cc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor]
  · subst e
    refine Or.inr (Or.inr (Or.inr ?_))
    simp only [Nat.xor_assoc, Nat.xor_comm, lc, cc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor]

theorem syl_testBit_of_cls {SL : List (List Nat)} (hS : Native.sextList () = SL.toArray)
    (hSl : SL.length = 1771) {m : Nat}
    (h : ∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = m) :
    (sylClsMask SL).testBit m = true := by
  obtain ⟨q, hq, rfl⟩ := h
  rw [sylClsMask, testBit_orMask, syl_sext_get hS (by omega), List.contains_iff_mem]
  exact List.mem_map_of_mem (List.getElem_mem _)

theorem syl_span_of {SL : List (List Nat)} (hS : Native.sextList () = SL.toArray)
    (hSl : SL.length = 1771) (h : sylSpanOn (sylClsMask SL) = true) :
    ∀ v < 2048, ∀ w < 2048, v ≠ 0 → v ≠ 31 → w ≠ 0 → w ≠ 31 → w ≠ v → w ≠ 31 ^^^ v →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = v) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = 31 ^^^ v) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = w) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = 31 ^^^ w) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = v ^^^ w) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = 31 ^^^ v ^^^ w) →
      (Native.sp8 v w).Nodup ∧
      ((∀ a ∈ Native.s0Tabs, Native.toddAct a v ∈ Native.sp8 v w ∧
          Native.toddAct a w ∈ Native.sp8 v w) →
        Native.sortL (Native.sp8 v w) = Native.v0List ∨
          Native.sortL (Native.sp8 v w) = Native.vpList) := by
  intro v hv w hw h1 h2 h3 h4 h5 h6 c1 c2 c3 c4 c5 c6
  refine ⟨syl_sp8_nodup h1 h2 h3 h4 h5 h6, fun hinv => ?_⟩
  have t1 := syl_testBit_of_cls hS hSl c1
  have t2 := syl_testBit_of_cls hS hSl c2
  have hcand : sylCand (sylClsMask SL) v w = true := by
    unfold sylCand
    simp only [Bool.and_eq_true, t1, t2, syl_testBit_of_cls hS hSl c3,
      syl_testBit_of_cls hS hSl c4, syl_testBit_of_cls hS hSl c5, syl_testBit_of_cls hS hSl c6,
      bne_iff_ne, ne_eq, h1, h2, h3, h4, h5, h6, not_false_eq_true, and_self]
  have hinvB : sylInv v w = true := by
    unfold sylInv
    rw [List.all_eq_true]
    intro bt hbt
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hbt
    rw [← syl_toddAct_eq ha, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem]
    exact hinv a ha
  have hrow : sylRow (sylClsMask SL) v w = true →Native.sortL (Native.sp8 v w) = Native.v0List ∨
      Native.sortL (Native.sp8 v w) = Native.vpList := by
    intro hr
    unfold sylRow at hr
    simp only [hcand, hinvB, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hr
    rwa [sortL_eq_sortN]
  have hpre : ((sylClsMask SL).testBit v && (sylClsMask SL).testBit (31 ^^^ v) && v != 0 &&
      v != 31) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, t1, t2, h1, h2, not_false_eq_true, and_self]
  have hV := allLt_iff'.1 h v hv
  unfold sylSpanV at hV
  rw [hpre, Bool.not_true, Bool.false_or] at hV
  revert hV
  cases hm : sylMove v with
  | none =>
    intro hV
    have hV' : Native.allLt 2048 (sylRow (sylClsMask SL) v) = true := hV
    exact hrow (allLt_iff'.1 hV' w hw)
  | some u =>
    intro hV
    have hV' : [u, u ^^^ 31, u ^^^ v, u ^^^ 31 ^^^ v].all (sylRow (sylClsMask SL) v) = true := hV
    unfold sylMove at hm
    have hp := List.find?_some hm
    obtain ⟨bt, hbt, hu⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hm)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hbt
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hp
    obtain ⟨⟨⟨p0, p1⟩, p2⟩, p3⟩ := hp
    have huin : u ∈ Native.sp8 v w := by
      rw [← hu, ← syl_toddAct_eq ha]
      exact (hinv a ha).1
    exact hrow (List.all_eq_true.1 hV' w (syl_mem_of_move huin p0 p1 p2 p3))

end CFSG.KC.M24G
