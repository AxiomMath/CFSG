module

public import Certificates.Data.Kernel.M24G.Trio12
public import CFSG.Certificates.Kernel.M24G.ListChecksSound
public import CFSG.Certificates.Kernel.M24G.DualSound
public import CFSG.Certificates.Kernel.M24G.BfsFacts

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem tTabs_lt : ∀ t ∈ Native.tTabs, ∀ x ∈ t.toList, x < 24 := by decide

theorem lTabs_lt24 : ∀ t ∈ Native.lTabs, ∀ x ∈ t.toList, x < 24 := by decide

theorem imgTrio_octsT_lt {g : Array Nat} (hg : ∀ x ∈ g.toList, x < 24) (t : Nat × Nat × Nat) :
    ∀ x ∈ Native.octsT (Native.imgTrio g t), x < 2 ^ 24 := by
  intro x hx
  rcases mem_sort3 hx with rfl | rfl | rfl <;> exact img_lt hg _

theorem getD_map_eq {β γ : Type} [Inhabited γ] (f : β → γ) {l : List β} {k : Nat}
    (hk : k < l.length) : (l.map f).getD k default = f l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

theorem trio12_getD_eq_getElem {β : Type} (l : List β) (d : β) {k : Nat} (hk : k < l.length) :
    l.getD k d = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem reachOK_of_replay {steps : List (Nat → Nat)} {n base : Nat} {L par gen : List Nat}
    {pos : KTree (Nat × Nat)} (hr : replayOK (fun i => i) steps base 5000 L par gen pos = true)
    (hn : ∀ q ∈ L, q < n) {c : List Nat} (hc : ∀ q ∈ c, q ∈ L) :
    Native.reachOK n steps base c = true := by
  refine reachOK_of_tree ?_ ?_ <;> rw [bfs_eq_of_replayOK hr]
  · intro j hj
    dsimp only at hj ⊢
    rw [List.size_toArray] at hj
    rw [toArray_getElem! L hj]
    exact hn _ (List.getElem_mem hj)
  · intro q hq
    dsimp only
    exact hc q hq

theorem nodup_of_posOK {L : List Nat} {pos : KTree (Nat × Nat)}
    (h : posOK (fun i => i) L pos = true) : L.Nodup := by
  refine List.pairwise_iff_getElem.2 fun i j hi hj hij e => ?_
  have := posOK_inj h hi hj e
  omega

theorem genFixF_spec {bs : List (Nat × Nat × Nat)} {SL : List (List Nat)} {B : List Nat}
    (h : genFixF bs SL B = true) :
    B.length = 7 ∧ ∀ b ∈ bs, ((imgF b 255 = 255 ∧ imgF b 65280 = 65280) ∧
      imgF b 16711680 = 16711680) ∧
      ∀ q ∈ B, sortN ((SL.getD q []).map (imgF b)) = SL.getD q [] := by
  unfold genFixF at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h

section Lists

variable {O oP oG : List Nat} {posO : KTree (Nat × Nat)}
  (hO : replayOK id (Native.genTabs.map Native.img) 255 1000 O oP oG posO = true)
  (hOl : O.length = 759) (hOi : O.all octItem = true) (hB : baseOK posO = true)
  {T : List (Nat × Nat × Nat)} {tP tG : List Nat} {posT : KTree (Nat × Nat)}
  (hT : replayOK Native.key3 (Native.genTabs.map Native.imgTrio) Native.baseTrio 5000 T tP tG posT =
    true)
  (hTl : T.length = 3795)
  {S : List (List Nat)} {sP sG : List Nat} {posS : KTree (Nat × Nat)}
  (hS : replayOK Native.keyL (Native.genTabs.map Native.imgSext) Native.baseSext 3000 S sP sG posS =
    true)
  (hSl : S.length = 1771) (hSi : S.all sextItem = true)

include hS hSl in
theorem genFixCheck_of {B : List Nat}
    (hB7 : allIdx (fun i x => Native.trioIn Native.baseTrio x == B.contains i) S 0 = true)
    (hasc : ascL B = true) (hlt : ∀ x ∈ B, x < Native.nSext)
    (hg : genFixF (Native.tTabs.map fun t => imgTab t.toList) S B = true) :
    Native.genFixCheck () = true := by
  unfold Native.genFixCheck Native.sextsOfBase
  dsimp only
  have hBe : (List.range Native.nSext).filter (fun q => Native.trioIn Native.baseTrio S.toArray[q]!) =
      B :=
    filter_range_eq_of_allIdx (f := fun x => Native.trioIn Native.baseTrio x) hSl hB7 hasc hlt
  rw [sextList_of hS, hBe]
  obtain ⟨h7, hall⟩ := genFixF_spec hg
  simp only [toArray_getElem!_eq_getD, Native.imgSext, sortL_eq_sortN]
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨h7, fun t ht => ?_⟩
  have hf : Native.img t = imgF (imgTab t.toList) := funext (img_eq_imgF t (tTabs_lt t ht))
  rw [hf]
  exact hall _ (List.mem_map_of_mem ht)

include hS hSl hSi in
theorem baseSextCheck_of
    (hb : [Native.baseSext, Native.sextU2, Native.sextU3].all
      (fun U => Native.trioIn Native.baseTrio U && S.contains U) = true) :
    Native.baseSextCheck () = true := by
  unfold Native.baseSextCheck
  rw [List.all_eq_true] at hb ⊢
  intro U hU
  have h := hb U hU
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have hl : U.length = 6 ∧ ∀ B ∈ U, B < 2 ^ 24 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hU
    rcases hU with rfl | rfl | rfl <;> decide
  rw [decide_eq_true_eq, sextIdx_of hS hSl hSi U hl.1 hl.2]
  exact idxK_mem (key := Native.keyL) (replay_facts hS).1 hSl (List.contains_iff_mem.1 h.2)

theorem imgTrio_default : ∀ t ∈ Native.tTabs, Native.imgTrio t default = (0, 0, 0) := by decide

include hO hOl hOi hB hT hTl in
theorem trioSteps_tTabs {PI : List Nat}
    (hc : closeOK (Native.tTabs.map fun t => imgTab t.toList) PI posT T = true)
    (h0 : idxK posT 3795 0 = 3795) :
    Native.trioSteps Native.tTabs = piSteps PI := by
  unfold Native.trioSteps piSteps
  dsimp only
  rw [trioList_of hT]
  unfold closeOK at hc
  rw [Bool.and_eq_true, beq_iff_eq, List.length_map, allIdx_iff] at hc
  obtain ⟨hlen, hc⟩ := hc
  apply List.ext_getElem
  · rw [List.length_map, List.length_map, hlen]
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_map]
    rw [List.length_map] at h1
    have ht : Native.tTabs[k] ∈ Native.tTabs := List.getElem_mem h1
    funext i
    unfold stepP
    split
    · rename_i hi
      have hi' : i < T.length := by omega
      have hk := hc i hi'
      rw [Nat.zero_add, allIdx_iff] at hk
      have hk' := hk k (by rw [List.length_map]; exact h1)
      rw [Nat.zero_add, Bool.and_eq_true, beq_iff_eq, getD_map_eq _ h1] at hk'
      rw [toArray_getElem!_eq_getD,
        trioIdx_of hO hOl hOi hB hT hTl _ (imgTrio_octsT_lt (tTabs_lt _ ht) _)]
      have e : Native.imgTrio Native.tTabs[k] (T.getD i default) =
          imgTrioB (imgTab Native.tTabs[k].toList) (T.getD i default) := by
        unfold Native.imgTrio imgTrioB
        rw [img_eq_imgF _ (tTabs_lt _ ht), img_eq_imgF _ (tTabs_lt _ ht),
          img_eq_imgF _ (tTabs_lt _ ht)]
      rw [e, hk'.2, trio12_getD_eq_getElem _ _ (by omega)]
    · rename_i hi
      have hd : T.getD i default = default := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [toArray_getElem!_eq_getD, hd,
        imgTrio_default _ ht, trioIdx_of hO hOl hOi hB hT hTl _ (by decide)]
      exact h0

theorem piSteps_closed {bs : List (Nat × Nat × Nat)} {PI : List Nat}
    {posT : KTree (Nat × Nat)} {T : List (Nat × Nat × Nat)} (hTl : T.length = 3795)
    (hc : closeOK bs PI posT T = true) : ∀ s ∈ piSteps PI, ∀ i < 3795, s i < 3795 := by
  unfold closeOK at hc
  rw [Bool.and_eq_true, beq_iff_eq, allIdx_iff] at hc
  obtain ⟨hlen, hc⟩ := hc
  intro s hs i hi
  unfold piSteps at hs
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hs
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hP
  have h := hc i (by omega)
  rw [Nat.zero_add, allIdx_iff] at h
  have h' := h k (by omega)
  rw [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq, trio12_getD_eq_getElem _ _ hk] at h'
  unfold stepP
  rw [if_pos hi]
  exact h'.1

theorem orbOK_sound {st : List (Nat → Nat)} (hcl : ∀ s ∈ st, ∀ i < 3795, s i < 3795) {p : Nat}
    (hp : p < 3795) (h : orbOK st p = true) :
    (Native.orbitFive st p).length = 5 ∧ (Native.orbitFive st p).Nodup ∧
      (∀ q ∈ Native.orbitFive st p, q < 3795) ∧
      Native.reachOK 3795 st p (Native.orbitFive st p) = true := by
  unfold orbOK at h
  dsimp only at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h5, hnd⟩, hlt⟩, hr⟩ := h
  have e : Native.orbitFive st p = (exp1 st p).1.take 5 := by
    unfold Native.orbitFive
    rw [bfs_eq_of_replayOK hr]
  refine ⟨by rw [e]; exact h5, by rw [e]; exact hnd, fun q hq => hlt q (by rw [← e]; exact hq),
    reachOK_of_closed hp hcl fun q hq => ?_⟩
  unfold Native.orbitFive at hq
  exact (bfs_prefix (fun i => i) st p (by decide : 1 ≤ 5000)).subset (List.mem_of_mem_take hq)

include hT hTl in
theorem trioOrbitCheck_of {PI : List Nat} (hsteps : Native.trioSteps Native.tTabs = piSteps PI)
    (hcl : ∀ s ∈ piSteps PI, ∀ i < 3795, s i < 3795) (h0T : T.getD 0 default = Native.baseTrio)
    (horb : trioOrbF (piSteps PI) T = true) : Native.trioOrbitCheck () = true := by
  unfold Native.trioOrbitCheck
  dsimp only
  rw [trioList_of hT, hsteps, range_all_iff]
  intro p hp
  unfold trioOrbF at horb
  rw [allIdx_iff] at horb
  have hp' : p < T.length := by rw [hTl]; exact hp
  have hq := horb p hp'
  rw [Nat.zero_add, Bool.or_eq_true] at hq
  rw [toArray_getElem!_eq_getD, toArray_getElem!_eq_getD, h0T, Bool.or_eq_true]
  rcases hq with hq | hq
  · exact Or.inl hq
  · right
    obtain ⟨a, b, c, d⟩ := orbOK_sound hcl (by omega) hq
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨⟨a, b⟩, c⟩, d⟩

include hS hSl hSi in
theorem sext_img_idx {g : Array Nat} (hg : ∀ x ∈ g.toList, x < 24) {s : List Nat} (hs : s ∈ S) :
    Native.sextIdx (Native.imgSext g s) =
      idxK posS 1771 (Native.keyL (sortN (s.map (imgF (imgTab g.toList))))) := by
  have hsl := sextItem_facts (List.all_eq_true.1 hSi s hs)
  have hl : (Native.imgSext g s).length = 6 := by
    unfold Native.imgSext
    rw [length_sortL, List.length_map, hsl.1]
  have hb : ∀ B ∈ Native.imgSext g s, B < 2 ^ 24 := by
    intro B hB
    unfold Native.imgSext at hB
    rw [mem_sortL, List.mem_map] at hB
    obtain ⟨b, -, rfl⟩ := hB
    exact img_lt hg _
  rw [sextIdx_of hS hSl hSi _ hl hb]
  have hf : Native.img g = imgF (imgTab g.toList) := funext (img_eq_imgF g hg)
  unfold Native.imgSext
  rw [sortL_eq_sortN, hf]

theorem trio12_getD_mem {β : Type} [Inhabited β] {l : List β} {i : Nat} (hi : i < l.length) :
    l.getD i default ∈ l := by
  rw [trio12_getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

include hO hOl hS hSl hSi in
theorem stepTup_eq {g : Array Nat} (hg : ∀ x ∈ g.toList, x < 24) (c : Nat) :
    Native.stepTup O.toArray S.toArray g c = stepTupF O posO S posS (imgTab g.toList) c := by
  unfold Native.stepTup stepTupF
  dsimp only
  have hf : Native.img g = imgF (imgTab g.toList) := funext (img_eq_imgF g hg)
  have hm : ∀ i, S.getD (i % 1771) default ∈ S := fun i =>
    trio12_getD_mem (by rw [hSl]; exact Nat.mod_lt _ (by decide))
  simp only [arr_getElem! O.toArray, List.toList_toArray, toArray_getElem!_eq_getD S,
    octIdx_of hO hOl, sext_img_idx hS hSl hSi hg (hm _), hf]
  rfl

include hO hOl hS hSl hSi in
theorem tupSteps_lTabs :
    Native.tupSteps Native.lTabs =
      tupStepsF O posO S posS (Native.lTabs.map fun t => imgTab t.toList) := by
  unfold Native.tupSteps tupStepsF
  dsimp only
  rw [octList_of hO, sextList_of hS, List.map_map]
  refine List.map_congr_left fun g hg => ?_
  funext c
  exact stepTup_eq hO hOl hS hSl hSi (lTabs_lt24 g hg) c

include hO hOl hS hSl hSi in
theorem x0Code_eq : Native.x0Code () = x0F posO posS := by
  unfold Native.x0Code x0F
  rw [octIdx_of hO hOl, octIdx_of hO hOl, sextIdx_of hS hSl hSi _ (by decide) (by decide),
    sextIdx_of hS hSl hSi Native.sextU2 (by decide) (by decide),
    sextIdx_of hS hSl hSi Native.sextU3 (by decide) (by decide)]

include hO hOl hS hSl hSi in
theorem tupOrbitCheck_of {U uPar uGen : List Nat}
    (ht : tupOK O posO S posS (Native.lTabs.map fun t => imgTab t.toList) U uPar uGen = true) :
    Native.tupOrbitCheck () = true := by
  unfold tupOK at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
  obtain ⟨⟨h1008, hlt⟩, hr⟩ := ht
  obtain ⟨hpos, hb, -, -, -, -⟩ := replay_facts hr
  have hx : x0F posO posS ∈ U := List.mem_of_mem_head? hb
  unfold Native.tupOrbitCheck Native.orbitTup
  dsimp only
  rw [x0Code_eq hO hOl hS hSl hSi, tupSteps_lTabs hO hOl hS hSl hSi, bfs_eq_of_replayOK hr]
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨hlt _ hx, h1008⟩, nodup_of_posOK hpos⟩, hlt⟩,
    reachOK_of_replay hr hlt fun q hq => hq⟩

end Lists

end CFSG.KC.M24G
