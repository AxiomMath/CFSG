module

public import Certificates.Data.Kernel.AS91K45.Defs
public import CFSG.Certificates.Kernel.HJ12KTSound
public import CFSG.Quasithin.H13.AS91Sec4FourInputs
public import CFSG.GF2Type.Smith1979.GammaU.PairBridge

public section

namespace Certificates.Kernel.AS91K45

open CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.Quasithin.H13.MatNCert Certificates.Kernel.HJ12K
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.Quasithin.H13.AS91

theorem appN_A (X n : ℕ) : appN (unpackA X) n = mvNR (unpackQ X) n := by
  rw [← native_appN]
  exact appN_unpackA X n

theorem appN_fA (X : ℕ) : appN (unpackA X) = mvNR (unpackQ X) := funext (appN_A X)

theorem mulR_A (X Y : ℕ) : mulR (unpackA X) (unpackA Y) = unpackA (mulQ X Y) := by
  rw [← native_mulR]
  exact mulR_unpackA X Y

theorem idR_A : idR = unpackA oneQ := by
  rw [← native_idR]
  exact idR_eq

theorem enumGrp_A (gs : List ℕ) :
    enumGrp (gs.map unpackA) = (enumQ gs).map unpackA ∧ ∀ q ∈ enumQ gs, q < 2 ^ 144 := by
  rw [← native_enumGrp]
  exact enumGrp_eq gs

theorem closedCheck_A (gs X : List ℕ) (hX : ∀ q ∈ X, q < 2 ^ 144) :
    closedCheck (gs.map unpackA) (X.map unpackA) = closedQ gs X := by
  rw [← native_closedCheck]
  exact closedCheck_eq gs X hX

theorem gensOKb_of (gs : List ℕ) (h : gensOKQ gs = true) : Two.gensOKb (gs.map unpackA) = true := by
  have := gensOKN_of gs h
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12.gensOKN, native_okRows, native_invR,
    native_mulR, native_idR] at this
  exact this

theorem nGensI_eq : Two.nGensI = nGensQ.map unpackA := by decide

theorem nGensL_eq : nGensQ.map unpackQ = nGensL := by decide

theorem pRows_eq : Two.pRows = pQ.map unpackA := by decide

theorem gZRows_eq : Two.gZRows = gZQ.map unpackA := by decide

theorem p2Rows_eq : Two.p2Rows = p2Q.map unpackA := by decide

theorem omegaRows_eq : CFSG.GF2Type.Smith1979.IdxFour.omegaRows = unpackA omegaQ := by decide

theorem w1List_eq : Two.w1List = w1L := rfl

theorem maskOf_eq (L : List ℕ) : Two.maskOf L = maskOf 0 L := rfl

theorem pQ_lt : ∀ g ∈ pQ, g < 2 ^ 144 := by decide

theorem gZQ_lt : ∀ g ∈ gZQ, g < 2 ^ 144 := by decide

theorem p2Q_lt : ∀ g ∈ p2Q, g < 2 ^ 144 := by decide

theorem omegaQ_lt : omegaQ < 2 ^ 144 := by decide

theorem w1L_lt : ∀ c ∈ w1L, c < 4096 := by decide

theorem nGensL_lt : ∀ A ∈ nGensL, ∀ c ∈ A, c < 2 ^ 12 := by decide

theorem wordRows_A (gs : List ℕ) : ∀ w : List ℕ, (∀ i ∈ w, i < gs.length) →
    CFSG.GF2Type.Smith1979.IdxFour.wordRows (gs.map unpackA) w = unpackA (wordP gs w)
  | [], _ => by
    rw [CFSG.GF2Type.Smith1979.IdxFour.wordRows, wordP, List.map_nil, List.map_nil, List.foldr_nil,
      List.foldr_nil, idR_A]
  | i :: w, h => by
    have hi : i < gs.length := h i List.mem_cons_self
    have ih := wordRows_A gs w fun j hj => h j (List.mem_cons_of_mem i hj)
    rw [CFSG.GF2Type.Smith1979.IdxFour.wordRows] at ih ⊢
    rw [wordP] at ih ⊢
    rw [List.map_cons, List.map_cons, List.foldr_cons, List.foldr_cons, ih]
    have hg : (gs.map unpackA)[i]! = unpackA (gs.getD i oneQ) := by
      rw [getElem!_pos (gs.map unpackA) i (by rw [List.length_map]; exact hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi]
    rw [hg, mulR_A]

theorem stab1Gens_eq (h : stab1OK = true) : Two.stab1Gens () = stab1Q.map unpackA := by
  rw [stab1OK, beq_iff_eq] at h
  rw [← h, Two.stab1Gens, nGensI_eq, List.map_map]
  have hw : Two.stab1Words = stab1W := rfl
  rw [hw]
  refine List.map_congr_left fun w hw => ?_
  rw [Function.comp_apply]
  refine wordRows_A nGensQ w fun i hi => ?_
  have hb : ∀ w ∈ stab1W, ∀ i ∈ w, i < 6 := by decide
  exact hb w hw i hi

theorem foldl_img_testBit (m y : ℕ) (g : Array ℕ) : ∀ (L : List ℕ) (a : ℕ),
    (L.foldl (fun acc x => if m.testBit x then acc ||| 1 <<< appN g x else acc) a).testBit y =
      (a.testBit y || L.any fun x => m.testBit x && appN g x == y)
  | [], a => by simp
  | x :: L, a => by
    rw [List.foldl_cons, foldl_img_testBit m y g L, List.any_cons]
    by_cases hp : m.testBit x = true
    · rw [if_pos hp, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases h : appN g x = y
      · subst h
        simp [hp]
      · have h' : (appN g x == y) = false := beq_false_of_ne h
        simp [h, h']
    · rw [if_neg hp]
      simp [hp]

theorem testBit_maskOf0 (L : List ℕ) (s : ℕ) : (maskOf 0 L).testBit s = L.contains s := by
  rw [maskOf_testBit, Nat.zero_testBit, Bool.false_or]

theorem imgMask_maskOf (g : Array ℕ) (cs : List ℕ) (hcs : ∀ c ∈ cs, c < 4096) :
    Two.imgMask g (maskOf 0 cs) = maskOf 0 (cs.map (appN g)) := by
  apply Nat.eq_of_testBit_eq
  intro y
  rw [Two.imgMask, foldl_img_testBit, Nat.zero_testBit, Bool.false_or, testBit_maskOf0,
    Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, -, hx⟩
    rw [Bool.and_eq_true, testBit_maskOf0, List.contains_iff_mem, beq_iff_eq] at hx
    exact ⟨x, hx.1, hx.2⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, List.mem_range.2 (hcs x hx), ?_⟩
    rw [Bool.and_eq_true, testBit_maskOf0, List.contains_iff_mem, beq_iff_eq]
    exact ⟨hx, rfl⟩

@[expose] def PC (cs : List ℕ) : Prop := ∀ c ∈ cs, c < 4096

@[expose] def SeenT (h : Std.HashSet ℕ) (t : NT ℕ) : Prop := ∀ k, h.contains k = memP t k

theorem foldl_stepW : ∀ (L : List (List ℕ)), (∀ s ∈ L, PC s) →
    ∀ (l : List (List ℕ)) (h : Std.HashSet ℕ) (t : NT ℕ), (∀ s ∈ l, PC s) → SeenT h t →
      ((L.map (maskOf 0)).foldl HJ12K.stepH (l.map (maskOf 0), h)).1 =
          (L.foldl stepW (l, t)).1.map (maskOf 0) ∧
        SeenT ((L.map (maskOf 0)).foldl HJ12K.stepH (l.map (maskOf 0), h)).2 (L.foldl stepW (l, t)).2 ∧
        ∀ s ∈ (L.foldl stepW (l, t)).1, PC s
  | [], _, l, h, t, hl, hr => ⟨rfl, hr, hl⟩
  | x :: L, hL, l, h, t, hl, hr => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hc : h.contains (maskOf 0 x) = memP t (maskOf 0 x) := hr (maskOf 0 x)
    have hL' : ∀ s ∈ L, PC s := fun s hs => hL s (List.mem_cons_of_mem x hs)
    by_cases hm : memP t (maskOf 0 x) = true
    · have e1 : HJ12K.stepH (l.map (maskOf 0), h) (maskOf 0 x) = (l.map (maskOf 0), h) := by
        simp only [HJ12K.stepH, id, hc, hm, if_true]
      have e2 : stepW (l, t) x = (l, t) := by simp only [stepW, stepWK, hm, if_true]
      rw [e1, e2]
      exact foldl_stepW L hL' l h t hl hr
    · have hm' : memP t (maskOf 0 x) = false := by simpa using hm
      have e1 : HJ12K.stepH (l.map (maskOf 0), h) (maskOf 0 x) =
          ((x :: l).map (maskOf 0), h.insert (maskOf 0 x)) := by
        simp only [HJ12K.stepH, id, hc, hm', Bool.false_eq_true, if_false, List.map_cons]
      have e2 : stepW (l, t) x = (x :: l, insP t (maskOf 0 x)) := by
        simp only [stepW, stepWK, hm', Bool.false_eq_true, if_false]
      rw [e1, e2]
      refine foldl_stepW L hL' (x :: l) _ _ ?_ ?_
      · intro s hs
        rcases List.mem_cons.1 hs with rfl | hs
        · exact hL _ List.mem_cons_self
        · exact hl s hs
      · intro k
        rw [Std.HashSet.contains_insert, memP_insP, hr k]

theorem flat_W (fs : List (ℕ → ℕ)) (fs' : List (List ℕ → List ℕ))
    (hfs : ∀ s, PC s → fs.map (fun f => f (maskOf 0 s)) = fs'.map (fun f => maskOf 0 (f s))) :
    ∀ fr : List (List ℕ), (∀ s ∈ fr, PC s) →
      (fr.map (maskOf 0)).flatMap (fun s => fs.map fun f => f s) =
        (fr.flatMap fun s => fs'.map fun f => f s).map (maskOf 0)
  | [], _ => rfl
  | s :: fr, h => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append,
      flat_W fs fs' hfs fr fun t ht => h t (List.mem_cons_of_mem s ht), hfs s (h s List.mem_cons_self),
      List.map_map]
    rfl

theorem closW_eq (fs : List (ℕ → ℕ)) (fs' : List (List ℕ → List ℕ))
    (hfs : ∀ s, PC s → fs.map (fun f => f (maskOf 0 s)) = fs'.map (fun f => maskOf 0 (f s)))
    (hP : ∀ f ∈ fs', ∀ s, PC s → PC (f s)) :
    ∀ (fuel : ℕ) (fr vis : List (List ℕ)) (h : Std.HashSet ℕ) (t : NT ℕ), (∀ s ∈ fr, PC s) →
      (∀ s ∈ vis, PC s) → SeenT h t →
      bfsClosure (fun x : ℕ => x) fs fuel (fr.map (maskOf 0)) h (vis.map (maskOf 0)) =
          (closW fs' fuel fr t vis).map (maskOf 0) ∧ ∀ s ∈ closW fs' fuel fr t vis, PC s
  | 0, fr, vis, h, t, hfr, hvis, _ => by
    refine ⟨by rw [bfsClosure, closW, List.map_append], fun q hq => ?_⟩
    rw [closW] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hfr q hq
    · exact hvis q hq
  | fuel + 1, fr, vis, h, t, hfr, hvis, hr => by
    have himg : ∀ s ∈ fr.flatMap (fun s => fs'.map fun f => f s), PC s := by
      intro s hs
      obtain ⟨u, hu, hs⟩ := List.mem_flatMap.1 hs
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hs
      exact hP f hf u (hfr u hu)
    have hfv : ∀ q ∈ fr ++ vis, PC q := fun q hq => by
      rcases List.mem_append.1 hq with hq | hq
      · exact hfr q hq
      · exact hvis q hq
    have e1 : bfsRound (fun x : ℕ => x) fs (fr.map (maskOf 0)) h =
        (((fr.flatMap fun s => fs'.map fun f => f s).map (maskOf 0)).foldl HJ12K.stepH
          (([] : List (List ℕ)).map (maskOf 0), h)) := by
      rw [bfsRound, flat_W fs fs' hfs fr hfr]
      rfl
    have e2 : roundW fs' fr t = (fr.flatMap fun s => fs'.map fun f => f s).foldl stepW ([], t) :=
      rfl
    obtain ⟨r1, r2, r3⟩ := foldl_stepW _ himg [] h t (by simp) hr
    rw [bfsClosure, closW, e1, e2, r1, List.isEmpty_map]
    split_ifs
    · exact ⟨by rw [List.map_append], hfv⟩
    · rw [← List.map_append]
      exact closW_eq fs fs' hfs hP fuel _ _ _ _ r3 hfv r2

theorem mvNR_lt {A : List ℕ} (hA : ∀ c ∈ A, c < 2 ^ 12) (v : ℕ) : mvNR A v < 4096 := by
  rw [mvNR_eq]
  exact mvN_lt A v hA

theorem w1Orbit_eq : Two.w1Orbit () = orbW.map (maskOf 0) ∧ ∀ s ∈ orbW, PC s := by
  have hfs : ∀ s, PC s → (Two.nGensI.map Two.imgMask).map (fun f => f (maskOf 0 s)) =
      imgFs.map (fun f => maskOf 0 (f s)) := by
    intro s hs
    rw [imgFs, ← nGensL_eq, nGensI_eq, List.map_map, List.map_map, List.map_map, List.map_map]
    refine List.map_congr_left fun X _ => ?_
    simp only [Function.comp_apply]
    rw [imgMask_maskOf _ s hs, appN_fA]
  have hP : ∀ f ∈ imgFs, ∀ s, PC s → PC (f s) := by
    intro f hf s _ c hc
    rw [imgFs] at hf
    obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hf
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc
    exact mvNR_lt (nGensL_lt A hA) x
  have hseen : SeenT ((∅ : Std.HashSet ℕ).insert (maskOf 0 w1L)) (insP (.tip []) (maskOf 0 w1L)) := by
    intro k
    rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty]
  have := closW_eq (Two.nGensI.map Two.imgMask) imgFs hfs hP 100 [w1L] [] _ _
    (fun s hs => by rw [List.mem_singleton.1 hs]; exact w1L_lt) (by simp) hseen
  rw [Two.w1Orbit, Two.w1Mask, maskOf_eq, w1List_eq]
  exact this

theorem contains_A (gs : List ℕ) {y : ℕ} (hy : y < 2 ^ 144) :
    (enumGrp (gs.map unpackA)).contains (unpackA y) = (enumQ gs).contains y := by
  rw [(enumGrp_A gs).1, contains_map (enumGrp_A gs).2 hy]

theorem setContains_A (gs : List ℕ) {y : ℕ} (hy : y < 2 ^ 144) :
    (Std.HashSet.ofList (enumGrp (gs.map unpackA))).contains (unpackA y) =
      memP (ofListP (enumQ gs)) y := by
  rw [Std.HashSet.contains_ofList, contains_A gs hy, memP_ofListP]

theorem memAll_of (gs ps : List ℕ) (hb : ∀ p ∈ ps, p < 2 ^ 144)
    (h : memAll (ofListP (enumQ gs)) ps = true) :
    (ps.map unpackA).all (fun p => (Std.HashSet.ofList (enumGrp (gs.map unpackA))).contains p) =
      true := by
  rw [all_map_congr fun p hp => setContains_A gs (hb p hp)]
  exact h

theorem grpAt_sound (gs : List ℕ) (n : ℕ) (h : grpAt gs (enumQ gs) n = true) :
    Two.gensOKb (gs.map unpackA) = true ∧ (enumGrp (gs.map unpackA)).contains idR = true ∧
      closedCheck (gs.map unpackA) (enumGrp (gs.map unpackA)) = true ∧
      ((enumGrp (gs.map unpackA)).dedup.length == n) = true := by
  obtain ⟨hE, hEv⟩ := enumGrp_A gs
  rw [grpAt] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨gensOKb_of gs h1, ?_, ?_, ?_⟩
  · rw [idR_A, contains_A gs oneQ_lt]
    exact h2
  · rw [hE, closedCheck_A gs _ hEv]
    exact h3
  · rw [hE, dedup_length hEv h4, nat_beq]
    exact h5

theorem testBit_nine : ∀ n : ℕ, Nat.testBit 9 n = (n == 0 || n == 3)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n + 4 => by
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : 9 < 2 ^ 4)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp

theorem fixAll_testBit (gs : List ℕ) {n : ℕ} (hn : n < 4096) :
    (fixAll gs).testBit n = (gs.map unpackA).all fun g => appN g n == n := by
  rw [fixAll, foldl_and_testBit, fullM_testBit hn, Bool.true_and, List.all_map]
  refine congrArg gs.all (funext fun g => ?_)
  rw [Function.comp_apply, fixMask_testBit g hn, appN_A, nat_beq]

theorem fix_sound (gs : List ℕ) (h : Nat.beq (fixAll gs) 9 = true) :
    (List.range 4096).all (fun n => ((gs.map unpackA).all fun g => appN g n == n) ==
      (n == 0 || n == 3)) = true := by
  rw [List.all_eq_true]
  intro n hn
  rw [← fixAll_testBit gs (List.mem_range.1 hn), Nat.eq_of_beq_eq_true h, testBit_nine,
    beq_self_eq_true]

theorem z_sound (gs : List ℕ)
    (h : gs.all (fun g => [0, 3, 192, 195].all fun n =>
      [0, 3, 192, 195].contains (mvNR (unpackQ g) n)) = true) :
    (gs.map unpackA).all (fun g => Two.zList.all fun n => Two.zList.contains (appN g n)) = true := by
  rw [all_map_congr fun g _ => by rw [appN_fA]]
  exact h

theorem img_sound (W : List ℕ) (hW : ∀ c ∈ W, c < 4096) (g : ℕ) :
    (Two.imgMask (unpackA g) (Two.maskOf W) == Two.maskOf W) =
      Nat.beq (maskOf 0 (W.map (mvNR (unpackQ g)))) (maskOf 0 W) := by
  rw [maskOf_eq, imgMask_maskOf _ W hW, appN_fA, nat_beq]

theorem orb_sound (O : List (List ℕ)) (hO : Two.w1Orbit () = O.map (maskOf 0))
    (hP : ∀ s ∈ O, PC s) (h : orbAtM O (O.map (maskOf 0)) = true) : Two.orbitOK45 () = true := by
  rw [orbAtM, orbAtS] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [Two.orbitOK45, hO]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by rw [nat_beq]; exact h1, (nodupP_iff _).1 h2⟩, ?_⟩
  rw [List.all_eq_true]
  intro m hm
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.1 hm
  have h3' := List.all_eq_true.1 h3 cs hcs
  rw [← nGensL_eq, List.all_map] at h3'
  rw [nGensI_eq, List.all_map, List.all_eq_true]
  intro X hX
  have := List.all_eq_true.1 h3' X hX
  simp only [Function.comp_apply] at this ⊢
  rw [memP_ofListP] at this
  rw [imgMask_maskOf _ cs (hP cs hcs), appN_fA]
  exact this

theorem orbitOK45_of (h : ok45Orb = true) : Two.orbitOK45 () = true :=
  orb_sound orbW w1Orbit_eq.1 w1Orbit_eq.2 h

theorem pOK_gen (gs S W : List ℕ) (om : ℕ) (hgs : ∀ g ∈ gs, g < 2 ^ 144) (hom : om < 2 ^ 144)
    (hW : ∀ c ∈ W, c < 4096) (hst : memAll (ofListP (enumQ S)) gs = true)
    (h : pAt gs om W (enumQ gs) (maskOf 0 W) = true) :
    (Two.gensOKb (gs.map unpackA) &&
      (gs.map unpackA).all (fun p => (Std.HashSet.ofList (enumGrp (S.map unpackA))).contains p) &&
      (enumGrp (gs.map unpackA)).contains idR &&
      closedCheck (gs.map unpackA) (enumGrp (gs.map unpackA)) &&
      (enumGrp (gs.map unpackA)).dedup.length == 256 &&
      (List.range 4096).all (fun n => ((gs.map unpackA).all fun g => appN g n == n) ==
        (n == 0 || n == 3)) &&
      (gs.map unpackA).all (fun g => Two.zList.all fun n => Two.zList.contains (appN g n)) &&
      (gs.map unpackA).all (fun g => Two.imgMask g (Two.maskOf W) == Two.maskOf W) &&
      Two.imgMask (unpackA om) (Two.maskOf W) == Two.maskOf W) = true := by
  rw [pAt] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hg, hf⟩, hz⟩, hm⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := grpAt_sound gs 256 hg
  rw [List.all_cons] at hm
  rw [Bool.and_eq_true] at hm
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨g1, memAll_of S gs hgs hst⟩, g2⟩, g3⟩, g4⟩, fix_sound gs hf⟩, z_sound gs hz⟩, ?_⟩, ?_⟩
  · rw [all_map_congr (p := fun g => Two.imgMask g (Two.maskOf W) == Two.maskOf W)
      (q := fun g => Nat.beq (maskOf 0 (W.map (mvNR (unpackQ g)))) (maskOf 0 W))
      fun g _ => img_sound W hW g]
    exact hm.2
  · rw [img_sound W hW om]
    exact hm.1

theorem pOK45_of (hs1 : stab1OK = true) (hst : ok45Stab = true) (hp : ok45P = true) :
    Two.pOK45 () = true := by
  rw [Two.pOK45, pRows_eq, stab1Gens_eq hs1, omegaRows_eq, Two.w1Mask, w1List_eq]
  exact pOK_gen pQ stab1Q w1L omegaQ pQ_lt omegaQ_lt w1L_lt hst hp

theorem ok45_of (hs1 : stab1OK = true) (ho : ok45Orb = true) (hst : ok45Stab = true)
    (hp : ok45P = true) : Two.ok45 () = true := by
  rw [Two.ok45, orbitOK45_of ho, pOK45_of hs1 hst hp, Bool.and_true]

theorem grp44_gen (gs ps S : List ℕ) (hgs : ∀ g ∈ gs, g < 2 ^ 144) (hps : ∀ g ∈ ps, g < 2 ^ 144)
    (hst : memAll (ofListP (enumQ S)) gs = true)
    (h : grp44At gs ps S (enumQ gs) (enumQ ps) = true) :
    (let X := enumGrp (gs.map unpackA)
     let Xs := Std.HashSet.ofList X
     let P := enumGrp (ps.map unpackA)
     let St := Std.HashSet.ofList (enumGrp (S.map unpackA))
     Two.gensOKb (gs.map unpackA) && Two.gensOKb (ps.map unpackA) &&
      (gs.map unpackA).all (fun g => St.contains g && appN g 192 == 192) &&
      appN ((S.map unpackA).getD 4 idR) 192 != 192 &&
      X.contains idR && closedCheck (gs.map unpackA) X && X.dedup.length == 1920 &&
      P.contains idR && closedCheck (ps.map unpackA) P && P.dedup.length == 16 &&
      (ps.map unpackA).all (fun p => Xs.contains p) &&
      P.all (fun x => P.all fun y => mulR x y == mulR y x) && P.all (fun x => mulR x x == idR)) =
      true := by
  obtain ⟨hP, hPv⟩ := enumGrp_A ps
  rw [grp44At] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hX, hPg⟩, h192⟩, hmv⟩, hmem⟩, hcomm⟩, hinv⟩ := h
  obtain ⟨x1, x2, x3, x4⟩ := grpAt_sound gs 1920 hX
  obtain ⟨p1, p2, p3, p4⟩ := grpAt_sound ps 16 hPg
  have hs := memAll_of S gs hgs hst
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨x1, p1⟩, ?_⟩, ?_⟩, x2⟩, x3⟩, x4⟩, p2⟩, p3⟩, p4⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at hs h192 ⊢
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    rw [Bool.and_eq_true, appN_A, nat_beq]
    exact ⟨hs _ hg, h192 g' hg'⟩
  · rw [idR_A, List.getD_map, appN_A, bne, nat_beq]
    exact hmv
  · rw [memAll] at hmem
    rw [all_map_congr fun p hp => setContains_A gs (hps p hp)]
    exact hmem
  · rw [hP, all_map_congr fun x hx => ?_]
    · exact hcomm
    · rw [all_map_congr fun y hy => by rw [mulR_A, mulR_A, beq_unpackA (mulQ_lt _ _) (mulQ_lt _ _),
        nat_beq]]
  · rw [hP, all_map_congr fun x _ => by rw [mulR_A, idR_A, beq_unpackA (mulQ_lt _ _) oneQ_lt,
      nat_beq]]
    exact hinv

theorem all_codesOf (cs : List ℕ) (hcs : PC cs) (p : ℕ → Bool) :
    (Two.codesOf (maskOf 0 cs)).all p = cs.all p := by
  have hmem : ∀ c, c ∈ Two.codesOf (maskOf 0 cs) ↔ c ∈ cs := by
    intro c
    rw [Two.codesOf, List.mem_filter, List.mem_range, testBit_maskOf0, List.contains_iff_mem]
    exact ⟨fun h => h.2, fun h => ⟨hcs c h, h⟩⟩
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h c hc => h c ((hmem c).2 hc), fun h c hc => h c ((hmem c).1 hc)⟩

theorem maps_sound (cs : List ℕ) (hcs : PC cs) (x : ℕ) :
    Two.mapsInto (unpackA x) (maskOf 0 cs) (Two.codesOf (maskOf 0 cs)) =
      mapsQ (unpackQ x) (maskOf 0 cs) cs := by
  rw [Two.mapsInto, all_codesOf cs hcs, mapsQ]
  refine congrArg cs.all (funext fun c => ?_)
  rw [appN_A, bitQ_eq]

theorem w5_gen (O : List (List ℕ)) (hO : Two.w1Orbit () = O.map (maskOf 0))
    (hPO : ∀ s ∈ O, PC s) (gs ps : List ℕ) (hgs : ∀ g ∈ gs, g < 2 ^ 144)
    (hps : ∀ g ∈ ps, g < 2 ^ 144)
    (h : w5At ps ((O.filter inW5).map fun cs => (cs, maskOf 0 cs)) (enumQ gs) (ofListP (enumQ ps)) =
      true) :
    (let X := enumGrp (gs.map unpackA)
     let Ps := Std.HashSet.ofList (enumGrp (ps.map unpackA))
     let WC := (Two.w5 ()).map fun m => (m, Two.codesOf m)
     (Two.w5 ()).length == 5 &&
      (ps.map unpackA).all (fun p => WC.all fun mc => Two.mapsInto p mc.1 mc.2) &&
      X.all (fun x => !(WC.all fun mc => Two.mapsInto x mc.1 mc.2) || Ps.contains x)) = true := by
  have hW5 : Two.w5 () = (O.filter inW5).map (maskOf 0) := by
    rw [Two.w5, hO, List.filter_map]
    congr 1
    refine List.filter_congr fun cs _ => ?_
    rw [Function.comp_apply, inW5, bitQ_eq, bitQ_eq, bitQ_eq]
  have hPF : ∀ s ∈ O.filter inW5, PC s := fun s hs => hPO s (List.mem_filter.1 hs).1
  have hall : ∀ y : ℕ, ((Two.w5 ()).map fun m => (m, Two.codesOf m)).all
      (fun mc => Two.mapsInto (unpackA y) mc.1 mc.2) =
        ((O.filter inW5).map fun cs => (cs, maskOf 0 cs)).all
          (fun mc => mapsQ (unpackQ y) mc.2 mc.1) := by
    intro y
    rw [hW5, List.map_map, List.all_map, List.all_map]
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro H cs hcs
      have := H cs hcs
      simp only [Function.comp_apply] at this ⊢
      rwa [maps_sound cs (hPF cs hcs)] at this
    · intro H cs hcs
      have := H cs hcs
      simp only [Function.comp_apply] at this ⊢
      rwa [maps_sound cs (hPF cs hcs)]
  rw [w5At] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hW5, List.length_map, nat_beq]
    rw [List.length_map] at h1
    exact h1
  · rw [all_map_congr fun p _ => hall p]
    exact h2
  · rw [(enumGrp_A gs).1, all_map_congr fun x hx => by
      rw [hall x, setContains_A ps ((enumGrp_A gs).2 x hx)]]
    exact h3

theorem perp_gen (ps : List ℕ) (h : ((enumQ ps).all fun x =>
      !([4, 24].all fun c => Nat.beq (mvNR (unpackQ x) c) c) || Nat.beq x oneQ) = true) :
    (enumGrp (ps.map unpackA)).all (fun x => !(Two.perpWit.all fun c => appN x c == c) || x == idR) =
      true := by
  obtain ⟨hE, hEv⟩ := enumGrp_A ps
  rw [hE, all_map_congr fun x hx => by
    rw [idR_A, beq_unpackA (hEv x hx) oneQ_lt, appN_fA, nat_beq]]
  exact h

theorem ok44_of (hs1 : stab1OK = true) (hst : ok44Stab = true) (hg : ok44Grp = true)
    (hw : ok44W5 = true) (hp : ok44Perp = true) : Two.ok44 () = true := by
  have e1 : Two.zGrpOK44 () = true := by
    rw [Two.zGrpOK44, gZRows_eq, p2Rows_eq, stab1Gens_eq hs1]
    exact grp44_gen gZQ p2Q stab1Q gZQ_lt p2Q_lt hst hg
  have e2 : Two.zW5OK44 () = true := by
    rw [Two.zW5OK44, gZRows_eq, p2Rows_eq]
    exact w5_gen orbW w1Orbit_eq.1 w1Orbit_eq.2 gZQ p2Q gZQ_lt p2Q_lt hw
  have e3 : Two.zPerpOK44 () = true := by
    rw [Two.zPerpOK44, p2Rows_eq]
    exact perp_gen p2Q hp
  rw [Two.ok44, e1, e2, e3]
  rfl

end Certificates.Kernel.AS91K45
