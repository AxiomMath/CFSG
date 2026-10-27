module

public import CFSG.Certificates.Kernel.AS91K468.Bfs
public import CFSG.Quasithin.H13.L32NMatN
public import CFSG.Certificates.Kernel.AS91K468.Common

public section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
  CFSG.GF2Type.Smith1979.GammaU.Enum

theorem nGensI_eq : CFSG.Quasithin.H13.AS91.Two.nGensI = nQ.map unpackA := by decide +kernel

theorem omegaRows_eq : CFSG.GF2Type.Smith1979.IdxFour.omegaRows = unpackA omQ := by decide +kernel

theorem wordRowsS (gs : List ℕ) : ∀ w : List ℕ, (∀ i ∈ w, i < gs.length) →
    CFSG.GF2Type.Smith1979.IdxFour.wordRows (gs.map unpackA) w = unpackA (wordQS gs w)
  | [], _ => idRS
  | i :: w, h => by
    have hi : i < gs.length := h i List.mem_cons_self
    have ih := wordRowsS gs w fun j hj => h j (List.mem_cons_of_mem i hj)
    rw [CFSG.GF2Type.Smith1979.IdxFour.wordRows, wordQS] at ih ⊢
    have hg : (gs.map unpackA)[i]! = unpackA (gs.getD i oneQ) := by
      rw [getElem!_pos (gs.map unpackA) i (by simpa using hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi]
    rw [List.map_cons, List.foldr_cons, List.map_cons, List.foldr_cons, hg, ih, mulRS]

theorem words_eqS (ws : List (List ℕ)) (hw : ∀ w ∈ ws, ∀ i ∈ w, i < nQ.length) (L : List ℕ)
    (h : ws.map (wordQS nQ) = L) :
    ws.map (CFSG.GF2Type.Smith1979.IdxFour.wordRows CFSG.Quasithin.H13.AS91.Two.nGensI) =
      L.map unpackA := by
  rw [← h, List.map_map, nGensI_eq]
  exact List.map_congr_left fun w hw' => wordRowsS nQ w (hw w hw')

theorem stab1Gens_eq (h : wordsOK46 = true) :
    CFSG.Quasithin.H13.AS91.Two.stab1Gens () = st1Q.map unpackA := by
  rw [wordsOK46, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact words_eqS _ (by decide +kernel) _ h.1

theorem g13Gens_eq (h : wordsOK46 = true) :
    CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA := by
  rw [wordsOK46, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact words_eqS _ (by decide +kernel) _ h.2

theorem maskOfT (L : List ℕ) : CFSG.Quasithin.H13.AS91.Two.maskOf L = maskOf 0 L := rfl

theorem w1Mask_eq : CFSG.Quasithin.H13.AS91.Two.w1Mask () = w1M := rfl

theorem span_fix (A : List ℕ) : ∀ B : List ℕ, (∀ b ∈ B, CFSG.Quasithin.H13.MatNCert.mvN A b = b) →
    ∀ c ∈ spanL B, CFSG.Quasithin.H13.MatNCert.mvN A c = c
  | [], _, c, hc => by
    rw [spanL, List.mem_singleton] at hc
    rw [hc, CFSG.Quasithin.H13.MatNCert.mvN_zero]
  | b :: B, hB, c, hc => by
    have ih := span_fix A B fun b' hb' => hB b' (List.mem_cons_of_mem b hb')
    rw [spanL, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ih c hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      rw [CFSG.Quasithin.H13.MatNCert.mvN_xor, hB b List.mem_cons_self, ih d hd]

theorem w1_span : ∀ c ∈ CFSG.Quasithin.H13.AS91.Two.w1List, c ∈ spanL w1B := by decide +kernel

theorem w1B_sub : ∀ b ∈ w1B, b ∈ CFSG.Quasithin.H13.AS91.Two.w1List := by decide +kernel

theorem fixW1_eq (x : ℕ) :
    (CFSG.Quasithin.H13.AS91.Two.w1List.all fun c => appN (unpackA x) c == c) = fixW1 x := by
  rw [fixW1, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  have e : ∀ c, (appN (unpackA x) c == c) = Nat.beq (mvNR (unpackQ x) c) c := fun c => by
    rw [appNS, nat_beq]
  simp only [e, Nat.beq_eq, mvNR_eq]
  exact ⟨fun H b hb => H b (w1B_sub b hb),
    fun H c hc => span_fix (unpackQ x) w1B H c (w1_span c hc)⟩

theorem imgMask_eq (g m : ℕ) : CFSG.Quasithin.H13.AS91.Two.imgMask (unpackA g) m = imgQ g m := by
  simp only [CFSG.Quasithin.H13.AS91.Two.imgMask, imgQ, appNS]

theorem fixMaskS (X : ℕ) :
    CFSG.Quasithin.H13.AS91.Two.fixMask (unpackA X) = fixMask (unpackQ X) := by
  apply Nat.eq_of_testBit_eq
  intro v
  rw [CFSG.Quasithin.H13.AS91.Two.fixMask, maskOfT, maskOf_testBit, Nat.zero_testBit,
    Bool.false_or]
  by_cases hv : v < 4096
  · rw [fixMask_testBit X hv, Bool.eq_iff_iff, List.contains_iff_mem, List.mem_filter,
      List.mem_range, appNS, nat_beq]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  · have h1 : (fixMask (unpackQ X)).testBit v = false := by
      rw [fixMask, foldl_and_testBit, fullM, Nat.testBit_two_pow_sub_one, decide_eq_false hv,
        Bool.false_and]
    rw [h1, Bool.eq_false_iff]
    intro h
    exact hv (List.mem_range.1 (List.mem_filter.1 (List.contains_iff_mem.1 h)).1)

theorem fullMask_eq : CFSG.Quasithin.H13.AS91.Two.fullMask () = fullM := by
  apply Nat.eq_of_testBit_eq
  intro v
  rw [CFSG.Quasithin.H13.AS91.Two.fullMask, maskOfT, maskOf_testBit, Nat.zero_testBit,
    Bool.false_or, fullM, Nat.testBit_two_pow_sub_one, Bool.eq_iff_iff, List.contains_iff_mem,
    List.mem_range, decide_eq_true_iff]

theorem w1OK46_eq : CFSG.Quasithin.H13.AS91.Two.w1OK46 () = w1OK46Q := by
  simp only [CFSG.Quasithin.H13.AS91.Two.w1OK46, w1OK46Q, w1_contains]

theorem eb_sound (St P Eb : List ℕ) (ES : enumGrp (st1Q.map unpackA) = St.map unpackA)
    (EP : enumGrp (pQ.map unpackA) = P.map unpackA)
    (EE : enumGrp (ebQ.map unpackA) = Eb.map unpackA) (BS : ∀ q ∈ St, q < 2 ^ 144)
    (BP : ∀ q ∈ P, q < 2 ^ 144) (BE : ∀ q ∈ Eb, q < 2 ^ 144)
    (hst : CFSG.Quasithin.H13.AS91.Two.stab1Gens () = st1Q.map unpackA)
    (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (h : ebAt St P Eb = true) : CFSG.Quasithin.H13.AS91.Two.ebOK46 () = true := by
  simp only [ebAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  simp only [CFSG.Quasithin.H13.AS91.Two.ebOK46, Bool.and_eq_true]
  rw [hst, hg, pRows_eq, ebRows_eq, ES, EP, EE, omegaRows_eq,
    w1Mask_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨gensS ebQ h1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, dedupS BE 16 h7 h8⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩
  · exact (all_map_congr fun x _ => fixW1_eq x).trans h2
  · exact (all_map_congr fun x hx => ofListS BP (ebQ_lt x hx)).trans h3
  · refine (all_map_congr fun x _ => ?_).trans h4
    rw [mulRS, mulRS, beqS (mulQ_lt' _ _) (mulQ_lt' _ _)]
  · rw [idRS, containsS BE oneQ_lt]
    exact h5
  · rw [closedS _ _ BE]
    exact h6
  · refine (all_map_congr fun x hx => ?_).trans h9
    rw [fixW1_eq x, ofListS BE (BS x hx)]
  · refine (all_map_congr fun g _ => ?_).trans h10
    rw [imgMask_eq, nat_beq]
  · refine (all_map_congr fun x _ => all_map_congr fun y _ => ?_).trans h11
    rw [mulRS, mulRS, beqS (mulQ_lt' _ _) (mulQ_lt' _ _)]
  · refine (all_map_congr fun x _ => ?_).trans h12
    rw [mulRS, idRS, beqS (mulQ_lt' _ _) oneQ_lt]

theorem invRS {g r : ℕ} (h : invOKQ g r = true) : Viol.invR (unpackA g) = unpackA r :=
  invR_unpackA h

theorem hk_unpackA (a b : ℕ) (ha : a < 2 ^ 144) (hb : b < 2 ^ 144) :
    ((fun x : Array ℕ => x) (unpackA a) == (fun x : Array ℕ => x) (unpackA b)) = (a == b) :=
  beq_unpackA ha hb

theorem ebOrbit_eq (hgens : gensOKQ g13Q = true)
    (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA) :
    CFSG.Quasithin.H13.AS91.Two.ebOrbit () = orbQ.map unpackA ∧ ∀ q ∈ orbQ, q < 2 ^ 144 := by
  have hinv : ∀ g ∈ g13Q, invOKQ g (invQ g) = true := List.all_eq_true.1 hgens
  have hf : ∀ q, q < 2 ^ 144 →
      (((g13Q.map unpackA).map fun g => let gi := Viol.invR g; fun x => mulR g (mulR x gi)).map
        fun f => f (unpackA q)) = (conjFs.map fun f => f q).map unpackA := by
    intro q _
    rw [conjFs, List.map_map, List.map_map, List.map_map, List.map_map]
    refine List.map_congr_left fun g hg' => ?_
    simp only [Function.comp_apply]
    rw [invRS (hinv g hg'), mulRS, mulRS]
  have hd : ∀ q, q < 2 ^ 144 → ∀ f ∈ conjFs, f q < 2 ^ 144 := by
    intro q _ f hf'
    rw [conjFs] at hf'
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hf'
    exact mulQ_lt' _ _
  have he : CFSG.Quasithin.H13.AS91.Two.ebRows.headD idR = unpackA (ebQ.headD oneQ) := by
    rw [ebRows_eq, idRS]
    rfl
  have hs : SRel unpackA (fun x : Array ℕ => x) (· < 2 ^ 144)
      ((∅ : Std.HashSet (Array ℕ)).insert (unpackA (ebQ.headD oneQ)))
      (insP (.tip []) (ebQ.headD oneQ)) := by
    intro q hq
    rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty,
      hk_unpackA _ _ (by decide +kernel) hq]
  have := bfsClosure_N unpackA (fun x : Array ℕ => x) (· < 2 ^ 144) hk_unpackA _ conjFs hf hd 100
    [ebQ.headD oneQ] [] _ _ (by decide +kernel) (by simp) hs
  rw [CFSG.Quasithin.H13.AS91.Two.ebOrbit, hg, he]
  exact this

theorem trans_sound (Eb : List ℕ) (EE : enumGrp (ebQ.map unpackA) = Eb.map unpackA)
    (BE : ∀ q ∈ Eb, q < 2 ^ 144)
    (hg : CFSG.Quasithin.H13.AS91.Two.g13Gens () = g13Q.map unpackA)
    (h : transAt Eb orbQ = true) : CFSG.Quasithin.H13.AS91.Two.transOK46 () = true := by
  rw [transAt, Bool.and_eq_true] at h
  have eo := ebOrbit_eq h.1 hg
  simp only [CFSG.Quasithin.H13.AS91.Two.transOK46, Bool.and_eq_true]
  rw [hg, eo.1, ebRows_eq, EE]
  refine ⟨gensS g13Q h.1, (all_map_congr fun x hx => ?_).trans h.2⟩
  rw [idRS, beqS (BE x hx) oneQ_lt, ofListS eo.2 (BE x hx)]

theorem mkey_beq (a b : ℕ) :
    (CFSG.Quasithin.H13.AS91.Two.mkey a == CFSG.Quasithin.H13.AS91.Two.mkey b) = (a == b) := by
  by_cases h : a = b
  · subst h
    simp
  · rw [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne]
    intro e
    exact h (Prod.mk.inj e).2

theorem contains_mkey (L : List ℕ) (y : ℕ) :
    (L.map CFSG.Quasithin.H13.AS91.Two.mkey).contains (CFSG.Quasithin.H13.AS91.Two.mkey y) =
      L.contains y := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.contains_cons, List.contains_cons, ih, mkey_beq]

theorem pList_eq (P : List ℕ) (EP : enumGrp (pQ.map unpackA) = P.map unpackA)
    (BP : ∀ q ∈ P, q < 2 ^ 144) (hn : nodupP P = true) :
    CFSG.Quasithin.H13.AS91.Two.pList () = P.map unpackA := by
  have hN : (P.map unpackA).Nodup :=
    List.Nodup.map_on (fun x hx y hy e => unpackA_inj (BP x hx) (BP y hy) e) ((nodupP_iff P).1 hn)
  rw [CFSG.Quasithin.H13.AS91.Two.pList, pRows_eq, EP, List.dedup_eq_self.2 hN]

theorem fixPairs_eq (P : List ℕ) (EP : enumGrp (pQ.map unpackA) = P.map unpackA)
    (BP : ∀ q ∈ P, q < 2 ^ 144) (hn : nodupP P = true) :
    CFSG.Quasithin.H13.AS91.Two.fixPairs () = (pfOf P).map fun p => (unpackA p.1, p.2) := by
  rw [CFSG.Quasithin.H13.AS91.Two.fixPairs, pList_eq P EP BP hn, pfOf, List.map_map, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, fixMaskS]

theorem popc_eq (F : ℕ) : CFSG.Quasithin.H13.AS91.Two.popc F = CFSG.KC.pc4096 F := bitsM_length F

theorem jF_eq (PF : List (ℕ × ℕ)) (BP : ∀ p ∈ PF, p.1 < 2 ^ 144) (m F : ℕ) :
    CFSG.Quasithin.H13.AS91.Two.jF (PF.map fun p => (unpackA p.1, p.2)) m F = jFQ PF m F := by
  have hC : (((PF.map fun p => (unpackA p.1, p.2)).filter fun rf => F &&& rf.2 == F).map
      Prod.fst) = ((PF.filter fun rf => F &&& rf.2 == F).map Prod.fst).map unpackA := by
    rw [List.filter_map, List.map_map, List.map_map]
    rfl
  have BC : ∀ a ∈ (PF.filter fun rf => F &&& rf.2 == F).map Prod.fst, a < 2 ^ 144 := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    exact BP p (List.mem_filter.1 hp).1
  have hA : ((((PF.filter fun rf => F &&& rf.2 == F).map Prod.fst).map unpackA).any fun a =>
      (((PF.filter fun rf => F &&& rf.2 == F).map Prod.fst).map unpackA).any fun b =>
        mulR a b != mulR b a) =
      ((PF.filter fun rf => F &&& rf.2 == F).map Prod.fst).any fun a =>
        ((PF.filter fun rf => F &&& rf.2 == F).map Prod.fst).any fun b =>
          !Nat.beq (mulQ a b) (mulQ b a) :=
    any_map_congr fun a _ => any_map_congr fun b _ => by
      rw [bne, mulRS, mulRS, beqS (mulQ_lt' _ _) (mulQ_lt' _ _)]
  simp only [CFSG.Quasithin.H13.AS91.Two.jF, jFQ]
  rw [hC, List.length_map, popc_eq, hA]

theorem pfOf_lt (P : List ℕ) (BP : ∀ q ∈ P, q < 2 ^ 144) : ∀ p ∈ pfOf P, p.1 < 2 ^ 144 := by
  intro p hp
  rw [pfOf] at hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
  exact BP x hx

theorem jAt_eq (PF : List (ℕ × ℕ)) (BP : ∀ p ∈ PF, p.1 < 2 ^ 144) (L : List ℕ) :
    ((L.all fun F => (PF.map fun p => (unpackA p.1, p.2)).all fun rf =>
        (Std.HashSet.ofList (L.map CFSG.Quasithin.H13.AS91.Two.mkey)).contains
          (CFSG.Quasithin.H13.AS91.Two.mkey (F &&& rf.2))) &&
      L.all (CFSG.Quasithin.H13.AS91.Two.jF (PF.map fun p => (unpackA p.1, p.2)) w1M)) =
      jAt PF L (ofListP L) := by
  rw [jAt]
  refine congrArg₂ (fun a b => a && b) (allc fun F _ => all_mapL fun rf _ => ?_)
    (allc fun F _ => jF_eq PF BP w1M F)
  rw [Std.HashSet.contains_ofList, contains_mkey, memP_ofListP]

end Certificates.Kernel.AS91K468
