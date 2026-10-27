module

public import Certificates.Data.Kernel.AS91Split
public import CFSG.Certificates.Kernel.HJ12KTSound

public section

namespace Certificates.Kernel.AS91Split

open Certificates.Kernel.HJ12K CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.Quasithin.H13.AS91.Two
  CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA CFSG.GF2Type.Smith1979.IdxFour

theorem enumGrp_native : @Enum.enumGrp = @CFSG.GammaU.Native.enumGrp := by
  funext gs
  simp only [Enum.enumGrp, CFSG.GammaU.Native.enumGrp, native_bfsClosure, native_mulR, native_idR]

theorem closedCheck_native : @Enum.closedCheck = @CFSG.GammaU.Native.closedCheck := by
  funext gs X
  simp only [Enum.closedCheck, CFSG.GammaU.Native.closedCheck, native_mulR]

theorem invR_native : @Viol.invR = @CFSG.GammaU.Native.invR := by
  funext r
  simp only [Viol.invR, CFSG.GammaU.Native.invR, native_appN]

theorem idR_unpackA : idR = unpackA oneQ := by rw [← native_idR]; exact idR_eq

theorem mulR_unpack (X Y : ℕ) : mulR (unpackA X) (unpackA Y) = unpackA (mulQ X Y) := by
  rw [← native_mulR]; exact mulR_unpackA X Y

theorem appN_unpack (X n : ℕ) : appN (unpackA X) n = mvNR (unpackQ X) n := by
  rw [← native_appN]; exact appN_unpackA X n

theorem okRows_unpack (X : ℕ) : Viol.okRows (unpackA X) = true := by
  rw [Viol.okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨rfl, fun i hi => decide_eq_true ?_⟩
  exact unpackQ_lt4096 X _ (List.getElem_mem (by simpa [unpackA] using hi))

theorem gensOKb_of (gs : List ℕ) (h : gensOKQ gs = true) : gensOKb (gs.map unpackA) = true := by
  rw [gensOKQ, List.all_eq_true] at h
  rw [gensOKb, List.all_eq_true]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
  have hi := h g hg
  rw [invR_native, invR_unpackA hi, okRows_unpack, okRows_unpack, mulR_unpack, mulR_unpack,
    idR_unpackA, beq_unpackA (mulQ_lt _ _) oneQ_lt, beq_unpackA (mulQ_lt _ _) oneQ_lt]
  rw [invOKQ, Bool.and_eq_true] at hi
  rw [nat_beq, nat_beq, hi.1, hi.2]
  rfl

theorem enumGrp_unpack (gs : List ℕ) :
    Enum.enumGrp (gs.map unpackA) = (enumQ gs).map unpackA ∧ ∀ q ∈ enumQ gs, q < 2 ^ 144 := by
  rw [enumGrp_native]; exact enumGrp_eq gs

theorem closedCheck_unpack (gs X : List ℕ) (hX : ∀ q ∈ X, q < 2 ^ 144) :
    Enum.closedCheck (gs.map unpackA) (X.map unpackA) = closedQ gs X := by
  rw [closedCheck_native]; exact closedCheck_eq gs X hX

theorem contains_ofList_map {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 144) {y : ℕ} (hy : y < 2 ^ 144) :
    (Std.HashSet.ofList (L.map unpackA)).contains (unpackA y) = L.contains y := by
  rw [Std.HashSet.contains_ofList, contains_map hL hy]

theorem getElem!_map : ∀ {L : List ℕ} {i : ℕ}, i < L.length →
    (L.map unpackA)[i]! = unpackA (L.getD i oneQ)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: L, 0, _ => by rw [List.map_cons, List.getElem!_cons_zero]; rfl
  | a :: L, i + 1, h => by
    rw [List.map_cons, List.getElem!_cons_succ, getElem!_map (by simpa using h)]
    rfl

theorem wordRows_eq (L : List ℕ) : ∀ (w : List ℕ), (∀ i ∈ w, i < L.length) →
    wordRows (L.map unpackA) w = unpackA (wordP L w)
  | [], _ => by rw [wordRows, wordP, List.map_nil, List.foldr_nil, List.map_nil, List.foldr_nil,
      idR_unpackA]
  | i :: w, h => by
    have ih := wordRows_eq L w fun j hj => h j (List.mem_cons_of_mem i hj)
    rw [wordRows, wordP, List.map_cons, List.foldr_cons, List.map_cons, List.foldr_cons]
    rw [wordRows, wordP] at ih
    rw [ih, getElem!_map (h i List.mem_cons_self), mulR_unpack]

theorem all_lt_of {w : List ℕ} {n : ℕ} (h : w.all (· < n) = true) : ∀ i ∈ w, i < n :=
  fun i hi => of_decide_eq_true (List.all_eq_true.1 h i hi)

theorem aRows48_eq : aRows48 = unpackA aQ := by decide

theorem bRows48_eq : bRows48 = unpackA bQ := by decide

theorem cRows48_eq : cRows48 = unpackA cQ := by decide

theorem omegaRows_eq : omegaRows = unpackA omQ := by decide

theorem sGens48_eq : sGens48 = sGQ.map unpackA := by decide

theorem pRows_eq : pRows = pQ.map unpackA := by decide

theorem ebRows_eq : ebRows = ebQ.map unpackA := by decide

theorem gamGensI_eq : gamGensI = gamIQ.map unpackA := by decide

theorem nGensI_eq : nGensI = nIQ.map unpackA := by decide

theorem sGQ_lt : ∀ q ∈ sGQ, q < 2 ^ 144 := by decide

theorem aQ_lt : aQ < 2 ^ 144 := by decide

theorem bQ_lt : bQ < 2 ^ 144 := by decide

theorem cQ_lt : cQ < 2 ^ 144 := by decide

theorem sOK48_of (h : sQ48 = true) : sOK48 () = true := by
  obtain ⟨EP, BP⟩ := enumGrp_unpack pQ
  obtain ⟨EE, BE⟩ := enumGrp_unpack ebQ
  obtain ⟨ES, BS⟩ := enumGrp_unpack sGQ
  rw [sQ48] at h
  generalize enumQ pQ = P at EP BP h
  generalize enumQ ebQ = Eb at EE BE h
  generalize enumQ sGQ = Sl at ES BS h
  simp only [sAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hg, hP⟩, h1⟩, hc⟩, hn, hl⟩, hx⟩ := h
  rw [sOK48, sGens48_eq, pRows_eq, ebRows_eq, EP, EE, ES]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨gensOKb_of _ hg, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨g, hg', rfl⟩ := List.mem_map.1 hx
    rw [contains_ofList_map BP (sGQ_lt g hg')]
    exact List.all_eq_true.1 hP g hg'
  · rw [idR_unpackA, contains_map BS oneQ_lt]
    exact h1
  · rw [closedCheck_unpack _ _ BS]
    exact hc
  · rw [dedup_length BS hn, nat_beq]
    exact hl
  · rw [List.all_eq_true]
    intro x hxm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hxm
    rw [idR_unpackA, beq_unpackA (BS y hy) oneQ_lt, nat_beq, contains_ofList_map BE (BS y hy)]
    exact List.all_eq_true.1 hx y hy

theorem nIQ_sWord : ∀ i ∈ sWord48, i < nIQ.length := by decide

theorem nIQ_sWordInv : ∀ i ∈ sWordInv48, i < nIQ.length := by decide

theorem sRows48_eq : sRows48 () = unpackA s48Q := by
  rw [sRows48, nGensI_eq, wordRows_eq nIQ sWord48 nIQ_sWord, s48Q]

theorem sInvRows48_eq : sInvRows48 () = unpackA si48Q := by
  rw [sInvRows48, nGensI_eq, wordRows_eq nIQ sWordInv48 nIQ_sWordInv, si48Q]

theorem coreL_lt {P : List ℕ} (BP : ∀ q ∈ P, q < 2 ^ 144) (s si : ℕ) :
    ∀ q ∈ coreL P s si, q < 2 ^ 144 := fun q hq => BP q (List.mem_of_mem_filter hq)

theorem coreList_eq {P : List ℕ} (EP : Enum.enumGrp (pQ.map unpackA) = P.map unpackA)
    (BP : ∀ q ∈ P, q < 2 ^ 144) : coreList48 () = (coreL P s48Q si48Q).map unpackA := by
  rw [coreList48, pRows_eq, EP, sRows48_eq, sInvRows48_eq]
  rw [List.filter_map, coreL]
  congr 1
  refine List.filter_congr fun r _ => ?_
  rw [Function.comp_apply, mulR_unpack, mulR_unpack, contains_ofList_map BP (mulQ_lt _ _)]

theorem coreOK48_of (h : coreQ48 = true) : coreOK48 () = true := by
  obtain ⟨EP, BP⟩ := enumGrp_unpack pQ
  rw [coreQ48] at h
  generalize enumQ pQ = P at EP BP h
  simp only [coreAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := h
  rw [coreOK48, coreList_eq EP BP, sRows48_eq, sInvRows48_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [mulR_unpack, idR_unpackA, beq_unpackA (mulQ_lt _ _) oneQ_lt, nat_beq]
    exact h3
  · rw [appN_unpack, nat_beq]
    exact h4
  · rw [dedup_length (coreL_lt BP _ _) h5, nat_beq]
    exact h6

theorem uOK48_of (h : uQ48 = true) : uOK48 () = true := by
  rw [uQ48] at h
  simp only [uAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rw [uOK48]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, h3⟩, h4⟩, ?_⟩, h6⟩, ?_⟩, ?_⟩, h9⟩
  · rw [List.dedup_eq_self.2 ((nodupP_iff _).1 h1), nat_beq]
    exact h2
  · simpa only [Std.HashSet.contains_ofList, contains_bitQ] using h5
  · simpa only [omegaRows_eq, appN_unpack, Std.HashSet.contains_ofList, contains_bitQ] using h7
  · simpa only [sGens48_eq, List.all_map, Function.comp_def, appN_unpack,
      Std.HashSet.contains_ofList, contains_bitQ] using h8

theorem conjOK_of (L : List ℕ) (d : List ℕ × List ℕ × Array ℕ) (hd : d.2.2 = unpackA (cjP d).2.2)
    (t : ℕ) (ht : t < 2 ^ 144) (h : conjP L (cjP d) t = true) :
    conjOK (L.map unpackA) d (unpackA t) = true := by
  simp only [conjP, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := wordRows_eq L d.1 (all_lt_of h1)
  have e2 := wordRows_eq L d.2.1 (all_lt_of h2)
  rw [conjOK, List.length_map]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
  · rw [e1, e2, mulR_unpack, idR_unpackA, beq_unpackA (mulQ_lt _ _) oneQ_lt, nat_beq]
    exact h3
  · rw [e1, e2, hd, mulR_unpack, mulR_unpack, beq_unpackA (mulQ_lt _ _) ht, nat_beq]
    exact h4

theorem cjA_eq : cjA48.2.2 = unpackA (cjP cjA48).2.2 := by decide

theorem cjB_eq : cjB48.2.2 = unpackA (cjP cjB48).2.2 := by decide

theorem cjAB_eq : cjAB48.2.2 = unpackA (cjP cjAB48).2.2 := by decide

theorem cjC_eq : cjC48.2.2 = unpackA (cjP cjC48).2.2 := by decide

theorem cjAC_eq : cjAC48.2.2 = unpackA (cjP cjAC48).2.2 := by decide

theorem cjBC_eq : cjBC48.2.2 = unpackA (cjP cjBC48).2.2 := by decide

theorem cj_lt : (cjP cjA48).2.2 < 2 ^ 144 ∧ (cjP cjB48).2.2 < 2 ^ 144 ∧
    (cjP cjAB48).2.2 < 2 ^ 144 ∧ (cjP cjC48).2.2 < 2 ^ 144 ∧ (cjP cjAC48).2.2 < 2 ^ 144 ∧
    (cjP cjBC48).2.2 < 2 ^ 144 := by decide

theorem cjOK48_of (h : cjQ48 = true) : cjOK48 () = true := by
  obtain ⟨EP, BP⟩ := enumGrp_unpack pQ
  obtain ⟨EE, BE⟩ := enumGrp_unpack ebQ
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := cj_lt
  rw [cjQ48] at h
  generalize enumQ pQ = P at EP BP h
  generalize enumQ ebQ = Eb at EE BE h
  have BC := coreL_lt BP s48Q si48Q
  simp only [cjAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hA⟩, hA'⟩, hB⟩, hB'⟩, hAB⟩, hAB'⟩, hC⟩, hC'⟩, hC''⟩, hAC⟩, hAC'⟩,
    hAC''⟩, hBC⟩, hBC'⟩, hBC''⟩, hT⟩ := h
  rw [cjOK48, ebRows_eq, EE, coreList_eq EP BP, aRows48_eq, bRows48_eq, cRows48_eq, omegaRows_eq,
    gamGensI_eq, nGensI_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, conjOK_of _ _ cjA_eq _ aQ_lt hA⟩, ?_⟩,
    conjOK_of _ _ cjB_eq _ bQ_lt hB⟩, ?_⟩, ?_⟩, ?_⟩, conjOK_of _ _ cjC_eq _ cQ_lt hC⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simpa only [List.all_map, Function.comp_def, mulR_unpack, beq_unpackA, mulQ_lt, nat_beq]
      using h0
  · rw [cjA_eq, contains_ofList_map BE l1]
    exact hA'
  · rw [cjB_eq, contains_ofList_map BE l2]
    exact hB'
  · rw [mulR_unpack, mulR_unpack]
    exact conjOK_of _ _ cjAB_eq _ (mulQ_lt _ _) hAB
  · rw [cjAB_eq, contains_ofList_map BE l3]
    exact hAB'
  · rw [cjC_eq, contains_ofList_map BC l4]
    exact hC'
  · rw [cjC_eq, idR_unpackA, bne, beq_unpackA l4 oneQ_lt, nat_beq]
    exact hC''
  · rw [mulR_unpack]
    exact conjOK_of _ _ cjAC_eq _ (mulQ_lt _ _) hAC
  · rw [cjAC_eq, contains_ofList_map BC l5]
    exact hAC'
  · rw [cjAC_eq, idR_unpackA, bne, beq_unpackA l5 oneQ_lt, nat_beq]
    exact hAC''
  · rw [mulR_unpack]
    exact conjOK_of _ _ cjBC_eq _ (mulQ_lt _ _) hBC
  · rw [cjBC_eq, contains_ofList_map BC l6]
    exact hBC'
  · rw [cjBC_eq, idR_unpackA, bne, beq_unpackA l6 oneQ_lt, nat_beq]
    exact hBC''
  · simpa only [List.all_cons, List.all_nil, mulR_unpack, idR_unpackA, beq_unpackA, mulQ_lt,
      oneQ_lt, nat_beq, Bool.and_true] using hT

theorem splitOK48_of (h1 : sQ48 = true) (h2 : coreQ48 = true) (h3 : uQ48 = true)
    (h4 : cjQ48 = true) : splitOK48 () = true := by
  rw [splitOK48, sOK48_of h1, coreOK48_of h2, uOK48_of h3, cjOK48_of h4]
  rfl

end Certificates.Kernel.AS91Split
