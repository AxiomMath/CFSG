module

public import Certificates.Data.Kernel.CertF8.G9557
public import CFSG.Certificates.Kernel.CertF8.T3GSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28TCheck

public section

namespace CFSG.KC.CertF8.G9557

open CFSG.Quasithin CFSG.KC.G28 CFSG.KC.CertF8.T3G CFSG.RankThree.PartTwo.Sec4.Item434G28
  CFSG.AGLEmbedding.KFactProofs.G28

theorem natBeq (a b : ℕ) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  exact ⟨fun h => beq_true h, Nat.eq_of_beq_eq_true⟩

theorem sqL_eq (n : ℕ) : sqL n = 8 * (n / 8) + GF8.mulNat (n % 8) (n % 8) := by
  have h : ∀ t : Fin 8, [0, 1, 4, 5, 6, 7, 2, 3].getD t.val 0 = GF8.mulNat t.val t.val := by
    decide +kernel
  rw [sqL, h ⟨n % 8, Nat.mod_lt _ (by norm_num)⟩]

theorem frobCode_foldl (w : List ℕ) {A : Array ℕ} (hA : Valid A) :
    frobCode (w.foldl (fun A n => mulCode A (letterCode n)) A) =
      (w.map sqL).foldl (fun A n => mulCode A (letterCode n)) (frobCode A) := by
  induction w generalizing A with
  | nil => rfl
  | cons n w ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih (valid_mulCode hA (valid_letterCode n)),
      frobCode_mulCode hA (valid_letterCode n), frobCode_letterCode, sqL_eq]

theorem frobCode_wordCode (w : List ℕ) : frobCode (wordCode w) = wordCode (w.map sqL) := by
  rw [wordCode, wordCode, frobCode_foldl w valid_idCode, frobCode_idCode]

theorem frobM_pow (A : Matrix (Fin 6) (Fin 6) GF8) (n : ℕ) : frobM (A ^ n) = frobM A ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, frobM_one]
  | succ n ih => rw [pow_succ, pow_succ, frobM_mul, ih]

theorem frI_lt {m : ℕ} (hm : m < 243) : ∀ s, frI s m < 243
  | 0 => hm
  | _ + 1 => pcIdx_lt _ _ _

theorem pm_lt (x y : ℕ) : pm x y < 243 := pcIdx_lt _ _ _

theorem pw9_lt (x n : ℕ) : pw9 x n < 243 := pwG_lt 4 6 4 4 x n

theorem fr_lt (x : ℕ) : fr x < 243 := pcIdx_lt _ _ _

theorem aI_lt (t : ℕ) : aI t < 243 := pcIdx_lt _ _ _

theorem kOf_lt {x : ℕ} (hx : x < 243) : kOf x < 81 := by
  unfold kOf
  omega

theorem eq_of_codeP_eq {A B : Array ℕ} (hA : Valid A) (hB : Valid B) {x : ℕ} (hx : codeP A = x)
    (hy : codeP B = x) : A = B :=
  codeP_inj hA hB (by rw [hx, hy])

theorem list_getElem! (l : List (List ℕ)) (j : ℕ) : l[j]! = l.getD j [] := by
  induction l generalizing j with
  | nil => rfl
  | cons a l ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

structure Facts (U Z O : Array ℕ) : Prop where
  vU : Valid U
  vZ : Valid Z
  vO : Valid O
  R : RelsG 4 6 4 4 (decode U) (decode Z) (decode O)
  inj : ∀ i < 243, ∀ j < 243, (t3List U Z O)[i]! = (t3List U Z O)[j]! → i = j
  fU : frobCode U = powCode U 7
  fZ : frobCode Z = powCode Z 7
  fO : frobCode O = O

section Facts

variable {U Z O : Array ℕ} (F : Facts U Z O)
include F

theorem hV {t : ℕ} (ht : t < 243) : Valid (t3List U Z O)[t]! := valid_t3List F.vU F.vZ F.vO ht

theorem decL {t : ℕ} (ht : t < 243) :
    decode (t3List U Z O)[t]! = fT (decode U) (decode Z) (decode O) t :=
  decode_t3 F.vU F.vZ F.vO ht

theorem mulL {s t : ℕ} (hs : s < 243) (ht : t < 243) :
    mulCode (t3List U Z O)[s]! (t3List U Z O)[t]! = (t3List U Z O)[pm s t]! :=
  eq_of_decode_eq (valid_mulCode (hV F hs) (hV F ht)) (hV F (pm_lt _ _)) (by
    rw [decode_mulCode (hV F hs) (hV F ht), decL F hs, decL F ht, decL F (pm_lt _ _)]
    exact fTG_mul F.R s t)

theorem pwL {s : ℕ} (hs : s < 243) (n : ℕ) :
    powCode (t3List U Z O)[s]! n = (t3List U Z O)[pw9 s n]! :=
  eq_of_decode_eq (valid_powCode (hV F hs) n) (hV F (pw9_lt _ _)) (by
    rw [decode_powCode (hV F hs), decL F hs, decL F (pw9_lt _ _)]
    exact (fTG_pw F.R s n).symm)

theorem zeroL : (t3List U Z O)[0]! = idCode := t3_zero F.vU F.vZ F.vO

theorem beqL {i j : ℕ} (hi : i < 243) (hj : j < 243) :
    ((t3List U Z O)[i]! == (t3List U Z O)[j]!) = Nat.beq i j := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  exact ⟨fun h => beq_true (F.inj i hi j hj h), fun h => by rw [Nat.eq_of_beq_eq_true h]⟩

theorem idL {i : ℕ} (hi : i < 243) : ((t3List U Z O)[i]! == idCode) = Nat.beq i 0 := by
  rw [← zeroL F, beqL F hi (by norm_num)]

theorem memL {k : ℕ} (hk : k < 243) : (t3List U Z O).contains (t3List U Z O)[k]! = true := by
  rw [Array.contains_iff_mem, getElem!_pos (t3List U Z O) k (by rw [size_t3List]; exact hk)]
  exact Array.getElem_mem _

theorem frobL {t : ℕ} (ht : t < 243) : frobCode (t3List U Z O)[t]! = (t3List U Z O)[fr t]! := by
  have hft : fr t < 243 := pcIdx_lt _ _ _
  apply eq_of_decode_eq (valid_frobCode (hV F ht)) (hV F hft)
  have eU : frobM (decode U) = decode U ^ 7 := by
    rw [← decode_frobCode F.vU, F.fU, decode_powCode F.vU]
  have eZ : frobM (decode Z) = decode Z ^ 7 := by
    rw [← decode_frobCode F.vZ, F.fZ, decode_powCode F.vZ]
  have eO : frobM (decode O) = decode O := by
    rw [← decode_frobCode F.vO, F.fO]
  rw [decode_frobCode (hV F ht), decL F ht, decL F hft, fr, fT_pcIdxG F.R, fT, frobM_mul,
    frobM_mul, frobM_pow, frobM_pow, frobM_pow, eU, eZ, eO, ← pow_mul, ← pow_mul]

theorem frobkL {m : ℕ} (hm : m < 243) :
    ∀ s, frobk s (t3List U Z O)[m]! = (t3List U Z O)[frI s m]!
  | 0 => rfl
  | s + 1 => by
    rw [frobk, frobkL hm s, frobL F (frI_lt hm s)]
    rfl

theorem semiL {n m : ℕ} (hn : n < 243) (hm : m < 243) (s t : ℕ) :
    semi ((t3List U Z O)[n]!, s) ((t3List U Z O)[m]!, t) =
      ((t3List U Z O)[pm n (frI s m)]!, (s + t) % 3) := by
  rw [semi, frobkL F hm, mulL F hn (frI_lt hm s)]

theorem pairBeqL {a b : ℕ} (ha : a < 243) (hb : b < 243) (k l : ℕ) :
    (((t3List U Z O)[a]!, k) == ((t3List U Z O)[b]!, l)) = (Nat.beq a b && Nat.beq k l) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, Prod.mk.injEq]
  exact ⟨fun h => ⟨beq_true (F.inj a ha b hb h.1), beq_true h.2⟩,
    fun h => ⟨by rw [Nat.eq_of_beq_eq_true h.1], Nat.eq_of_beq_eq_true h.2⟩⟩

theorem scL {n m : ℕ} (hn : n < 243) (hm : m < 243) (s t : ℕ) :
    semiComm ((t3List U Z O)[n]!, s) ((t3List U Z O)[m]!, t) = sc n s m t := by
  rw [semiComm, semiL F hn hm, semiL F hm hn, pairBeqL F (pm_lt _ _)
    (pm_lt _ _), Nat.add_comm s t, beq_true rfl, Bool.and_true]
  rfl

theorem eU27 : U = (t3List U Z O)[27]! :=
  eq_of_decode_eq F.vU (hV F (by norm_num)) (by rw [decL F (by norm_num), fT]; norm_num)

theorem eZ3 : Z = (t3List U Z O)[3]! :=
  eq_of_decode_eq F.vZ (hV F (by norm_num)) (by rw [decL F (by norm_num), fT]; norm_num)

theorem eO1 : O = (t3List U Z O)[1]! :=
  eq_of_decode_eq F.vO (hV F (by norm_num)) (by rw [decL F (by norm_num), fT]; norm_num)

theorem ezc : powCode U 3 = (t3List U Z O)[81]! := by
  conv_lhs => rw [eU27 F]
  rw [pwL F (by norm_num)]
  rfl

theorem ez9 : powCode Z 3 = (t3List U Z O)[9]! := by
  conv_lhs => rw [eZ3 F]
  rw [pwL F (by norm_num)]
  rfl

theorem ezz : mulCode (powCode U 3) (powCode U 3) = (t3List U Z O)[162]! := by
  rw [ezc F, mulL F (by norm_num) (by norm_num)]
  rfl

theorem gensL : [(U, 0), (Z, 0), (O, 0), (idCode, 1)] =
    gensI.map fun g => ((t3List U Z O)[g.1]!, g.2) := by
  rw [gensI]
  simp only [List.map_cons, List.map_nil]
  rw [← eU27 F, ← eZ3 F, ← eO1 F, zeroL F]

theorem allGensL {n : ℕ} (hn : n < 243) (s : ℕ) :
    ((gensI.map fun g => ((t3List U Z O)[g.1]!, g.2)).all fun g =>
      semiComm ((t3List U Z O)[n]!, s) g) = gensI.all fun g => sc n s g.1 g.2 := by
  simp only [gensI, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
  rw [scL F hn (by norm_num), scL F hn (by norm_num), scL F hn (by norm_num),
    scL F hn (by norm_num)]

theorem aL {t : ℕ} (ht : t < 81) : (aList U Z)[t]! = (t3List U Z O)[aI t]! := by
  have hlt : aI t < 243 := pcIdx_lt _ _ _
  rw [aList, getElem!_ofFn_nat' _ ht]
  apply eq_of_decode_eq (valid_mulCode (valid_powCode F.vU _) (valid_powCode F.vZ _)) (hV F hlt)
  rw [decode_mulCode (valid_powCode F.vU _) (valid_powCode F.vZ _), decode_powCode F.vU,
    decode_powCode F.vZ, decL F hlt, aI, fT_pcIdxG F.R, pow_zero, mul_one]

theorem size_aList : (aList U Z).size = 81 := by simp [aList]

theorem memA {k : ℕ} (hk : k < 81) : (aList U Z).contains (aList U Z)[k]! = true := by
  rw [Array.contains_iff_mem, getElem!_pos (aList U Z) k (by rw [size_aList F]; exact hk)]
  exact Array.getElem_mem _

theorem inA_mem {x : ℕ} (hx : x < 243) (h : inA x = true) :
    (aList U Z).contains (t3List U Z O)[x]! = true := by
  have e : aI (kOf x) = x := Nat.eq_of_beq_eq_true h
  rw [← e, ← aL F (kOf_lt hx)]
  exact memA F (kOf_lt hx)

end Facts

section Checks

variable {U Z O : Array ℕ} (F : Facts U Z O) (hI : chkI = true)
include F hI

theorem t3OK_F : t3OK (t3List U Z O) = true := by
  simp only [chkI, Bool.and_eq_true] at hI
  have hinv := hI.1.1.1.1
  simp only [pcInvOKG, List.all_eq_true, List.mem_range] at hinv
  refine t3OK_of (size_t3List _ _ _) (zeroL F) (fun i hi j hj e => ?_)
    (fun i hi j hj => ⟨_, pm_lt i j, mulL F hi hj⟩)
    (fun i hi => ⟨pcInvG 4 6 4 4 i, pm_lt _ _, ?_⟩)
  · exact absurd (F.inj i hi j (by omega) e) (by omega)
  · have hlt : pcInvG 4 6 4 4 i < 243 := pcMulG_lt _ _ _ _ _ _
    rw [mulL F hi hlt]
    have e : pm i (pcInvG 4 6 4 4 i) = 0 := Nat.eq_of_beq_eq_true (hinv i hi)
    rw [e, zeroL F]

omit hI in
theorem frobStable_F : frobStable (t3List U Z O) = true := by
  simp only [frobStable, List.all_eq_true, List.mem_range, size_t3List]
  intro n hn
  rw [frobL F hn]
  exact memL F (pcIdx_lt _ _ _)

theorem centerOK_F : centerOK (t3List U Z O) [(U, 0), (Z, 0), (O, 0), (idCode, 1)]
    (powCode U 3) = true := by
  simp only [chkI, Bool.and_eq_true] at hI
  have hc := hI.1.1.1.2
  simp only [cenI, List.all_eq_true, List.mem_range] at hc
  simp only [centerOK, List.all_eq_true, List.mem_range]
  intro n hn s hs
  have h := hc n hn s hs
  rw [gensL F, allGensL F hn s, natBeq s 0, ezz F, ezc F, idL F hn, beqL F hn (by norm_num),
    beqL F hn (by norm_num)]
  exact h

omit hI in
theorem zOKc_F : zOKc (t3List U Z O) (powCode U 3) [(U, 0), (Z, 0), (O, 0), (idCode, 1)] =
    true := by
  rw [zOKc, gensL F, ezc F, allGensL F (by norm_num) 0, bne, idL F (by norm_num),
    pwL F (by norm_num), idL F (pw9_lt _ _), frobL F (by norm_num),
    beqL F (fr_lt _) (by norm_num), beqL F (by norm_num) (by norm_num)]
  decide +kernel

theorem aOK_F : aOK (t3List U Z O) U Z = true := by
  simp only [chkI, Bool.and_eq_true] at hI
  have ha := hI.1.1.2
  simp only [aOKI, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true,
    Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨ha0, hcl⟩, hinv⟩, hd⟩ := ha
  simp only [aOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true,
    bne_iff_ne, ne_eq]
  have hA : ∀ {t}, t < 81 → aI t < 243 := fun _ => pcIdx_lt _ _ _
  refine ⟨⟨⟨⟨?_, fun i hi j hj => ?_⟩, fun i hi => ?_⟩, fun i hi j hj => ?_⟩, fun i hi => ?_⟩
  · rw [aL F (by norm_num), idL F (hA (by norm_num))]
    exact ha0
  · rw [aL F hi, aL F hj, mulL F (hA hi) (hA hj)]
    exact inA_mem F (pm_lt _ _) (hcl i hi j hj)
  · obtain ⟨j, hj, e⟩ := hinv i hi
    refine ⟨j, hj, ?_⟩
    rw [aL F hi, aL F hj, mulL F (hA hi) (hA hj), idL F (pm_lt _ _)]
    exact e
  · intro e
    rw [aL F hi, aL F (by omega)] at e
    have := hd i hi j hj
    rw [beq_true (F.inj _ (hA hi) _ (hA (by omega)) e)] at this
    exact absurd this (by decide)
  · rw [aL F hi]
    exact memL F (hA hi)

theorem omegaOK_F : omegaOK U Z = true := by
  simp only [chkI, Bool.and_eq_true] at hI
  have ho := hI.1.2
  simp only [omI, List.all_eq_true, List.mem_range] at ho
  simp only [omegaOK, List.all_eq_true, List.mem_range]
  intro t ht
  rw [aL F ht, pwL F (aI_lt _), bne, idL F (pw9_lt _ _), natBeq, natBeq]
  exact ho t ht

theorem compOK_F : compOK (t3List U Z O) U Z = true := by
  simp only [chkI, Bool.and_eq_true] at hI
  have hc := hI.2
  simp only [compI, List.all_eq_true, List.mem_range] at hc
  simp only [compOK, List.all_eq_true, List.mem_range]
  intro n hn
  have h := hc n hn
  simp only [Bool.or_eq_true] at h ⊢
  rw [ezc F, ez9 F, pwL F hn, bne, bne, bne, idL F (pw9_lt _ _),
    mulL F hn (by norm_num), mulL F (by norm_num) hn, mulL F hn (by norm_num),
    mulL F (by norm_num) hn, beqL F (pm_lt _ _) (pm_lt _ _),
    beqL F (pm_lt _ _) (pm_lt _ _)]
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (inA_mem F hn h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

omit hI in
theorem qOK_F {b y : ℕ} (hb : b < 243) (hy : y < 243)
    (h : (Nat.blt b 243 && Nat.blt y 243 && !Nat.beq b 0 && !Nat.beq b 81 && !Nat.beq b 162 &&
      Nat.beq (pw9 b 3) 0 && Nat.beq (pm 81 b) (pm b 81) &&
      (Nat.beq (pm y (frI 1 (pm y (frI 1 y)))) 0 && Nat.beq ((1 + (1 + 1) % 3) % 3) 0) &&
      sc y 1 81 0 && sc y 1 b 0) = true) :
    qOK (t3List U Z O) (powCode U 3) b y = true := by
  have hyy : pm y (frI 1 y) < 243 := pm_lt _ _
  rw [qOK, ezz F, ezc F, bne, bne, bne, idL F hb, beqL F hb (by norm_num),
    beqL F hb (by norm_num), pwL F hb, idL F (pw9_lt _ _), mulL F (by norm_num) hb,
    mulL F hb (by norm_num), beqL F (pm_lt _ _) (pm_lt _ _),
    semiL F hy hy, semiL F hy hyy, semiOne, ← zeroL F,
    pairBeqL F (pm_lt _ _) (by norm_num), scL F hy (by norm_num), scL F hy hb]
  have e1 : decide (b < 243) = Nat.blt b 243 := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
  have e2 : decide (y < 243) = Nat.blt y 243 := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
  rw [e1, e2]
  exact h

end Checks

section Words

variable {U Z O : Array ℕ} (F : Facts U Z O)
include F

theorem fldTL {k : ℕ} (hk : k < 243) :
    fldT (bldT 108 (elT (powT (codeP U) 9) (powT (codeP Z) 9) (powT (codeP O) 3)) 243) k =
      codeP (t3List U Z O)[k]! :=
  fldT_t3 F.vU F.vZ F.vO hk

theorem qL {b : ℕ} (hb : b < 243) {m : ℕ} (hm : m < 9) :
    (qList ((t3List U Z O)[81]!) ((t3List U Z O)[b]!))[m]! = (t3List U Z O)[qIdx b m]! := by
  rw [qList, getElem!_ofFn_nat' _ hm]
  dsimp only
  rw [pwL F (by norm_num), pwL F hb, mulL F (pw9_lt _ _) (pw9_lt _ _)]
  rfl

theorem gOne {g : List ℕ} {b : ℕ} (hb : b < 243)
    (h : gChk1 (bldT 108 (elT (powT (codeP U) 9) (powT (codeP Z) 9) (powT (codeP O) 3)) 243)
      g b = true) :
    mulCode (wordCode g) (wordCode g.reverse) = idCode ∧
      mulCode (wordCode g.reverse) (wordCode g) = idCode ∧
      (mulCode (mulCode (wordCode g) (t3List U Z O)[81]!) (wordCode g.reverse) =
          (t3List U Z O)[81]! ∨
        mulCode (mulCode (wordCode g) (t3List U Z O)[81]!) (wordCode g.reverse) =
          (t3List U Z O)[162]!) ∧
      (qList ((t3List U Z O)[81]!) ((t3List U Z O)[b]!)).contains
        (mulCode (mulCode (wordCode g) (t3List U Z O)[b]!) (wordCode g.reverse)) = true := by
  simp only [gChk1, letB_eq, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
    List.mem_range] at h
  obtain ⟨⟨e1, e2⟩, e3, m, hm, e4⟩ := h
  have vg := valid_wordCode g
  have vgi := valid_wordCode g.reverse
  have cj : ∀ {k}, k < 243 → codeP (mulCode (mulCode (wordCode g) (t3List U Z O)[k]!)
      (wordCode g.reverse)) = mulP (mulP (wordP g) (fldT (bldT 108 (elT (powT (codeP U) 9)
        (powT (codeP Z) 9) (powT (codeP O) 3)) 243) k)) (wordP g.reverse) := fun hk => by
    rw [codeP_mulCode (valid_mulCode vg (hV F hk)) vgi, codeP_mulCode vg (hV F hk),
      codeP_wordCode, codeP_wordCode, fldTL F hk]
  have v81 : Valid (mulCode (mulCode (wordCode g) (t3List U Z O)[81]!) (wordCode g.reverse)) :=
    valid_mulCode (valid_mulCode vg (hV F (by norm_num))) vgi
  refine ⟨eq_of_beq_codeP (valid_mulCode vg vgi) valid_idCode
      (by rw [codeP_mulCode vg vgi, codeP_wordCode, codeP_wordCode]) codeP_idCode e1,
    eq_of_beq_codeP (valid_mulCode vgi vg) valid_idCode
      (by rw [codeP_mulCode vgi vg, codeP_wordCode, codeP_wordCode]) codeP_idCode e2, ?_, ?_⟩
  · rcases e3 with e3 | e3
    · exact Or.inl (eq_of_beq_codeP v81 (hV F (by norm_num)) (cj (by norm_num))
        (fldTL F (by norm_num)).symm e3)
    · exact Or.inr (eq_of_beq_codeP v81 (hV F (by norm_num)) (cj (by norm_num))
        (fldTL F (by norm_num)).symm e3)
  · have hq : qIdx b m < 243 := pm_lt _ _
    have e := eq_of_beq_codeP (valid_mulCode (valid_mulCode vg (hV F hb)) vgi) (hV F hq) (cj hb)
      (fldTL F hq).symm e4
    rw [e, ← qL F hb hm, Array.contains_iff_mem,
      getElem!_pos _ m (by simp [qList]; exact hm)]
    exact Array.getElem_mem _

theorem gOK_F {gw : List (List ℕ)}
    (h : gChk (bldT 108 (elT (powT (codeP U) 9) (powT (codeP Z) 9) (powT (codeP O) 3)) 243)
      gw [55, 55, 10, 10] = true) :
    gOK (powCode U 3) (t3List U Z O)[55]! (t3List U Z O)[10]! gw = true := by
  simp only [gChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hj⟩ := h
  simp only [gOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq]
  refine ⟨Nat.eq_of_beq_eq_true hlen, fun j hj4 => ?_⟩
  rw [list_getElem!, ezz F, ezc F]
  have hb : ([55, 55, 10, 10] : List ℕ).getD j 0 < 243 := by interval_cases j <;> decide
  have hif : (if j < 2 then (t3List U Z O)[55]! else (t3List U Z O)[10]!) =
      (t3List U Z O)[([55, 55, 10, 10] : List ℕ).getD j 0]! := by
    interval_cases j <;> rfl
  rw [hif]
  obtain ⟨g1, g2, g3, g4⟩ := gOne F hb (hj j hj4)
  exact ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩

end Words

theorem sound9557 {uw zw ow : List ℕ} {gw : List (List ℕ)}
    (hP : chkP uw zw ow gw [55, 55, 10, 10] = true) (hI : chkI = true) :
    t3OK (t3List (wordCode uw) (wordCode zw) (wordCode ow)) = true ∧
      frobStable (t3List (wordCode uw) (wordCode zw) (wordCode ow)) = true ∧
      centerOK (t3List (wordCode uw) (wordCode zw) (wordCode ow))
        [(wordCode uw, 0), (wordCode zw, 0), (wordCode ow, 0), (idCode, 1)]
        (powCode (wordCode uw) 3) = true ∧
      zOKc (t3List (wordCode uw) (wordCode zw) (wordCode ow)) (powCode (wordCode uw) 3)
        [(wordCode uw, 0), (wordCode zw, 0), (wordCode ow, 0), (idCode, 1)] = true ∧
      aOK (t3List (wordCode uw) (wordCode zw) (wordCode ow)) (wordCode uw) (wordCode zw) =
        true ∧
      omegaOK (wordCode uw) (wordCode zw) = true ∧
      compOK (t3List (wordCode uw) (wordCode zw) (wordCode ow)) (wordCode uw) (wordCode zw) =
        true ∧
      qOK (t3List (wordCode uw) (wordCode zw) (wordCode ow)) (powCode (wordCode uw) 3) 55 9 =
        true ∧
      qOK (t3List (wordCode uw) (wordCode zw) (wordCode ow)) (powCode (wordCode uw) 3) 10 0 =
        true ∧
      gOK (powCode (wordCode uw) 3) (t3List (wordCode uw) (wordCode zw) (wordCode ow))[55]!
        (t3List (wordCode uw) (wordCode zw) (wordCode ow))[10]! gw = true := by
  simp only [chkP, letB_eq, Bool.and_eq_true] at hP
  obtain ⟨⟨⟨⟨hrel, hfu⟩, hfz⟩, hfo⟩, hdist, hg⟩ := hP
  rw [← codeP_wordCode uw, ← codeP_wordCode zw, ← codeP_wordCode ow] at hrel hdist hg
  rw [← codeP_wordCode uw] at hfu
  rw [← codeP_wordCode zw] at hfz
  rw [← codeP_wordCode ow] at hfo
  have vU := valid_wordCode uw
  have vZ := valid_wordCode zw
  have vO := valid_wordCode ow
  have hd : ∀ i < 243, ∀ j < i, (t3List (wordCode uw) (wordCode zw) (wordCode ow))[i]! ≠
      (t3List (wordCode uw) (wordCode zw) (wordCode ow))[j]! := by
    simp only [distinctT, List.all_eq_true, List.mem_range, letB_eq, Bool.not_eq_true'] at hdist
    intro i hi j hj e
    have := hdist i hi j hj
    rw [fldT_t3 vU vZ vO hi, fldT_t3 vU vZ vO (by omega), e, Nat.beq_refl] at this
    exact absurd this (by decide)
  have F : Facts (wordCode uw) (wordCode zw) (wordCode ow) := {
    vU := vU, vZ := vZ, vO := vO, R := relsG_of vU vZ vO hrel
    inj := fun i hi j hj e => by
      rcases lt_trichotomy i j with h | h | h
      · exact absurd e.symm (hd j hj i h)
      · exact h
      · exact absurd e (hd i hi j h)
    fU := by
      rw [frobCode_wordCode]
      exact eq_of_beq_codeP (valid_wordCode _) (valid_powCode vU 7) (codeP_wordCode _)
        (codeP_powCode vU 7) hfu
    fZ := by
      rw [frobCode_wordCode]
      exact eq_of_beq_codeP (valid_wordCode _) (valid_powCode vZ 7) (codeP_wordCode _)
        (codeP_powCode vZ 7) hfz
    fO := by
      rw [frobCode_wordCode]
      exact eq_of_beq_codeP (valid_wordCode _) vO (codeP_wordCode _) rfl hfo }
  exact ⟨t3OK_F F hI, frobStable_F F, centerOK_F F hI, zOKc_F F, aOK_F F hI, omegaOK_F F hI,
    compOK_F F hI, qOK_F F (by norm_num) (by norm_num) (by decide +kernel),
    qOK_F F (by norm_num) (by norm_num) (by decide +kernel), gOK_F F hg⟩

end CFSG.KC.CertF8.G9557

end
