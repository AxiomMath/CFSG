module

public import Certificates.Data.Kernel.SmithEKG
public import CFSG.LargeExtraspecial.SMod20BasicCheck
public import CFSG.Certificates.Kernel.SmithEK.MSound
public import CFSG.Certificates.Kernel.SmithEK.TvSound

public section

namespace CFSG.SmithE.K

open CFSG.SmithE CFSG.F4.Native

theorem bitsOf_cons (b x : Nat) (L : List Nat) :
    bitsOf b (x :: L) = (x >>> b) % 2 + 2 * bitsOf b L := rfl

theorem testBit_bitsOf (b : Nat) : ∀ (L : List Nat) (j : Nat),
    (bitsOf b L).testBit j = (decide (j < L.length) && (L.getD j 0).testBit b)
  | [], j => by simp [bitsOf]
  | x :: L, 0 => by
    have e : x.testBit b = (x >>> b).testBit 0 := by rw [Nat.testBit_shiftRight, Nat.add_zero]
    rw [bitsOf_cons, List.getD_cons_zero, e]
    simp only [Nat.testBit_zero]
    simp [Nat.add_mul_mod_self_left]
  | x :: L, j + 1 => by
    rw [bitsOf_cons]
    have e : ((x >>> b) % 2 + 2 * bitsOf b L) / 2 = bitsOf b L := by omega
    rw [Nat.testBit_succ, e, testBit_bitsOf b L j]
    simp

@[expose] def fxB (a : Nat → Bool) : List Bool → Nat → Bool
  | [], _ => false
  | c :: cs, b => (a (b ^^^ 1) && c) ^^ fxB a cs (b + 1)

theorem testBit_formRow (u j : Nat) : ∀ (Bs : List Nat) (b : Nat),
    (formRow u Bs b).testBit j = fxB u.testBit (Bs.map (·.testBit j)) b
  | [], b => by simp [formRow, fxB]
  | B :: Bs, b => by
    have e : formRow u (B :: Bs) b =
        (bif u.testBit (b ^^^ 1) then B else 0) ^^^ formRow u Bs (b + 1) := rfl
    rw [e, Nat.testBit_xor, testBit_formRow u j Bs (b + 1), List.map_cons, fxB]
    cases u.testBit (b ^^^ 1) <;> simp

theorem xor_one_even (s : Nat) : (2 * s) ^^^ 1 = 2 * s + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · have h0 : (2 * s) % 2 = 0 := by omega
    have h1 : (2 * s + 1) % 2 = 1 := by omega
    simp [Nat.testBit_zero, h0, h1]
  · have h0 : (2 * s) / 2 = s := by omega
    have h1 : (2 * s + 1) / 2 = s := by omega
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, h0, h1]
    simp

theorem xor_one_odd (s : Nat) : (2 * s + 1) ^^^ 1 = 2 * s := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · have h0 : (2 * s) % 2 = 0 := by omega
    have h1 : (2 * s + 1) % 2 = 1 := by omega
    simp [Nat.testBit_zero, h0, h1]
  · have h0 : (2 * s) / 2 = s := by omega
    have h1 : (2 * s + 1) / 2 = s := by omega
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, h0, h1]
    simp

theorem fx_step (a b : Nat → Bool) : ∀ (n s : Nat) (acc : Bool),
    (List.range' s n).foldl (fun acc k => acc ^^
      ((a (2 * k) && b (2 * k + 1)) ^^ (a (2 * k + 1) && b (2 * k)))) acc =
      (acc ^^ fxB a ((List.range' (2 * s) (2 * n)).map b) (2 * s))
  | 0, s, acc => by simp [fxB]
  | n + 1, s, acc => by
    have e1 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    have e2 : 2 * (s + 1) = 2 * s + 1 + 1 := by ring
    rw [List.range'_succ, List.foldl_cons, fx_step a b n (s + 1), e1, List.range'_succ,
      List.range'_succ, e2]
    simp only [List.map_cons, fxB]
    rw [xor_one_even s, xor_one_odd s]
    generalize fxB a (List.map b (List.range' (2 * s + 1 + 1) (2 * n))) (2 * s + 1 + 1) = X
    cases a (2 * s) <;> cases a (2 * s + 1) <;> cases b (2 * s) <;> cases b (2 * s + 1) <;>
      cases acc <;> cases X <;> rfl

theorem fx_pairs (a b : Nat → Bool) :
    (List.range 10).foldl (fun acc k => acc ^^
      ((a (2 * k) && b (2 * k + 1)) ^^ (a (2 * k + 1) && b (2 * k)))) false =
      fxB a ((List.range 20).map b) 0 := by
  rw [List.range_eq_range', List.range_eq_range', fx_step a b 10 0 false, Bool.false_xor]

theorem fB_eq (u v : Nat) : fB u v = fxB u.testBit ((List.range 20).map v.testBit) 0 :=
  fx_pairs u.testBit v.testBit

theorem fB_planes {L : List Nat} {j : Nat} (hj : j < L.length) (u : Nat) :
    fB u (L.getD j 0) = (formRow u (planesOf L) 0).testBit j := by
  rw [testBit_formRow, fB_eq]
  congr 1
  simp only [planesOf, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp [testBit_bitsOf, hj]

theorem planePtsArr_get {i : Nat} (hi : i < 891) : planePtsArr[i]! = planePts i := by
  unfold planePtsArr
  exact CFSG.SmithL6.Kernel.ofFn_get! _ hi

theorem inPlane_eq {pts P : List Nat} (hpts : uPts () = pts.toArray) (hlen : pts.length = 693)
    (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) {k a : Nat} (hk : k < 891)
    (ha : a < 693) : inPlane k a = (P.getD k 0).testBit a := by
  rw [hP k hk, testBit_ptBits, hlen]
  simp only [inPlane, maskArr_get hk, hpts, CFSG.SmithL6.Kernel.get0, List.toList_toArray]
  simp [ha]

theorem mask_lt {pts P : List Nat} (hlen : pts.length = 693)
    (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) {k : Nat} (hk : k < 891) :
    P.getD k 0 < 2 ^ 693 := by
  rw [hP k hk, ← hlen]
  exact ptBits_lt _ _

theorem mem_planePts {i a : Nat} : a ∈ (planePts i).toList ↔ a < 693 ∧ inPlane i a = true := by
  simp [planePts]

theorem oppB_eq {pts P : List Nat} (hpts : uPts () = pts.toArray) (hlen : pts.length = 693)
    (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) {i j : Nat} (hi : i < 891)
    (hj : j < 891) : oppB i j = (P.getD i 0 &&& P.getD j 0 == 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  unfold oppB
  rw [planePtsArr_get hi, Array.all_eq_true_iff_forall_mem]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro a
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases ha : a < 693
    · by_cases hb : inPlane i a = true
      · have e := h a (Array.mem_toList_iff.mp (mem_planePts.mpr ⟨ha, hb⟩))
        rw [inPlane_eq hpts hlen hP hj ha] at e
        rw [← inPlane_eq hpts hlen hP hi ha, hb]
        simpa using e
      · rw [← inPlane_eq hpts hlen hP hi ha]
        simp [hb]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (mask_lt hlen hP hi)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp
  · intro h a ha
    obtain ⟨ha1, ha2⟩ := mem_planePts.mp (Array.mem_toList_iff.mpr ha)
    have e := congrArg (fun x => x.testBit a) h
    simp only [Nat.testBit_and, Nat.zero_testBit] at e
    rw [← inPlane_eq hpts hlen hP hi ha1, ← inPlane_eq hpts hlen hP hj ha1, ha2] at e
    simpa using e

theorem planePts_size {pts P : List Nat} (hpts : uPts () = pts.toArray)
    (hlen : pts.length = 693) (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) {i : Nat}
    (hi : i < 891) : (planePts i).size = cntK 693 (P.getD i 0) := by
  rw [cntK_eq 693 _ (mask_lt hlen hP hi) (cntB_le _ _)]
  unfold planePts cntB
  rw [List.size_toArray, ← List.countP_eq_length_filter]
  refine List.countP_congr fun a ha => ?_
  rw [inPlane_eq hpts hlen hP hi (List.mem_range.mp ha)]

theorem chkPlanes_of {pts P : List Nat} {M : Nat} (hpts : uPts () = pts.toArray)
    (hlen : pts.length = 693) (hPl : P.length = 891)
    (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) (h : planesK P M = true) :
    chkPlanes = true := by
  unfold planesK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hnd : P.Nodup := CFSG.Decide.nodup_of_bitsetNodup (· % M) h.2
  have hmem : ∀ i < 891, P.getD i 0 ∈ P := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  unfold chkPlanes
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, bne_iff_ne, ne_eq]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · rw [planePtsArr_get hi, planePts_size hpts hlen hP hi]
    exact beq_iff_eq.mp (h.1 _ (hmem i hi))
  · intro heq
    rw [planePtsArr_get hi, planePtsArr_get (by omega)] at heq
    have hbits : P.getD i 0 = P.getD j 0 := by
      apply Nat.eq_of_testBit_eq
      intro a
      by_cases ha : a < 693
      · rw [← inPlane_eq hpts hlen hP hi ha, ← inPlane_eq hpts hlen hP (by omega) ha]
        have e : a ∈ (planePts i).toList ↔ a ∈ (planePts j).toList := by rw [heq]
        rw [mem_planePts, mem_planePts] at e
        cases h1 : inPlane i a <;> cases h2 : inPlane j a <;> simp_all
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (mask_lt hlen hP hi)
          (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (mask_lt hlen hP (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hbits
    have := (List.Nodup.getElem_inj_iff hnd).mp hbits
    omega

theorem oppRowK_sound (Pi : Nat) : ∀ (P : List Nat) (R : Nat), oppRowK Pi P R = true →
    ∀ j < P.length, R.testBit j = (Pi &&& P.getD j 0 == 0)
  | [], _, _, j, hj => absurd hj (by simp)
  | Pj :: P, R, h, j, hj => by
    have h' : (((R % 2 == 1) == (Pi &&& Pj == 0)) && oppRowK Pi P (R >>> 1)) = true := h
    rw [Bool.and_eq_true, beq_iff_eq] at h'
    rcases j with _ | j
    · rw [List.getD_cons_zero, ← h'.1, Nat.testBit_zero]
      by_cases hR : R % 2 = 1 <;> simp [hR]
    · rw [Nat.testBit_succ, List.getD_cons_succ, ← Nat.shiftRight_one]
      exact oppRowK_sound Pi P _ h'.2 j (by simpa using hj)

theorem gramChunkK_sound {W P : List Nat} {s n : Nat} (h : gramChunkK W P s n = true) {i : Nat}
    (h1 : s ≤ i) (h2 : i < s + n) :
    oppRowK (P.getD i 0) P (formRow (W.getD i 0) (planesOf W) 0) = true := by
  unfold gramChunkK at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem chkGram_of {pts P W : List Nat} (hpts : uPts () = pts.toArray)
    (hlen : pts.length = 693) (hPl : P.length = 891)
    (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) (hWl : W.length = 891)
    (hW : ∀ i < 891, wtArr[i]! = W.getD i 0)
    (hrow : ∀ i < 891, oppRowK (P.getD i 0) P (formRow (W.getD i 0) (planesOf W) 0) = true) :
    chkGram = true := by
  unfold chkGram
  simp only [List.all_eq_true, List.mem_range]
  intro i hi j hj
  rw [hW i hi, hW j hj, fB_planes (by omega), oppRowK_sound _ _ _ (hrow i hi) j (by omega),
    oppB_eq hpts hlen hP hi hj]
  exact beq_self_eq_true _

theorem formColsK_sound (Bs : List Nat) : ∀ (T E : List Nat), formColsK Bs T E = true →
    ∀ a < T.length, formRow (T.getD a 0) Bs 0 = E.getD a 0
  | [], _, _, a, ha => absurd ha (by simp)
  | t :: T, E, h, a, ha => by
    have h' : ((formRow t Bs 0 == E.headD 0) && formColsK Bs T E.tail) = true := h
    rw [Bool.and_eq_true, beq_iff_eq] at h'
    rcases a with _ | a
    · rw [List.getD_cons_zero, h'.1]
      cases E <;> rfl
    · rw [List.getD_cons_succ, formColsK_sound Bs T E.tail h'.2 a (by simpa using ha)]
      cases E <;> simp

theorem idCols_length : idCols.length = 20 := by simp [idCols]

theorem idCols_get {a : Nat} (ha : a < 20) : idCols.getD a 0 = 2 ^ a := by
  simp [idCols, List.getD_eq_getElem?_getD, ha]

theorem chkFormInv_of {C : List (List Nat)} (hT : ∀ k, tvArr[k]! = (C.getD k []).toArray)
    (hl : C.length = 693) (hc : ∀ k < 693, (C.getD k []).length = 20)
    (h : formInvK C = true) : chkFormInv = true := by
  unfold formInvK at h
  rw [List.all_eq_true] at h
  unfold chkFormInv
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro k hk a ha b hb
  have hmem : C.getD k [] ∈ C := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hr := formColsK_sound _ _ _ (h _ hmem) a (by rw [hc k hk]; exact ha)
  rw [hT k, getElem!_toArray, getElem!_toArray]
  have hbl : b < (C.getD k []).length := by rw [hc k hk]; exact hb
  rw [fB_planes hbl, hr, ← idCols_get ha, ← idCols_get hb,
    fB_planes (by rw [idCols_length]; exact hb)]
  congr 1
  simp [idCols, List.getD_eq_getElem?_getD, ha]

end CFSG.SmithE.K
