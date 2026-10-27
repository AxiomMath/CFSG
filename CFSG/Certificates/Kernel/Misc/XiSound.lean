module

public import CFSG.Certificates.Kernel.Misc.XiMu
public import CFSG.Certificates.Kernel.Misc.XiOrb
public import CFSG.Certificates.Kernel.Misc.XiRows
public import CFSG.Certificates.Kernel.Misc.XiTab
public import Mathlib.Tactic.Polynomial.Basic

public section

set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Xi

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73
  CFSG.KS.TW

@[expose] def rootFlagsG (U : Array Nat) (c : Nat) : Flags :=
  Array.ofFn (n := 693) fun p =>
    let v := U[p.val]!
    nzC v == 2 || (nzC v == 6 && prodCoordC v == c)

@[expose] def hypEnumG (U : Array Nat) (xw yw : List Int) (c : Nat) :
    Array Flags × Array Nat × Array Nat :=
  orbitEnum (rootFlagsG U c) #[powG U 3 xw, powG U 2 yw]
    #[powG U 3 xw, compT 693 (powG U 2 yw) (powG U 2 yw)] 1408

@[expose] def xiImgG (U : Array Nat) (H : Array Flags) (ix : Std.HashMap (Array UInt64) Nat) :
    Array (Array Nat) :=
  Array.ofFn (n := 1408) fun k =>
    let S := H[k.val]!
    let M := members S
    Array.ofFn (n := 693) fun f =>
      if S[f.val]! then k.val else findIn ix 4224 (packImg (tvTabsG U)[f.val]! M)

@[expose] def xiImgOKG (U : Array Nat) (H : Array Flags) (Im Iv : Array (Array Nat)) : Bool :=
  allIn 0 1408 fun k =>
    let S := H[k]!
    let M := members S
    let row := Im[k]!
    let irow := Iv[k]!
    irow.size == 1408 && allIn 0 693 (fun f => S[f]! ||
      (let i := row[f]!
       i < 1408 && i != k && irow[i]! == f && (let T := (tvTabsG U)[f]!; let Si := H[i]!;
         M.all fun p => Si[ap T p]!))) &&
    allIn 0 1408 fun i => irow[i]! == 693 ||
      (let f := irow[i]!; f < 693 && !S[f]! && row[f]! == i)

@[expose] def xiChecksG (U : Array Nat) (P : Array Flags) (H : Array Flags) : Bool :=
  let ix := famIndex H
  let Im := xiImgG U H ix
  let Iv := xiInv H Im
  let A := xiAdj Iv
  H.size == 4224 && xiImgOKG U H Im Iv && xiInterOK H A && perpCountOK P (rootFlagsG U 1) &&
    perpCountOK P (rootFlagsG U 2) && perpCountOK P (rootFlagsG U 3) && xiDiamOK A && xiMuOK A

@[expose] def xiG (U : Array Nat) (xw yw : List Int) : Bool :=
  xiChecksG U (perpTabG U)
    ((hypEnumG U xw yw 1).1 ++ (hypEnumG U xw yw 2).1 ++ (hypEnumG U xw yw 3).1)

theorem xi_eq : xiCertificate () = xiG uPts [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] :=
  rfl

@[expose] def hypSetsA (HS : Nat → Nat) (o : Nat) : Array Flags :=
  Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j))

theorem concat_eq (HS : Nat → Nat) :
    hypSetsA HS 0 ++ hypSetsA HS 1 ++ hypSetsA HS 2 =
      Array.ofFn (n := 4224) fun j => fl (HS j) := by
  apply Array.ext
  · simp [hypSetsA]
  · intro j h1 h2
    have hj : j < 4224 := by simpa [hypSetsA] using h1
    rw [Array.getElem_ofFn]
    by_cases hj1 : j < 1408
    · rw [Array.getElem_append_left (by simp [hypSetsA]; omega),
        Array.getElem_append_left (by simp [hypSetsA]; omega)]
      simp only [hypSetsA, Array.getElem_ofFn]
      congr 2
      omega
    · by_cases hj2 : j < 2816
      · rw [Array.getElem_append_left (by simp [hypSetsA]; omega),
          Array.getElem_append_right (by simp [hypSetsA]; omega)]
        simp only [hypSetsA, Array.getElem_ofFn, Array.size_ofFn]
        congr 2
        omega
      · rw [Array.getElem_append_right (by simp [hypSetsA]; omega)]
        simp only [hypSetsA, Array.getElem_ofFn, Array.size_ofFn, Array.size_append]
        congr 2
        omega

structure GenFacts (XP YP : Nat) : Prop where
  xlt : ∀ p < 693, fd 10 XP p < 693
  ylt : ∀ p < 693, fd 10 YP p < 693
  xx : ∀ p < 693, fd 10 XP (fd 10 XP p) = p
  yyy : ∀ p < 693, fd 10 YP (fd 10 YP (fd 10 YP p)) = p

structure ConjFacts (TP : Nat → Nat) (XP YP : Nat) : Prop where
  cx : ∀ p < 693, ∀ q < 693, fd 10 XP (fd 10 (TP p) (fd 10 XP q)) = fd 10 (TP (fd 10 XP p)) q
  cy : ∀ p < 693, ∀ q < 693,
    fd 10 YP (fd 10 (TP p) (fd 10 YP (fd 10 YP q))) = fd 10 (TP (fd 10 YP p)) q
  tlt : ∀ f < 693, ∀ p < 693, fd 10 (TP f) p < 693

@[expose] def RowOK (HS RW TP : Nat → Nat) (k : Nat) : Prop :=
  ∀ f < 693, (HS k).testBit f = false →
    fd 11 (RW k) f < 1408 ∧ fd 11 (RW k) f ≠ k ∧
    ∀ q, (HS (fd 11 (RW k) f)).testBit q = true ↔
      ∃ p < 693, (HS k).testBit p = true ∧ fd 10 (TP f) p = q

theorem rows_ok {TP HS ML RW AB : Nat → Nat} {XP YP J0 PA : Nat} (hG : GenFacts XP YP)
    (hCj : ConjFacts TP XP YP) (hmem : ∀ k < 4224, listsP (HS k) (ML k) = true)
    (hrow0 : rowsK TP HS ML RW AB 0 1 = true)
    (hrows : ∀ k < 11, rowsR HS RW AB XP YP J0 PA (128 * k) 128 = true) (hpa : paK J0 PA = true)
    (hacyc : ∀ k, 0 < k → k < 1408 → fd 12 PA k / 2 < k)
    (hJ : ∀ t < 2816, fd 11 J0 t < 1408)
    (horb : ∀ t < 2816, ∀ q, (HS (fd 11 J0 t)).testBit q = true ↔
      ∃ p < 693, (HS (t / 2)).testBit p = true ∧ fd 10 (if t % 2 = 1 then YP else XP) p = q) :
    ∀ k < 1408, RowOK HS RW TP k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨hc, himg⟩ := rowsK_spec hrow0
      intro f hf hnot
      refine ⟨(hc.outS f hf hnot).1, (hc.outS f hf hnot).2, fun q => ?_⟩
      rw [himg f hf hnot]
      exact img_set_iff (hmem 0 (by omega))
    · have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
      obtain ⟨hc, hrowf⟩ := rowsR_spec hrows hk0' hk
      obtain ⟨he1, he2⟩ := paK_spec hpa hk0' hk
      have hpar : fd 12 PA k / 2 < k := hacyc k hk0' hk
      have ihp := ih (fd 12 PA k / 2) hpar (by omega)
      have hl2 : fd 12 PA k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hk4 := horb (fd 12 PA k) he1
      rw [he2] at hk4
      set e := fd 12 PA k with he
      set gf : Nat → Nat := fun p => fd 10 (if e % 2 = 1 then YP else XP) p with hgf
      set Gf : Nat → Nat := fun p => fd 10 (if e % 2 = 1 then compP 693 10 YP YP else XP) p
        with hGf
      have hgl : ∀ p < 693, gf p < 693 := by
        intro p hp
        by_cases h1 : e % 2 = 1
        · simp only [hgf, if_pos h1]; exact hG.ylt p hp
        · simp only [hgf, if_neg h1]; exact hG.xlt p hp
      have hGl : ∀ p < 693, Gf p < 693 := by
        intro p hp
        by_cases h1 : e % 2 = 1
        · simp only [hGf, if_pos h1]
          rw [fd_compP _ _ hp]
          exact hG.ylt _ (hG.ylt _ hp)
        · simp only [hGf, if_neg h1]; exact hG.xlt p hp
      have hinv2 : ∀ p < 693, gf (Gf p) = p := by
        intro p hp
        by_cases h1 : e % 2 = 1
        · simp only [hGf, hgf, if_pos h1]
          rw [fd_compP _ _ hp, hG.yyy p hp]
        · simp only [hGf, hgf, if_neg h1]
          exact hG.xx p hp
      have hconj : ∀ f < 693, ∀ q < 693, fd 10 (TP f) (gf q) = gf (fd 10 (TP (Gf f)) q) := by
        intro f hf q hq
        by_cases h1 : e % 2 = 1
        · simp only [hGf, hgf, if_pos h1]
          have hq' : fd 10 YP q < 693 := hG.ylt q hq
          have hp0 : fd 10 (compP 693 10 YP YP) f < 693 := by
            rw [fd_compP _ _ hf]; exact hG.ylt _ (hG.ylt _ hf)
          have := hCj.cy _ hp0 _ hq'
          rw [fd_compP _ _ hf] at this ⊢
          rw [hG.yyy q hq, hG.yyy f hf] at this
          exact this.symm
        · simp only [hGf, hgf, if_neg h1]
          have hq' : fd 10 XP q < 693 := hG.xlt q hq
          have hp0 : fd 10 XP f < 693 := hG.xlt f hf
          have := hCj.cx _ hp0 _ hq'
          rw [hG.xx q hq, hG.xx f hf] at this
          exact this.symm
      intro f hf hnot
      have hc' := hc.outS f hf hnot
      refine ⟨hc'.1, hc'.2, fun q => ?_⟩
      have hGf693 : Gf f < 693 := hGl f hf
      have hnotp : (HS (e / 2)).testBit (Gf f) = false := by
        cases hb : (HS (e / 2)).testBit (Gf f)
        · rfl
        · exfalso
          have := (hk4 (gf (Gf f))).2 ⟨Gf f, hGf693, hb, rfl⟩
          rw [hinv2 f hf] at this
          rw [hnot] at this
          exact absurd this (by simp)
      obtain ⟨hi1, hi2, hi3⟩ := ihp (Gf f) hGf693 hnotp
      have hrf := hrowf f hf hnot
      have hrf' : fd 11 (RW k) f = fd 11 J0 (2 * fd 11 (RW (e / 2)) (Gf f) + e % 2) := hrf
      have ht : 2 * fd 11 (RW (e / 2)) (Gf f) + e % 2 < 2816 := by omega
      have hh := horb _ ht
      have hdiv : (2 * fd 11 (RW (e / 2)) (Gf f) + e % 2) / 2 = fd 11 (RW (e / 2)) (Gf f) := by
        omega
      have hmod : (2 * fd 11 (RW (e / 2)) (Gf f) + e % 2) % 2 = e % 2 := by omega
      rw [hdiv, hmod] at hh
      rw [hrf', hh q]
      constructor
      · rintro ⟨p1, hp1, hb1, hgq⟩
        obtain ⟨p2, hp2, hb2, hp21⟩ := (hi3 p1).1 hb1
        refine ⟨gf p2, hgl p2 hp2, (hk4 _).2 ⟨p2, hp2, hb2, rfl⟩, ?_⟩
        rw [hconj f hf p2 hp2, hp21]
        exact hgq
      · rintro ⟨p, hp, hb, htq⟩
        obtain ⟨p2, hp2, hb2, hgp⟩ := (hk4 p).1 hb
        refine ⟨fd 10 (TP (Gf f)) p2, hCj.tlt _ hGf693 p2 hp2, (hi3 _).2 ⟨p2, hp2, hb2, rfl⟩, ?_⟩
        show gf (fd 10 (TP (Gf f)) p2) = q
        rw [← hconj f hf p2 hp2]
        show fd 10 (TP f) (fd 10 (if e % 2 = 1 then YP else XP) p2) = q
        rw [hgp]
        exact htq

theorem rootFlagsG_eq {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) (c : Nat) :
    rootFlagsG UL.toArray c = fl (rootK UP c) := by
  apply flags_eq (by simp [rootFlagsG])
  intro p hp
  have hroot := testBit_rootK UP c p
  have e : (rootFlagsG UL.toArray c)[p]! =
      (nzC (UL.getD p 0) == 2 || (nzC (UL.getD p 0) == 6 && prodCoordC (UL.getD p 0) == c)) := by
    unfold rootFlagsG
    rw [getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn]
    simp only [list_toArray_getElem!]
  rw [e, ← H.fd12 p hp, Bool.eq_iff_iff, hroot, nzK_eq, prodK_eq]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact ⟨hp, h⟩
  · intro h
    exact h.2

theorem perpCountOK_of {P : Array Flags} {PB : Nat → Nat} {R : Nat}
    (hP : ∀ x < 693, ∀ y < 693, (P[x]!)[y]! = bitK (PB x) y)
    (hR : ∀ f < 693, R.testBit f = true ∨
      cnt (fun p => R.testBit p && (PB f).testBit p) 693 = 30) :
    perpCountOK P (fl R) = true := by
  unfold perpCountOK
  rw [allIn_iff']
  intro f _ hf
  simp only [Bool.or_eq_true, beq_iff_eq]
  rcases hR f hf with h | h
  · left
    rw [fl_get R hf]
    exact h
  · right
    rw [len_filter_members R, ← h]
    apply cnt_congr
    intro p hp
    rw [hP f hf p hp, bitK_eq_testBit]

theorem xiInterOK_of {H A : Array Flags} {HS AB : Nat → Nat}
    (hH : ∀ i < 4224, H[i]! = fl (HS i))
    (hA : ∀ i < 1408, (A[0]!)[i]! = (AB 0).testBit i)
    (h : ∀ i, 1 ≤ i → i < 1408 → cnt (fun p => (HS 0).testBit p && (HS i).testBit p) 693 =
      if (AB 0).testBit i = true then 30 else 18) :
    xiInterOK H A = true := by
  unfold xiInterOK
  rw [allIn_iff']
  intro i hi1 hi2
  have hc : ((members H[0]!).filter (fun p => (H[i]!)[p]!)).length =
      cnt (fun p => (HS 0).testBit p && (HS i).testBit p) 693 := by
    rw [hH 0 (by omega), hH i (by omega), len_filter_members]
    apply cnt_congr
    intro p hp
    rw [fl_get _ hp]
  rw [hA i hi2]
  show (if (AB 0).testBit i = true then
      decide (((members H[0]!).filter (fun p => (H[i]!)[p]!)).length = 30)
    else decide (((members H[0]!).filter (fun p => (H[i]!)[p]!)).length = 18)) = true
  rw [hc, h i hi1 hi2]
  by_cases hb : (AB 0).testBit i = true <;> simp [hb]

theorem anyIn_iff {n : Nat} {p : Nat → Bool} : anyIn n p = true ↔ ∃ i < n, p i = true := by
  unfold anyIn
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, allIn_iff']
  simp only [Bool.not_eq_true']
  constructor
  · intro h
    by_contra hcon
    apply h
    intro i _ hi
    by_contra hp
    exact hcon ⟨i, hi, by simpa using hp⟩
  · rintro ⟨i, hi, hp⟩ h
    have := h i (Nat.zero_le _) hi
    simp [hp] at this

theorem xiDiamOK_of {A : Array Flags} {AB : Nat → Nat}
    (hA : ∀ k < 1408, ∀ i < 1408, (A[k]!)[i]! = (AB k).testBit i)
    (hAB : ∀ x < 1408, AB x < 2 ^ 1408)
    (hsym : ∀ x < 1408, ∀ v < 1408, (AB x).testBit v = (AB v).testBit x)
    (hd : ∀ v, 0 < v → v < 1408 → (AB 0).testBit v = false →
      Nat.land (AB 0) (AB v) ≠ 0 ∧ ∀ w < 1408, 0 < w → (AB 0).testBit w = false →
        (AB v).testBit w = true → Nat.land (Nat.land (AB 0) (AB v)) (AB w) ≠ 0) :
    xiDiamOK A = true := by
  unfold xiDiamOK
  rw [allIn_iff']
  intro v hv1 hv2
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  by_cases h0 : (A[0]!)[v]! = true
  · exact Or.inl h0
  · right
    have hn : (AB 0).testBit v = false := by
      rw [← hA 0 (by omega) v hv2]
      simpa using h0
    obtain ⟨hC, hall⟩ := hd v hv1 hv2 hn
    have hCl : Nat.land (AB 0) (AB v) < 2 ^ 1408 := Nat.and_lt_two_pow (AB 0) (hAB v hv2)
    refine ⟨anyIn_iff.2 ?_, ?_⟩
    · obtain ⟨x, hx⟩ := Nat.exists_testBit_of_ne_zero hC
      have hx1408 : x < 1408 := by
        by_contra hcon
        have := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hCl (Nat.pow_le_pow_right
          (by norm_num) (Nat.not_lt.1 hcon)))
        rw [hx] at this
        exact absurd this (by simp)
      refine ⟨x, hx1408, ?_⟩
      have hx' : (AB 0).testBit x = true ∧ (AB v).testBit x = true := by
        have := hx
        rw [show Nat.land (AB 0) (AB v) = AB 0 &&& AB v from rfl, Nat.testBit_and] at this
        simpa using this
      rw [Bool.and_eq_true, hA 0 (by omega) x hx1408, hA x hx1408 v hv2, hsym x hx1408 v hv2]
      exact hx'
    · rw [allIn_iff']
      intro w hw1 hw2
      simp only [Bool.or_eq_true, Bool.not_eq_true']
      by_cases hw0 : (A[0]!)[w]! = true
      · exact Or.inl (Or.inl hw0)
      · by_cases hvw : (A[v]!)[w]! = true
        · right
          have hn' : (AB 0).testBit w = false := by
            rw [← hA 0 (by omega) w hw2]
            simpa using hw0
          have hvw' : (AB v).testBit w = true := by
            rw [← hA v hv2 w hw2]
            exact hvw
          have hne := hall w hw2 (by omega) hn' hvw'
          have hCw : Nat.land (Nat.land (AB 0) (AB v)) (AB w) < 2 ^ 1408 :=
            Nat.and_lt_two_pow _ (hAB w hw2)
          obtain ⟨x, hx⟩ := Nat.exists_testBit_of_ne_zero hne
          have hx1408 : x < 1408 := by
            by_contra hcon
            have := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hCw (Nat.pow_le_pow_right
              (by norm_num) (Nat.not_lt.1 hcon)))
            rw [hx] at this
            exact absurd this (by simp)
          refine anyIn_iff.2 ⟨x, hx1408, ?_⟩
          have hx' : ((AB 0).testBit x = true ∧ (AB v).testBit x = true) ∧
              (AB w).testBit x = true := by
            have := hx
            rw [show Nat.land (Nat.land (AB 0) (AB v)) (AB w) = (AB 0 &&& AB v) &&& AB w from rfl,
              Nat.testBit_and, Nat.testBit_and] at this
            simpa using this
          rw [Bool.and_eq_true, Bool.and_eq_true, hA 0 (by omega) x hx1408, hA x hx1408 v hv2,
            hA x hx1408 w hw2, hsym x hx1408 v hv2, hsym x hx1408 w hw2]
          exact ⟨⟨hx'.1.1, hx'.1.2⟩, hx'.2⟩
        · left
          right
          simpa using hvw

theorem xiMuOK_of {A : Array Flags} {AB MT : Nat → Nat}
    (hA : ∀ k < 1408, ∀ i < 1408, (A[k]!)[i]! = (AB k).testBit i)
    (hAB : ∀ x < 1408, AB x < 2 ^ 1408)
    (hsym : ∀ x < 1408, ∀ v < 1408, (AB x).testBit v = (AB v).testBit x)
    (hm : ∀ v, 0 < v → v < 1408 → (AB 0).testBit v = false →
      fd 11 (MT v) 0 ≠ 0 ∧ (∀ x, (Nat.land (AB 0) (AB v)).testBit x = true ↔
        ∃ i < fd 11 (MT v) 0, fd 11 (MT v) (i + 1) = x) ∧
      ∀ i < fd 11 (MT v) 0, 0 < i → ∃ j < i,
        (AB (fd 11 (MT v) (i + 1))).testBit (fd 11 (MT v) (j + 1)) = true) :
    xiMuOK A = true := by
  unfold xiMuOK
  rw [allIn_iff']
  intro v hv1 hv2
  simp only [Bool.or_eq_true]
  by_cases h0 : (A[0]!)[v]! = true
  · exact Or.inl h0
  · right
    have hn : (AB 0).testBit v = false := by
      rw [← hA 0 (by omega) v hv2]
      simpa using h0
    obtain ⟨hm0, hC, hchain⟩ := hm v hv1 hv2 hn
    have hCl : Nat.land (AB 0) (AB v) < 2 ^ 1408 := Nat.and_lt_two_pow (AB 0) (hAB v hv2)
    have hEl : ∀ i < fd 11 (MT v) 0, fd 11 (MT v) (i + 1) < 1408 := by
      intro i hi
      have hb := (hC (fd 11 (MT v) (i + 1))).2 ⟨i, hi, rfl⟩
      by_contra hcon
      have := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hCl (Nat.pow_le_pow_right
        (by norm_num) (Nat.not_lt.1 hcon)))
      rw [hb] at this
      exact absurd this (by simp)
    refine muTreeOK_of (m := fd 11 (MT v) 0) (E := fun i => fd 11 (MT v) (i + 1))
      (fun x hx y hy => ?_) hm0 hEl (fun x => ?_) (fun i hi hi0 => ?_)
    · rw [hA x hx y hy, hA y hy x hx, hsym x hx y hy]
    · rw [← hC]
      constructor
      · rintro ⟨hx, h0x, hxv⟩
        rw [hA 0 (by omega) x hx] at h0x
        rw [hA x hx v hv2, hsym x hx v hv2] at hxv
        rw [show Nat.land (AB 0) (AB v) = AB 0 &&& AB v from rfl, Nat.testBit_and]
        simp [h0x, hxv]
      · intro hx
        have hx1408 : x < 1408 := by
          by_contra hcon
          have := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hCl (Nat.pow_le_pow_right
            (by norm_num) (Nat.not_lt.1 hcon)))
          rw [hx] at this
          exact absurd this (by simp)
        have hx' : (AB 0).testBit x = true ∧ (AB v).testBit x = true := by
          have := hx
          rw [show Nat.land (AB 0) (AB v) = AB 0 &&& AB v from rfl, Nat.testBit_and] at this
          simpa using this
        refine ⟨hx1408, ?_, ?_⟩
        · rw [hA 0 (by omega) x hx1408]
          exact hx'.1
        · rw [hA x hx1408 v hv2, hsym x hx1408 v hv2]
          exact hx'.2
    · obtain ⟨j, hj, hadj⟩ := hchain i hi hi0
      refine ⟨j, hj, ?_⟩
      rw [hA _ (hEl i hi) _ (hEl j (by omega))]
      exact hadj

theorem hypEnum_sets {UL : List Nat} {UP PP XP YP J : Nat} {xw yw : List Int}
    {HS ML : Nat → Nat} (H : Pts UL UP PP) (hTX : TR 693 (powG UL.toArray 3 xw) (fd 10 XP))
    (hTY : TR 693 (powG UL.toArray 2 yw) (fd 10 YP)) (hG : GenFacts XP YP)
    (hmemK : ∀ k < 4224, listsP (HS k) (ML k) = true)
    (hdistS : ∀ j < 4224, ∀ j' < 4224, HS j = HS j' → j = j') {o c : Nat} (ho : o < 3)
    (horbK : orbK UP XP YP HS ML J o c = true) :
    (hypEnumG UL.toArray xw yw c).1 = hypSetsA HS o := by
  obtain ⟨hroot, nn, hn0, hnend, hstep, hset⟩ := orbK_spec o ho hmemK horbK
  have hcY : TR 693 (compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw))
      (fun p => fd 10 (compP 693 10 YP YP) p) := by
    have h := compT_TR (n := 693) (by norm_num) hTY hTY
    refine ⟨h.1, fun i hi => ?_⟩
    show ap (compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)) i =
      fd 10 (compP 693 10 YP YP) i ∧ fd 10 (compP 693 10 YP YP) i < 693
    rw [fd_compP _ _ hi]
    exact h.2 i hi
  have hyp : OrbHyp (rootFlagsG UL.toArray c) #[powG UL.toArray 3 xw, powG UL.toArray 2 yw]
      #[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)]
      (fun l p => fd 10 (if l = 1 then YP else XP) p)
      (fun l p => fd 10 (if l = 1 then compP 693 10 YP YP else XP) p)
      (fun j => HS (1408 * o + j)) (fun t => fd 11 J t) nn := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, by simp [rootFlagsG], ?_, ?_, ?_, hn0, hnend, hstep, ?_⟩
    · intro l hl
      interval_cases l
      · exact hTX
      · exact hTY
    · intro l hl
      interval_cases l
      · exact hTX
      · exact hcY
    · intro l hl x hx
      interval_cases l
      · exact ⟨hG.xx x hx, hG.xx x hx⟩
      · show fd 10 (compP 693 10 YP YP) (fd 10 YP x) = x ∧
          fd 10 YP (fd 10 (compP 693 10 YP YP) x) = x
        rw [fd_compP _ _ (hG.ylt x hx), fd_compP _ _ hx]
        exact ⟨hG.yyy x hx, hG.yyy x hx⟩
    · intro p hp
      rw [rootFlagsG_eq H c, fl_get _ hp]
      show (rootK UP c).testBit p = (HS (1408 * o + 0)).testBit p
      rw [Nat.add_zero, hroot]
    · intro j hj
      exact (listsP_spec (hmemK _ (by omega))).1
    · intro j hj j' hj' hjj
      have := hdistS _ (by omega) _ (by omega) hjj
      omega
    · intro t ht
      exact (hset t ht)
  obtain ⟨par, lab, heq, -⟩ := orbitEnum_spec hyp
  unfold hypEnumG
  rw [heq]
  rfl

theorem eq_of_members {S S' : Nat} (hS : S < 2 ^ 693) (hS' : S' < 2 ^ 693)
    (h : ∀ q, q ∈ members (fl S) ↔ q ∈ members (fl S')) : S = S' := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < 693
  · have := h q
    rw [mem_members_fl, mem_members_fl] at this
    cases hb : S.testBit q <;> cases hb' : S'.testBit q <;> simp_all
  · have a1 : S.testBit q = false := by
      cases hb : S.testBit q
      · rfl
      · exact absurd (lt_of_testBit hS hb) hq
    have a2 : S'.testBit q = false := by
      cases hb : S'.testBit q
      · rfl
      · exact absurd (lt_of_testBit hS' hb) hq
    rw [a1, a2]

theorem famIndex_getD_key {H : Array Flags} {HS : Nat → Nat} (hHsz : H.size = 4224)
    (hH : ∀ j < 4224, H[j]! = fl (HS j)) (hHSlt : ∀ j < 4224, HS j < 2 ^ 693)
    (hdistS : ∀ j < 4224, ∀ j' < 4224, HS j = HS j' → j = j') {i : Nat} (hi : i < 4224) :
    (famIndex H).getD (packList (members (fl (HS i)))) 4224 = i := by
  have hinj : ∀ j < 4224, ∀ j' < 4224, packList (members H[j]!) = packList (members H[j']!) →
      j = j' := by
    intro j hj j' hj' h
    rw [hH j hj, hH j' hj'] at h
    have hmem : ∀ q, q ∈ members (fl (HS j)) ↔ q ∈ members (fl (HS j')) := by
      refine (packList_eq_iff (fun p hp => ?_) (fun p hp => ?_)).1 h
      · have := (mem_members_fl.1 hp).1
        omega
      · have := (mem_members_fl.1 hp).1
        omega
    exact hdistS j hj j' hj' (eq_of_members (hHSlt j hj) (hHSlt j' hj') hmem)
  have := famFold_getD H 4224 4224 hinj i (by omega)
  rw [hH i hi] at this
  rw [famIndex_eq, hHsz]
  exact this

theorem xiImgG_get {U : Array Nat} {H : Array Flags} {HS RW AB TP : Nat → Nat}
    (hHsz : H.size = 4224) (hH : ∀ j < 4224, H[j]! = fl (HS j))
    (hHSlt : ∀ j < 4224, HS j < 2 ^ 693)
    (hdistS : ∀ j < 4224, ∀ j' < 4224, HS j = HS j' → j = j')
    (hTR : ∀ f < 693, TR 693 ((tvTabsG U)[f]!) (fd 10 (TP f)))
    (hRC : ∀ k < 1408, RowCommon (HS k) (RW k) (AB k) k)
    (hRow : ∀ k < 1408, RowOK HS RW TP k) {k f : Nat} (hk : k < 1408) (hf : f < 693) :
    ((xiImgG U H (famIndex H))[k]!)[f]! = fd 11 (RW k) f := by
  have e1 : (xiImgG U H (famIndex H))[k]! = Array.ofFn (n := 693) fun f =>
      if (H[k]!)[f.val]! = true then k else
        findIn (famIndex H) 4224 (packImg (tvTabsG U)[f.val]! (members H[k]!)) := by
    unfold xiImgG
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rw [e1, getElem!_pos _ f (by simpa using hf), Array.getElem_ofFn]
  simp only []
  rw [hH k (by omega), fl_get _ hf]
  by_cases hb : (HS k).testBit f = true
  · rw [if_pos hb]
    exact ((hRC k hk).inS f hf hb).symm
  · have hb' : (HS k).testBit f = false := by simpa using hb
    rw [if_neg hb]
    obtain ⟨hi1, hi2, hi3⟩ := hRow k hk f hf hb'
    set i := fd 11 (RW k) f with hi
    have hkey : packImg ((tvTabsG U)[f]!) (members (fl (HS k))) =
        packList (members (fl (HS i))) := by
      rw [packImg_eq]
      refine (packList_eq_iff (fun p hp => ?_) (fun p hp => ?_)).2 (fun q => ?_)
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        have := (hTR f hf).2 p' (mem_members_fl.1 hp').1
        omega
      · have := (mem_members_fl.1 hp).1
        omega
      · rw [mem_map_ap (hTR f hf), mem_members_fl, ← hi3 q]
        constructor
        · intro h
          exact ⟨lt_of_testBit (hHSlt i (by omega)) h, h⟩
        · intro h
          exact h.2
    show (famIndex H).getD (packImg ((tvTabsG U)[f]!) (members (fl (HS k)))) 4224 = i
    rw [hkey]
    exact famIndex_getD_key hHsz hH hHSlt hdistS (by omega)

theorem xiImgOKG_of {U : Array Nat} {H : Array Flags} {Im Iv : Array (Array Nat)}
    {HS RW AB TP : Nat → Nat} (hH : ∀ j < 4224, H[j]! = fl (HS j))
    (hTR : ∀ f < 693, TR 693 ((tvTabsG U)[f]!) (fd 10 (TP f)))
    (hRC : ∀ k < 1408, RowCommon (HS k) (RW k) (AB k) k)
    (hRow : ∀ k < 1408, RowOK HS RW TP k)
    (hIm : ∀ k < 1408, ∀ f < 693, (Im[k]!)[f]! = fd 11 (RW k) f)
    (hIv : ∀ k < 1408, InvInv (H[k]!) (Im[k]!) 693 (Iv[k]!)) : xiImgOKG U H Im Iv = true := by
  unfold xiImgOKG
  rw [allIn_iff']
  intro k _ hk
  have hS : ∀ f < 693, (H[k]!)[f]! = (HS k).testBit f := fun f hf => by
    rw [hH k (by omega), fl_get _ hf]
  obtain ⟨hsz, h2, h3⟩ := hIv k hk
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_iff', Bool.or_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq]
  refine ⟨⟨hsz, fun f _ hf => ?_⟩, fun i _ hi => ?_⟩
  · by_cases hb : (H[k]!)[f]! = true
    · exact Or.inl hb
    · right
      have hb' : (H[k]!)[f]! = false := by simpa using hb
      have hbk : (HS k).testBit f = false := by rw [← hS f hf]; exact hb'
      obtain ⟨o1, o2⟩ := (hRC k hk).outS f hf hbk
      obtain ⟨_, _, hi3⟩ := hRow k hk f hf hbk
      rw [hIm k hk f hf]
      refine ⟨⟨⟨o1, o2⟩, ?_⟩, ?_⟩
      · have := h2 f hf hb'
        rw [hIm k hk f hf] at this
        exact this
      · rw [List.all_eq_true]
        intro p hp
        have hp' := mem_members.1 hp
        have hpk : (HS k).testBit p = true := by rw [← hS p hp'.1]; exact hp'.2
        have hq : fd 10 (TP f) p < 693 := ((hTR f hf).2 p hp'.1).2
        have hap : ap ((tvTabsG U)[f]!) p = fd 10 (TP f) p := ((hTR f hf).2 p hp'.1).1
        rw [hap, hH _ (by omega), fl_get _ hq]
        exact (hi3 _).2 ⟨p, hp'.1, hpk, rfl⟩
  · by_cases hv : (Iv[k]!)[i]! = 693
    · exact Or.inl hv
    · right
      have hnot : ¬ ∀ f < 693, (H[k]!)[f]! = false → (Im[k]!)[f]! ≠ i :=
        fun hall => hv (h3 i hi hall)
      have hex : ∃ f < 693, (H[k]!)[f]! = false ∧ (Im[k]!)[f]! = i := by
        by_contra hcon
        apply hnot
        intro f hf hSf hrow
        exact hcon ⟨f, hf, hSf, hrow⟩
      obtain ⟨f, hf, hSf, hrf⟩ := hex
      have hr := h2 f hf hSf
      rw [hrf] at hr
      rw [hr]
      exact ⟨⟨hf, by simpa using hSf⟩, hrf⟩

theorem xiAdj_get {Iv : Array (Array Nat)} {k i : Nat} (hk : k < 1408) (hi : i < 1408)
    (hsz : (Iv[k]!).size = 1408) :
    ((xiAdj Iv)[k]!)[i]! = ((Iv[k]!)[i]! != 693) := by
  unfold xiAdj
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  simp only []
  rw [getElem!_pos _ i (by simpa [hsz] using hi), Array.getElem_map,
    getElem!_pos _ i (by omega)]

theorem xiChecks_of {U : Array Nat} {P H : Array Flags} {HS RW AB TP PB MT : Nat → Nat}
    (hHsz : H.size = 4224) (hH : ∀ j < 4224, H[j]! = fl (HS j))
    (hHSlt : ∀ j < 4224, HS j < 2 ^ 693)
    (hdistS : ∀ j < 4224, ∀ j' < 4224, HS j = HS j' → j = j')
    (hTR : ∀ f < 693, TR 693 ((tvTabsG U)[f]!) (fd 10 (TP f)))
    (hRC : ∀ k < 1408, RowCommon (HS k) (RW k) (AB k) k)
    (hRow : ∀ k < 1408, RowOK HS RW TP k)
    (hsym : ∀ x < 1408, ∀ v < 1408, (AB x).testBit v = (AB v).testBit x)
    (hint1 : ∀ i, 1 ≤ i → i < 1408 → cnt (fun p => (HS 0).testBit p && (HS i).testBit p) 693 =
      if (AB 0).testBit i = true then 30 else 18)
    (hint2 : ∀ off, off = 0 ∨ off = 1408 ∨ off = 2816 → ∀ f < 693, (HS off).testBit f = true ∨
      cnt (fun p => (HS off).testBit p && (PB f).testBit p) 693 = 30)
    (hd : ∀ v, 0 < v → v < 1408 → (AB 0).testBit v = false →
      Nat.land (AB 0) (AB v) ≠ 0 ∧ ∀ w < 1408, 0 < w → (AB 0).testBit w = false →
        (AB v).testBit w = true → Nat.land (Nat.land (AB 0) (AB v)) (AB w) ≠ 0)
    (hm : ∀ v, 0 < v → v < 1408 → (AB 0).testBit v = false →
      fd 11 (MT v) 0 ≠ 0 ∧ (∀ x, (Nat.land (AB 0) (AB v)).testBit x = true ↔
        ∃ i < fd 11 (MT v) 0, fd 11 (MT v) (i + 1) = x) ∧
      ∀ i < fd 11 (MT v) 0, 0 < i → ∃ j < i,
        (AB (fd 11 (MT v) (i + 1))).testBit (fd 11 (MT v) (j + 1)) = true)
    (hP : ∀ x < 693, ∀ y < 693, (P[x]!)[y]! = bitK (PB x) y)
    (hr1 : rootFlagsG U 1 = fl (HS 0)) (hr2 : rootFlagsG U 2 = fl (HS 1408))
    (hr3 : rootFlagsG U 3 = fl (HS 2816)) : xiChecksG U P H = true := by
  have hAB : ∀ x < 1408, AB x < 2 ^ 1408 := fun x hx => (hRC x hx).ablt
  have hS : ∀ k < 4224, ∀ f < 693, (H[k]!)[f]! = (HS k).testBit f := fun k hk f hf => by
    rw [hH k hk, fl_get _ hf]
  unfold xiChecksG
  simp only []
  have hIm : ∀ k < 1408, ∀ f < 693, ((xiImgG U H (famIndex H))[k]!)[f]! = fd 11 (RW k) f :=
    fun k hk f hf => xiImgG_get hHsz hH hHSlt hdistS hTR hRC hRow hk hf
  have hIv : ∀ k < 1408, InvInv (H[k]!) ((xiImgG U H (famIndex H))[k]!) 693
      ((xiInv H (xiImgG U H (famIndex H)))[k]!) := by
    intro k hk
    rw [xiInv_getElem _ _ hk]
    apply xiInv_loop
    · intro f hf hSf
      rw [hIm k hk f hf]
      exact ((hRC k hk).outS f hf (by rw [← hS k (by omega) f hf]; exact hSf)).1
    · intro f hf f' hf' hSf hSf' heq
      rw [hIm k hk f hf, hIm k hk f' hf'] at heq
      exact (hRC k hk).inj f hf f' hf' (by rw [← hS k (by omega) f hf]; exact hSf)
        (by rw [← hS k (by omega) f' hf']; exact hSf') heq
  have hA : ∀ k < 1408, ∀ i < 1408, ((xiAdj (xiInv H (xiImgG U H (famIndex H))))[k]!)[i]! =
      (AB k).testBit i := by
    intro k hk i hi
    obtain ⟨hsz, h2, h3⟩ := hIv k hk
    rw [xiAdj_get hk hi hsz]
    by_cases hex : ∃ f < 693, (H[k]!)[f]! = false ∧
        ((xiImgG U H (famIndex H))[k]!)[f]! = i
    · obtain ⟨f, hf, hSf, hrf⟩ := hex
      have hr := h2 f hf hSf
      rw [hrf] at hr
      rw [hr]
      have hbk : (HS k).testBit f = false := by rw [← hS k (by omega) f hf]; exact hSf
      have : (AB k).testBit i = true := ((hRC k hk).ab i).2 ⟨f, hf, hbk, by
        rw [← hIm k hk f hf]; exact hrf⟩
      rw [this]
      simp [Nat.ne_of_lt hf]
    · have hall : ∀ f < 693, (H[k]!)[f]! = false →
          ((xiImgG U H (famIndex H))[k]!)[f]! ≠ i := fun f hf hSf h => hex ⟨f, hf, hSf, h⟩
      rw [h3 i hi hall]
      have : (AB k).testBit i = false := by
        cases hb : (AB k).testBit i
        · rfl
        · obtain ⟨f, hf, hbk, hfi⟩ := ((hRC k hk).ab i).1 hb
          exact absurd ⟨f, hf, by rw [hS k (by omega) f hf]; exact hbk, by
            rw [hIm k hk f hf]; exact hfi⟩ hex
      rw [this]
      simp
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨hHsz, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact xiImgOKG_of hH hTR hRC hRow hIm hIv
  · exact xiInterOK_of hH (fun i hi => hA 0 (by omega) i hi) hint1
  · rw [hr1]
    exact perpCountOK_of hP (fun f hf => hint2 0 (Or.inl rfl) f hf)
  · rw [hr2]
    exact perpCountOK_of hP (fun f hf => hint2 1408 (Or.inr (Or.inl rfl)) f hf)
  · rw [hr3]
    exact perpCountOK_of hP (fun f hf => hint2 2816 (Or.inr (Or.inr rfl)) f hf)
  · exact xiDiamOK_of hA hAB hsym hd
  · exact xiMuOK_of hA hAB hsym hm

theorem xi_sound_of_perp {U : Array Nat} {xw yw : List Int} {UL : List Nat}
    {UP PP XP YP J0 J1 J2 PA : Nat} {GP : List Nat} {PB TP HS ML RW AB MT : Nat → Nat}
    {SP : List Nat}
    (hU : U = UL.toArray) (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hg : ∀ k < 46, gensOK UL UP GP k 1 = true) (hxy : xyK GP xw yw = true)
    (hX : Nat.beq XP (powP 3 (wordG GP xw)) = true) (hY : Nat.beq YP (powP 2 (wordG GP yw)) = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true)
    (hmem : ∀ k < 12, memK HS ML (352 * k) 352 = true) (hdist : distinctK HS SP = true)
    (ho0 : orbK UP XP YP HS ML J0 0 1 = true) (ho1 : orbK UP XP YP HS ML J1 1 2 = true)
    (ho2 : orbK UP XP YP HS ML J2 2 3 = true)
    (hconj : ∀ k < 21, conjK TP XP YP (33 * k) 33 = true) (hpa : paK J0 PA = true)
    (hrow0 : rowsK TP HS ML RW AB 0 1 = true)
    (hrows : ∀ k < 11, rowsR HS RW AB XP YP J0 PA (128 * k) 128 = true)
    (hsym : ∀ k < 11, symK AB (128 * k) 128 = true) (hinter : interK HS AB PB = true)
    (hdiam : ∀ k < 11, diamK AB (128 * k) 128 = true)
    (hmu : ∀ k < 11, muK AB MT (128 * k) 128 = true)
    (hacyc : ∀ k, 0 < k → k < 1408 → at' 12 PA k / 2 < k)
    (hP : ∀ x < 693, ∀ y < 693, ((perpTabG U)[x]!)[y]! = bitK (PB x) y) :
    xiG U xw yw = true := by
  subst hU
  have H := Pts.of hp hpos
  obtain ⟨-, -, hgen⟩ := gensOK_spec hg
  have hmemK := memK_spec hmem
  have hHSlt : ∀ k < 4224, HS k < 2 ^ 693 := fun k hk => (listsP_spec (hmemK k hk)).1
  have hdistS := distinct_spec hdist
  obtain ⟨hTX, hTY, -, -, hxx, hyyy⟩ := xy_facts H hgen hxy hX hY
  have hG : GenFacts XP YP :=
    ⟨fun p hp => (hTX.2 p hp).2, fun p hp => (hTY.2 p hp).2, hxx, hyyy⟩
  have hTR : ∀ f < 693, TR 693 ((tvTabsG UL.toArray)[f]!) (fd 10 (TP f)) :=
    fun f hf => tvTabs_TR H htab hf
  have hCj : ConjFacts TP XP YP :=
    ⟨fun p hp q hq => (conjK_spec hconj hp).1 q hq, fun p hp q hq => (conjK_spec hconj hp).2 q hq,
      fun f hf p hp => ((hTR f hf).2 p hp).2⟩
  have hsets0 := hypEnum_sets (xw := xw) (yw := yw) H hTX hTY hG hmemK hdistS (by norm_num) ho0
  have hsets1 := hypEnum_sets (xw := xw) (yw := yw) H hTX hTY hG hmemK hdistS (by norm_num) ho1
  have hsets2 := hypEnum_sets (xw := xw) (yw := yw) H hTX hTY hG hmemK hdistS (by norm_num) ho2
  have hHeq : (hypEnumG UL.toArray xw yw 1).1 ++ (hypEnumG UL.toArray xw yw 2).1 ++
      (hypEnumG UL.toArray xw yw 3).1 = Array.ofFn (n := 4224) fun j => fl (HS j) := by
    rw [hsets0, hsets1, hsets2]
    exact concat_eq HS
  obtain ⟨hroot0, nn0, -, -, -, hset0⟩ := orbK_spec (c := 1) 0 (by norm_num) hmemK ho0
  obtain ⟨hroot1, -⟩ := orbK_spec (c := 2) 1 (by norm_num) hmemK ho1
  obtain ⟨hroot2, -⟩ := orbK_spec (c := 3) 2 (by norm_num) hmemK ho2
  have hJ : ∀ t < 2816, fd 11 J0 t < 1408 := fun t ht => (hset0 t ht).1
  have horb : ∀ t < 2816, ∀ q, (HS (fd 11 J0 t)).testBit q = true ↔
      ∃ p < 693, (HS (t / 2)).testBit p = true ∧
        fd 10 (if t % 2 = 1 then YP else XP) p = q := by
    intro t ht q
    have := (hset0 t ht).2 q
    simpa only [Nat.mul_zero, Nat.zero_add] using this
  have hRow : ∀ k < 1408, RowOK HS RW TP k :=
    rows_ok hG hCj hmemK hrow0 hrows hpa (fun k hk0 hk => by
      have := hacyc k hk0 hk
      rwa [at'_eq] at this) hJ horb
  have hRC : ∀ k < 1408, RowCommon (HS k) (RW k) (AB k) k := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      exact (rowsK_spec hrow0).1
    · exact (rowsR_spec hrows (Nat.pos_of_ne_zero hk0) hk).1
  have hAB : ∀ x < 1408, AB x < 2 ^ 1408 := fun x hx => (hRC x hx).ablt
  have hsymAB : ∀ x < 1408, ∀ v < 1408, (AB x).testBit v = (AB v).testBit x :=
    fun x hx v hv => symK_spec hsym hx hv
  obtain ⟨hint1, hint2⟩ := interK_spec hinter
  have hr1 : rootFlagsG UL.toArray 1 = fl (HS 0) := by
    rw [rootFlagsG_eq H 1]
    exact congrArg fl hroot0.symm
  have hr2 : rootFlagsG UL.toArray 2 = fl (HS 1408) := by
    rw [rootFlagsG_eq H 2]
    exact congrArg fl hroot1.symm
  have hr3 : rootFlagsG UL.toArray 3 = fl (HS 2816) := by
    rw [rootFlagsG_eq H 3]
    exact congrArg fl hroot2.symm
  unfold xiG
  rw [hHeq]
  exact xiChecks_of (by simp) (fun j hj => by
      rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]) hHSlt hdistS hTR hRC hRow
    hsymAB hint1 hint2 (fun v hv0 hv hn => diamK_spec hdiam hv0 hv hn)
    (fun v hv0 hv hn => muK_spec hAB hmu hv0 hv hn) hP hr1 hr2 hr3

theorem xi_sound_acyc {U : Array Nat} {xw yw : List Int} {UL : List Nat}
    {UP PP XP YP J0 J1 J2 PA : Nat} {GP : List Nat} {PB TP HS ML RW AB MT : Nat → Nat}
    {SP : List Nat}
    (hU : U = UL.toArray) (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hg : ∀ k < 46, gensOK UL UP GP k 1 = true) (hxy : xyK GP xw yw = true)
    (hX : Nat.beq XP (powP 3 (wordG GP xw)) = true) (hY : Nat.beq YP (powP 2 (wordG GP yw)) = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true)
    (hmem : ∀ k < 12, memK HS ML (352 * k) 352 = true) (hdist : distinctK HS SP = true)
    (ho0 : orbK UP XP YP HS ML J0 0 1 = true) (ho1 : orbK UP XP YP HS ML J1 1 2 = true)
    (ho2 : orbK UP XP YP HS ML J2 2 3 = true)
    (hconj : ∀ k < 21, conjK TP XP YP (33 * k) 33 = true) (hpa : paK J0 PA = true)
    (hrow0 : rowsK TP HS ML RW AB 0 1 = true)
    (hrows : ∀ k < 11, rowsR HS RW AB XP YP J0 PA (128 * k) 128 = true)
    (hsym : ∀ k < 11, symK AB (128 * k) 128 = true) (hinter : interK HS AB PB = true)
    (hdiam : ∀ k < 11, diamK AB (128 * k) 128 = true)
    (hmu : ∀ k < 11, muK AB MT (128 * k) 128 = true)
    (hacyc : ∀ k, 0 < k → k < 1408 → at' 12 PA k / 2 < k) :
    xiG U xw yw = true :=
  xi_sound_of_perp hU hp hpos hg hxy hX hY hperp htab hmem hdist ho0 ho1 ho2 hconj hpa hrow0 hrows
    hsym hinter hdiam hmu hacyc (perpTabG_get hU hp hpos hperp)

end CFSG.KC.Misc.Xi

end
