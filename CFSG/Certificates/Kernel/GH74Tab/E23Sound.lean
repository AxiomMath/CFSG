module

public import CFSG.Certificates.Kernel.GH74Tab.E1Sound
public import Certificates.Data.Kernel.GH74Tab.E23

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem bit_foldl_shl (L : List Nat) (m k : Nat) :
    bit (L.foldl (fun m i => m ||| 1 <<< i) m) k = (bit m k || decide (k ∈ L)) := by
  induction L generalizing m with
  | nil => simp
  | cons i L ih =>
    rw [List.foldl_cons, ih, bit_or, bit_shl1]
    simp [Bool.or_assoc, List.mem_cons]

theorem bit_mskL (L : List Nat) (k : Nat) : bit (mskL L) k = decide (k ∈ L) := by
  rw [mskL, bit_foldl_shl]
  simp [bit]

theorem map_val_finRange : (List.finRange 64).map Fin.val = r64 := by decide

theorem filter_map_val {f : Fin 64 → Bool} {p : Nat → Bool} (h : ∀ i : Fin 64, f i = p i.val) :
    ((List.finRange 64).filter f).map Fin.val = r64.filter p := by
  rw [← map_val_finRange, List.filter_map]
  congr 1
  exact List.filter_congr fun i _ => h i

theorem getD_eq_get {α : Type} (l : List α) (d : α) {k : Nat} (h : k < l.length) :
    l.getD k d = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (k : Nat) (d : α) :
    (l.map f).getD k (f d) = f (l.getD k d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> rfl

theorem f64_mul_eq_iff (D : Dat) (a b c d : Nat) :
    f64 (mul D a b) = f64 (mul D c d) ↔ mul D a b = mul D c d :=
  f64_eq_f64 (mul_lt D a b) (mul_lt D c d)

theorem and4_swap (a b c d : Bool) : (a && b && c && d) = (b && a && c && d) := by
  cases a <;> cases b <;> rfl

@[expose] def aP (D : Dat) (A i : Nat) : Bool := (eLK D A).all fun j => mul D i j == mul D j i

theorem aLK_eq (D : Dat) (A : Nat) : aLK D A = r64.filter (aP D A) := rfl

theorem mem_aLK {D : Dat} {A i : Nat} : i ∈ aLK D A ↔ i < 64 ∧ aP D A i = true := by
  rw [aLK_eq, r64, List.mem_filter, List.mem_range]

@[expose] def bP (D : Dat) (A i : Nat) : Bool :=
  bit D.IV i && bit (mskL (aLK D A)) i && bit (reachK D A 12 (1 <<< D.x0)) i &&
    !(eLK D A).contains i

theorem bLK_eq (D : Dat) (A : Nat) : bLK D A = r64.filter (bP D A) := rfl

theorem contains_eLK {D : Dat} {A i : Nat} (hi : i < 64) : (eLK D A).contains i = eP D A i := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, mem_eLK]
  exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩

theorem aP_eq_bit {D : Dat} {A i : Nat} (hi : i < 64) : aP D A i = bit (mskL (aLK D A)) i := by
  rw [bit_mskL, Bool.eq_iff_iff, decide_eq_true_iff, mem_aLK]
  exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

theorem labs4_mem : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    [a.val, b.val, c.val, d.val] ∈ labs4 := by decide

theorem mem_labs4 : ∀ l ∈ labs4, ∃ a b c d : Fin 4, l = [a.val, b.val, c.val, d.val] ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by decide

theorem quadT_eq (D : Dat) (B : List Nat) (it a b c d : Nat) : quadT D B it [a, b, c, d] =
    (cjK D it (B.getD a D.one) == B.getD b D.one && cjK D it (B.getD b D.one) == B.getD a D.one &&
      cjK D it (B.getD c D.one) == B.getD c D.one &&
      cjK D it (B.getD d D.one) == B.getD d D.one) := rfl

theorem quadY_eq (D : Dat) (B : List Nat) (iy a b c d : Nat) : quadY D B iy [a, b, c, d] =
    (cjK D iy (B.getD a D.one) == B.getD a D.one && cjK D iy (B.getD b D.one) == B.getD b D.one &&
      cjK D iy (B.getD c D.one) == B.getD d D.one &&
      cjK D iy (B.getD d D.one) == B.getD c D.one) := rfl

theorem aVecE3_eq {n : ℕ} [NeZero n] (a : Tbl) :
    (mkTab n).aVecE3 ((mkTab n).eVecE1 a) = (mkTab n).aVecE2 a := rfl

theorem bVec3_get {n : ℕ} [NeZero n] (A0 E0 X0 : Vector Bool 64) (k : Fin 4) :
    ((mkTab n).bVecE3 A0 E0 X0).get k = ((List.finRange 64).filter fun i =>
      A0.get i && (mkTab n).isInv i && X0.get i && !E0.get i).getD k.val (mkTab n).one := by
  unfold Tab.bVecE3
  dsimp only
  rw [vget_ofFn]

section Sound

variable {D : Dat} {n : ℕ} [NeZero n] (ht : transOK D n = true) (hd : dataOK D = true)
include ht hd

theorem isInv_mul_of (h0 : e1K0 D = true) (i j : Fin 64) (hi : (mkTab n).isInv i = true)
    (hj : (mkTab n).isInv j = true) (hc : (mkTab n).mulT i j = (mkTab n).mulT j i) (hne : i ≠ j) :
    (mkTab n).isInv ((mkTab n).mulT i j) = true := by
  unfold e1K0 at h0
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h0
  obtain ⟨⟨hF, -⟩, -⟩ := h0
  rw [isInv_eq ht hd] at hi hj ⊢
  rw [mulT_eq D ht, mulT_eq D ht, f64_eq_f64 (mul_lt D _ _) (mul_lt D _ _)] at hc
  rw [mulT_eq D ht, val_f64_mul]
  have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases hF i.val (mem_r64 i.2) j.val (mem_r64 j.2) with h | h
  · simp [hi, hj, hc, hne'] at h
  · exact h

theorem aVec_get (A : Nat) (i : Fin 64) :
    ((mkTab n).aVecE2 (tblOf A)).get i = aP D A i.val := by
  rw [Bool.eq_iff_iff, Tab.aVecE2_get, aP, List.all_eq_true]
  constructor
  · intro h j hj
    have hj64 := (mem_eLK.1 hj).1
    have := h (f64 j) ((eVec_iff_f64 ht hd A hj64).2 hj)
    rw [mulT_eq D ht, mulT_eq D ht, f64_mul_eq_iff, val_f64 hj64] at this
    exact beq_iff_eq.2 this
  · intro h j hj
    rw [eVec_iff ht hd] at hj
    rw [mulT_eq D ht, mulT_eq D ht, f64_mul_eq_iff]
    exact beq_iff_eq.1 (h j.val hj)

theorem aVec_bit (A : Nat) (i : Fin 64) :
    ((mkTab n).aVecE2 (tblOf A)).get i = bit (mskL (aLK D A)) i.val := by
  rw [aVec_get ht hd, aP_eq_bit i.2]

theorem aVec_mem (A : Nat) (i : Fin 64) :
    ((mkTab n).aVecE2 (tblOf A)).get i = true ↔ i.val ∈ aLK D A := by
  rw [aVec_get ht hd, mem_aLK]
  exact ⟨fun h => ⟨i.2, h⟩, fun h => h.2⟩

theorem bVec_get (A : Nat) (i : Fin 64) :
    ((mkTab n).bVecE2 (tblOf A)).get i = bP D A i.val := by
  unfold Tab.bVecE2
  dsimp only
  rw [vget_ofFn, isInv_eq ht hd, aVec_bit ht hd, reachX ht hd, eVec_get ht hd, bP,
    contains_eLK i.2]

theorem bList_map (A : Nat) : ((mkTab n).bListE2 (tblOf A)).map Fin.val = bLK D A := by
  unfold Tab.bListE2
  dsimp only
  rw [filter_map_val (bVec_get ht hd A), bLK_eq]

theorem prodB4_eq (bl : List (Fin 64)) (m : Nat) :
    (mkTab n).prodB4E2 (bl.getD 0 (mkTab n).one) (bl.getD 1 (mkTab n).one)
      (bl.getD 2 (mkTab n).one) (bl.getD 3 (mkTab n).one) m = f64 (prodK D (bl.map Fin.val) m) := by
  have hd1 := (dataOK_spec D hd).1
  have hg : ∀ k, (bl.getD k (mkTab n).one).val = (bl.map Fin.val).getD k D.one := by
    intro k
    rw [one_eq D ht, ← getD_map' Fin.val, val_f64 hd1]
  have hi : ∀ j k : Nat, (if j % 2 = 1 then bl.getD k (mkTab n).one else (mkTab n).one).val =
      (bif j % 2 == 1 then (bl.map Fin.val).getD k D.one else D.one) := by
    intro j k
    by_cases h : j % 2 = 1
    · rw [if_pos h, hg, beq_iff_eq.2 h, cond_true]
    · have h' : (j % 2 == 1) = false := by simpa using h
      rw [if_neg h, h', cond_false, one_eq D ht, val_f64 hd1]
  unfold Tab.prodB4E2
  rw [mulT_eq D ht, mulT_eq D ht, mulT_eq D ht, val_f64_mul, val_f64_mul, hi m 0, hi (m / 2) 1,
    hi (m / 4) 2, hi (m / 8) 3]
  rfl

theorem conj2_eq (A : Nat) {t0 r : Nat} (ht0 : t0 < 64) (hr : r < 64) :
    (mkTab n).conjE2 (tblOf A) (f64 t0) (f64 r) = f64 (mul D (mul D t0 (g6 A r)) (g6 D.I t0)) := by
  unfold Tab.conjE2
  rw [tblOf_get_eq, inv_eq D ht, mulT_eq D ht, mulT_eq D ht]
  simp only [val_f64_mul, val_f64_g6, val_f64 ht0, val_f64 hr]

theorem inKlein_eq {r1 r2 s : Nat} (h1 : r1 < 64) (h2 : r2 < 64) (hs : s < 64) :
    (mkTab n).inKleinE2 (f64 r1) (f64 r2) (f64 s) =
      (s == D.one || s == r1 || s == r2 || s == mul D r1 r2) := by
  have hd1 := (dataOK_spec D hd).1
  unfold Tab.inKleinE2
  rw [one_eq D ht, mulT_eq D ht, val_f64 h1, val_f64 h2, f64_beq_f64 hs hd1, f64_beq_f64 hs h1,
    f64_beq_f64 hs h2, f64_beq_f64 hs (mul_lt D _ _)]

theorem stable_eq (A : Nat) {t0 r1 r2 : Nat} (ht0 : t0 < 64) (h1 : r1 < 64) (h2 : r2 < 64) :
    (mkTab n).stableE2 (tblOf A) (f64 t0) (f64 r1) (f64 r2) = stabK D A t0 r1 r2 := by
  have hd1 := (dataOK_spec D hd).1
  unfold Tab.stableE2
  rw [one_eq D ht, mulT_eq D ht, val_f64 h1, val_f64 h2, conj2_eq ht hd A ht0 hd1,
    conj2_eq ht hd A ht0 h1, conj2_eq ht hd A ht0 h2, conj2_eq ht hd A ht0 (mul_lt D _ _),
    inKlein_eq ht hd h1 h2 (mul_lt D _ _), inKlein_eq ht hd h1 h2 (mul_lt D _ _),
    inKlein_eq ht hd h1 h2 (mul_lt D _ _), inKlein_eq ht hd h1 h2 (mul_lt D _ _)]
  rfl

theorem klein_eq (A : Nat) {r1 r2 : Nat} (h1 : r1 < 64) (h2 : r2 < 64) :
    (mkTab n).kleinOkE2 ((mkTab n).aVecE2 (tblOf A)) (f64 r1) (f64 r2) =
      kleinK D (mskL (aLK D A)) r1 r2 := by
  unfold Tab.kleinOkE2 kleinK
  simp only [isInv_eq ht hd, aVec_bit ht hd, mulT_eq D ht, inv_eq D ht, val_f64 h1, val_f64 h2,
    val_f64_mul, val_f64_g6, f64_mul_eq_iff]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    List.all_eq_true, r64, List.mem_range, and_assoc, or_assoc]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7⟩
    exact ⟨a1, a2, a3, a4, a5, a6, fun t ht' => a7 ⟨t, ht'⟩⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7⟩
    exact ⟨a1, a2, a3, a4, a5, a6, fun t => a7 t.val t.2⟩

theorem e2P1_of (A : Nat) (h0 : e1K0 D = true) (h1 : e2K1 D A = true) (u : Fin 64) :
    (mkTab n).e2P1 (tblOf A) u = true := by
  unfold e2K1 at h1
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨⟨hvI, hlen⟩, hcomm⟩, hsq⟩ := h1
  unfold Tab.e2P1
  dsimp only
  rw [decide_eq_true_iff]
  refine ⟨isInv_mul_of ht hd h0, ?_, ?_, ?_, ?_⟩
  · rw [vIE1_eq ht hd, isInv_eq ht hd, val_f64 (vIK_lt D A)]
    exact hvI
  · simp only [aVec_get ht hd]
    rw [card_filter_r64, ← aLK_eq]
    exact hlen
  · intro i j hi hj
    rw [aVec_mem ht hd] at hi hj
    rw [mulT_eq D ht, mulT_eq D ht, hcomm i.val hi j.val hj]
  · intro i hi
    rw [aVec_mem ht hd] at hi
    rw [mulT_eq D ht, one_eq D ht, hsq i.val hi]

theorem e2P2_of (A : Nat) (ws : List Nat) (h2 : e2K2 D A ws = true) (u : Fin 64) :
    (mkTab n).e2P2 (tblOf A) u = true := by
  unfold e2K2 at h2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h2
  obtain ⟨⟨hB, hws⟩, hz⟩ := h2
  have hbm := bList_map ht hd A
  unfold Tab.e2P2
  dsimp only
  rw [decide_eq_true_iff]
  refine ⟨?_, ?_⟩
  · have hl := congrArg List.length hbm
    rw [List.length_map] at hl
    rw [hl]
    exact hB
  · intro i hi
    rw [aVec_mem ht hd] at hi
    obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hi
    have hk' : k < ws.length := by omega
    have hkz : k < ((aLK D A).zip ws).length := by
      rw [List.length_zip]
      omega
    have hz' := hz _ (List.getElem_mem hkz)
    rw [List.getElem_zip] at hz'
    refine ⟨⟨ws[k], hz'.1⟩, ?_⟩
    rw [prodB4_eq ht hd, hbm]
    apply Fin.ext
    rw [val_f64 (by rw [← hz'.2, hki]; exact i.2), ← hz'.2, hki]

theorem e2P3_of (A : Nat) {u : Nat} (hu : u < 64) (ws : List (List Nat))
    (h3 : e2K3 D A u ws = true) : (mkTab n).e2P3 (tblOf A) (f64 u) = true := by
  have hd1 := (dataOK_spec D hd).1
  unfold e2K3 at h3
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h3
  obtain ⟨hhead, hw⟩ := h3
  unfold Tab.e2P3
  dsimp only
  rw [decide_eq_true_iff]
  intro t0 ht0
  have hmem : t0.val ∈ r64.filter fun t0 => mul D (mul D t0 (g6 A t0)) u == D.one := by
    rw [r64, List.mem_filter, List.mem_range]
    refine ⟨t0.2, ?_⟩
    rw [tblOf_get_eq, mulT_eq D ht, mulT_eq D ht, one_eq D ht, val_f64_mul, val_f64_g6,
      val_f64 hu, f64_eq_f64 (mul_lt D _ _) hd1] at ht0
    exact beq_iff_eq.2 ht0
  rw [hhead, List.mem_map] at hmem
  obtain ⟨w, hwm, hwh⟩ := hmem
  have hw' := hw w hwm
  rcases w with _ | ⟨t1, _ | ⟨r1, _ | ⟨r2, _ | ⟨x, rest⟩⟩⟩⟩
  · simp at hw'
  · simp at hw'
  · simp at hw'
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hw'
    obtain ⟨⟨⟨hr12, hr2⟩, hst⟩, hkl⟩ := hw'
    have ht1 : t1 = t0.val := hwh
    have hr1 : r1 < 64 := by omega
    have e0 : t0 = f64 t1 := by rw [ht1, f64_val]
    refine ⟨f64 r1, f64 r2, ?_, ?_, ?_⟩
    · rw [Fin.lt_def, val_f64 hr1, val_f64 hr2]
      exact hr12
    · rw [e0, stable_eq ht hd A (by rw [ht1]; exact t0.2) hr1 hr2]
      exact hst
    · rw [klein_eq ht hd A hr1 hr2]
      exact hkl
  · simp at hw'

theorem e2P4_of (A : Nat) (h4 : e2K4 D (zLK D) A = true) (u : Fin 64) :
    (mkTab n).e2P4 (tblOf A) u = true := by
  unfold e2K4 at h4
  rw [List.all_eq_true] at h4
  unfold Tab.e2P4
  dsimp only
  rw [decide_eq_true_iff]
  intro s hc hfix hinv
  have hz : s.val ∈ zLK D := by
    unfold zLK
    rw [List.mem_filter]
    refine ⟨mem_r64 s.2, ?_⟩
    rw [List.all_eq_true]
    intro t ht'
    have ht64 : t < 64 := List.mem_range.1 ht'
    have := hc (f64 t)
    rw [mulT_eq D ht, mulT_eq D ht, f64_mul_eq_iff, val_f64 ht64] at this
    exact beq_iff_eq.2 this
  have h := h4 s.val hz
  have hfix' : g6 A s.val = s.val := by
    have := congrArg Fin.val hfix
    rwa [tblOf_get_eq, val_f64_g6] at this
  rw [isInv_eq ht hd] at hinv
  rw [hfix', hinv, beq_self_eq_true, Bool.and_true, Bool.not_true, Bool.false_or,
    beq_iff_eq] at h
  rw [vIE1_eq ht hd]
  exact Fin.ext (by rw [val_f64 (vIK_lt D A)]; exact h)

theorem e2OK_sound {L : List (Nat × Nat)} {W2 : List (List Nat)} {W3 : List (List (List Nat))}
    (h : e2OK D L W2 W3 = true) {p : Nat × Nat} (hp : p ∈ L) (hu : p.2 < 64) :
    (mkTab n).e2P1 (tblOf p.1) (f64 p.2) = true ∧ (mkTab n).e2P2 (tblOf p.1) (f64 p.2) = true ∧
      (mkTab n).e2P3 (tblOf p.1) (f64 p.2) = true ∧
      (mkTab n).e2P4 (tblOf p.1) (f64 p.2) = true := by
  unfold e2OK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h0, hl2⟩, hl3⟩, hall⟩ := h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hkz : k < (L.zip (W2.zip W3)).length := by
    simp only [List.length_zip]
    omega
  have hq := hall _ (List.getElem_mem hkz)
  rw [List.getElem_zip, List.getElem_zip] at hq
  obtain ⟨⟨⟨q1, q2⟩, q3⟩, q4⟩ := hq
  exact ⟨e2P1_of ht hd _ h0 q1 _, e2P2_of ht hd _ _ q2 _, e2P3_of ht hd _ hu _ q3,
    e2P4_of ht hd _ q4 _⟩

theorem conj3_val (i x : Fin 64) : ((mkTab n).conjE3 i x).val = cjK D i.val x.val := by
  unfold Tab.conjE3 cjK
  rw [mulT_eq D ht, mulT_eq D ht, inv_eq D ht]
  simp only [val_f64_mul, val_f64_g6]

theorem bList3_map (A : Nat) :
    ((List.finRange 64).filter fun i => ((mkTab n).aVecE2 (tblOf A)).get i && (mkTab n).isInv i &&
      ((mkTab n).reach (tblOf A) (mkTab n).x0i).get i &&
      !((mkTab n).eVecE1 (tblOf A)).get i).map Fin.val = bLK D A := by
  rw [bLK_eq]
  apply filter_map_val
  intro i
  rw [isInv_eq ht hd, aVec_bit ht hd, reachX ht hd, eVec_get ht hd, bP, contains_eLK i.2,
    and4_swap]

end Sound

theorem wOK7_spec {wa wc : Nat} (h : wOK7 wa wc = true) (i : Fin 64) :
    (mkTab 7).wActE3.get i = g6 wa i.val ∧ (mkTab 7).wCommE3.get i = bit wc i.val := by
  simp only [wOK7, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_finRange,
    true_implies] at h
  exact h i

section Sound7

variable {D : Dat} (ht : transOK D 7 = true) (hd : dataOK D = true)
include ht hd

theorem e3P_of (A : Nat) {wa wc : Nat} (h0 : e1K0 D = true) (hw : wOK7 wa wc = true)
    (w : List Nat) (h3 : e3K D wa wc A w = true) (u : Fin 64) :
    (mkTab 7).e3P (mkTab 7).wActE3 (mkTab 7).wCommE3 (tblOf A) u = true := by
  have hd1 := (dataOK_spec D hd).1
  unfold e3K at h3
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h3
  obtain ⟨⟨⟨⟨⟨hvI, hwE⟩, hwA⟩, hBl⟩, hU⟩, hX⟩ := h3
  have hLm := bList3_map ht hd A
  unfold Tab.e3P
  dsimp only
  rw [aVecE3_eq]
  set B := (mkTab 7).bVecE3 ((mkTab 7).aVecE2 (tblOf A)) ((mkTab 7).eVecE1 (tblOf A))
    ((mkTab 7).reach (tblOf A) (mkTab 7).x0i) with hBdef
  set L' := (List.finRange 64).filter fun i => ((mkTab 7).aVecE2 (tblOf A)).get i &&
    (mkTab 7).isInv i && ((mkTab 7).reach (tblOf A) (mkTab 7).x0i).get i &&
    !((mkTab 7).eVecE1 (tblOf A)).get i with hL'
  have hlen : L'.length = 4 := by
    have := congrArg List.length hLm
    rw [List.length_map] at this
    rw [this]
    exact hBl
  have hBk : ∀ k : Fin 4, B.get k = L'[k.val]'(by rw [hlen]; exact k.2) := by
    intro k
    rw [hBdef, bVec3_get, ← hL', getD_eq_get _ _ (by rw [hlen]; exact k.2)]
  have hBval : ∀ k : Fin 4, (B.get k).val = (bLK D A).getD k.val D.one := by
    intro k
    rw [hBdef, bVec3_get, ← getD_map' Fin.val, ← hL', hLm, one_eq D ht, val_f64 hd1]
  have hcv : ∀ (t : Fin 64) (k k' : Fin 4), (mkTab 7).conjE3 t (B.get k) = B.get k' →
      cjK D t.val ((bLK D A).getD k.val D.one) = (bLK D A).getD k'.val D.one := by
    intro t k k' h
    have := congrArg Fin.val h
    rwa [conj3_val ht hd, hBval, hBval] at this
  have hcv' : ∀ (t : Nat) (_ : t < 64) (k k' : Fin 4),
      cjK D t ((bLK D A).getD k.val D.one) = (bLK D A).getD k'.val D.one →
      (mkTab 7).conjE3 (f64 t) (B.get k) = B.get k' := by
    intro t htl k k' h
    apply Fin.ext
    rw [conj3_val ht hd, val_f64 htl, hBval, hBval]
    exact h
  have hIL : ∀ i : Fin 64, (mkTab 7).isInv i = true → ((mkTab 7).aVecE2 (tblOf A)).get i = false →
      i.val ∈ itLK D (mskL (aLK D A)) := by
    intro i hI hA
    unfold itLK
    rw [List.mem_filter]
    refine ⟨mem_r64 i.2, ?_⟩
    rw [isInv_eq ht hd] at hI
    rw [aVec_bit ht hd] at hA
    rw [hI, hA]
    rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨isInv_mul_of ht hd h0, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [vIE1_eq ht hd, isInv_eq ht hd, val_f64 (vIK_lt D A)]
    exact hvI
  · intro j hj
    rw [eVec_iff ht hd] at hj
    rw [(wOK7_spec hw j).2]
    exact hwE j.val hj
  · intro i hA hE
    have h := hwA i.val (mem_r64 i.2)
    rw [aVec_bit ht hd] at hA
    rw [eVec_get ht hd] at hE
    rw [hA, contains_eLK i.2, hE] at h
    simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or, beq_iff_eq] at h
    rw [(wOK7_spec hw i).1]
    exact h
  · intro k
    have hm := List.getElem_mem (l := L') (n := k.val) (by rw [hlen]; exact k.2)
    rw [← hBk k, hL', List.mem_filter] at hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
    obtain ⟨-, ⟨⟨hA, hI⟩, hX0⟩, hE⟩ := hm
    exact ⟨hA, hI, hX0, hE⟩
  · intro k k' h
    rw [hBk, hBk] at h
    have hnd : L'.Nodup := (List.nodup_finRange 64).filter _
    exact Fin.ext ((hnd.getElem_inj_iff).1 h)
  · intro i hA hI hX0 hE
    have hm : i ∈ L' := by
      rw [hL', List.mem_filter]
      exact ⟨List.mem_finRange i, by simp [hA, hI, hX0, hE]⟩
    obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hm
    refine ⟨⟨j, by rw [← hlen]; exact hj⟩, ?_⟩
    rw [hBk]
    exact hji.symm
  · intro it iy hp p1 p2 q1 q2 hq
    obtain ⟨hIt, hIy, hAt, hAy, hc⟩ := (mkTab 7).pairE3_elim _ hp
    obtain ⟨d1, d2, d3, d4, d5, d6, c1, c2, c3, c4, c5, c6, c7, c8⟩ := (mkTab 7).quadE3_elim B hq
    rw [(wOK7_spec hw it).1]
    by_contra hne
    have h := hU it.val (hIL it hIt hAt)
    have hne' : (g6 wa it.val == 0) = false := by simpa using hne
    rw [hne', Bool.false_or, List.all_eq_true] at h
    have hl := h _ (labs4_mem p1 p2 q1 q2 d1 d2 d3 d4 d5 d6)
    rw [quadT_eq, hcv _ _ _ c1, hcv _ _ _ c2, hcv _ _ _ c3, hcv _ _ _ c4] at hl
    simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
      List.all_eq_true] at hl
    have h2 := hl iy.val (hIL iy hIy hAy)
    have hc' : mul D it.val iy.val = mul D iy.val it.val := by
      rw [mulT_eq D ht, mulT_eq D ht, f64_mul_eq_iff] at hc
      exact hc
    rw [quadY_eq, hcv _ _ _ c5, hcv _ _ _ c6, hcv _ _ _ c7, hcv _ _ _ c8, hc'] at h2
    simp at h2
  · rcases w with _ | ⟨it, _ | ⟨iy, _ | ⟨p1, _ | ⟨p2, _ | ⟨q1, _ | ⟨q2, _ | ⟨x, rest⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hX; done)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
      List.contains_iff_mem] at hX
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hit, hiy⟩, hIt⟩, hIy⟩, hAt⟩, hAy⟩, hc⟩, hlab⟩, hqT⟩, hqY⟩ := hX
    obtain ⟨a, b, c, d, heq, d1, d2, d3, d4, d5, d6⟩ := mem_labs4 _ hlab
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    rw [quadT_eq] at hqT
    rw [quadY_eq] at hqY
    simp only [Bool.and_eq_true, beq_iff_eq] at hqT hqY
    obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := hqT
    obtain ⟨⟨⟨y1, y2⟩, y3⟩, y4⟩ := hqY
    refine ⟨f64 it, f64 iy, ?_, a, b, c, d, ?_⟩
    · refine (mkTab 7).pairE3_intro _ ?_ ?_ ?_ ?_ ?_
      · rw [isInv_eq ht hd, val_f64 hit]
        exact hIt
      · rw [isInv_eq ht hd, val_f64 hiy]
        exact hIy
      · rw [aVec_bit ht hd, val_f64 hit]
        exact hAt
      · rw [aVec_bit ht hd, val_f64 hiy]
        exact hAy
      · rw [mulT_eq D ht, mulT_eq D ht, f64_mul_eq_iff, val_f64 hit, val_f64 hiy]
        exact hc
    · exact (mkTab 7).quadE3_intro B d1 d2 d3 d4 d5 d6 (hcv' _ hit _ _ t1) (hcv' _ hit _ _ t2)
        (hcv' _ hit _ _ t3) (hcv' _ hit _ _ t4) (hcv' _ hiy _ _ y1) (hcv' _ hiy _ _ y2)
        (hcv' _ hiy _ _ y3) (hcv' _ hiy _ _ y4)

theorem e3OK_sound {L : List (Nat × Nat)} {W4 : List (List Nat)} {wa wc : Nat}
    (h : e3OK D L W4 wa wc = true) {p : Nat × Nat} (hp : p ∈ L) :
    (mkTab 7).e3P (mkTab 7).wActE3 (mkTab 7).wCommE3 (tblOf p.1) (f64 p.2) = true := by
  unfold e3OK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h0, hw⟩, hl⟩, hall⟩ := h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hkz : k < (L.zip W4).length := by
    rw [List.length_zip]
    omega
  have hq := hall _ (List.getElem_mem hkz)
  rw [List.getElem_zip] at hq
  exact e3P_of ht hd _ h0 hw _ hq _

end Sound7

end CFSG.KC.GH74Tab

end
