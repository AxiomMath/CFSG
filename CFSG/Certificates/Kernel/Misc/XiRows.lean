module

public import CFSG.Certificates.Kernel.Misc.XiBits
public import CFSG.Certificates.Kernel.J4Q.BfsOrder
public import CFSG.Certificates.Kernel.Misc.LinesPerp
public import Certificates.Data.CFSGNative.Fischer.Xi22

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Xi

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46 CFSG.KC.Misc.Lines
  CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.J4Q.BfsOrder

theorem memK_spec {HS ML : Nat → Nat} (h : ∀ k < 12, memK HS ML (352 * k) 352 = true) :
    ∀ k < 4224, listsP (HS k) (ML k) = true := by
  intro k hk
  have h1 := h (k / 352) (by omega)
  unfold memK at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (k % 352) (by omega)
  have e : 352 * (k / 352) + k % 352 = k := by omega
  have hb : Nat.blt k 4224 = true := Nat.blt_eq.mpr hk
  simp only [Nat.add_eq, e, letB_eq, impB_eq, hb, Bool.not_true, Bool.false_or] at h2
  exact h2

theorem list_or_testBit (L : List Nat) (j : Nat) :
    (List.rec (motive := fun _ => Nat) 0 (fun k _ ih => Nat.lor ih (Nat.shiftLeft 1 k)) L).testBit j
      = true ↔ j ∈ L := by
  induction L with
  | nil => simp
  | cons k t ih =>
    show (Nat.lor (List.rec (motive := fun _ => Nat) 0
      (fun k _ ih => Nat.lor ih (Nat.shiftLeft 1 k)) t) (Nat.shiftLeft 1 k)).testBit j = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, ih,
      show Nat.shiftLeft 1 k = 2 ^ k from Nat.one_shiftLeft _, Nat.testBit_two_pow,
      decide_eq_true_iff, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

theorem distinct_chain (HS : Nat → Nat) (L : List Nat) : ∀ prev : Nat,
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun k _ ih prev => letB (HS k) fun s => andB (Nat.blt prev (Nat.succ s)) (ih (Nat.succ s)))
      L prev) = true → (L.map HS).Pairwise (· < ·) ∧ ∀ k ∈ L, prev ≤ HS k := by
  induction L with
  | nil => intro prev _; exact ⟨List.Pairwise.nil, fun k hk => absurd hk (by simp)⟩
  | cons k t ih =>
    intro prev h
    have h0 : letB (HS k) (fun s => andB (Nat.blt prev (Nat.succ s)) (List.rec
        (motive := fun _ => Nat → Bool) (fun _ => true) (fun k _ ih prev => letB (HS k) fun s =>
          andB (Nat.blt prev (Nat.succ s)) (ih (Nat.succ s))) t (Nat.succ s))) = true := h
    rw [letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq] at h0
    obtain ⟨hp, hrest⟩ := ih (Nat.succ (HS k)) h0.2
    refine ⟨?_, fun k' hk' => ?_⟩
    · rw [List.map_cons]
      refine List.Pairwise.cons (fun b hb => ?_) hp
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hb
      have := hrest k' hk'
      omega
    · rcases List.mem_cons.1 hk' with rfl | hk'
      · have := h0.1
        omega
      · have := hrest k' hk'
        omega

theorem testBit_pow_sub_one' (n j : Nat) :
    (Nat.sub (Nat.shiftLeft 1 n) 1).testBit j = decide (j < n) := by
  show ((1 <<< n) - 1).testBit j = _
  rw [Nat.one_shiftLeft]
  exact Nat.testBit_two_pow_sub_one n j

theorem distinct_spec {HS : Nat → Nat} {SP : List Nat} (h : distinctK HS SP = true) :
    ∀ j < 4224, ∀ j' < 4224, HS j = HS j' → j = j' := by
  unfold distinctK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨-, h2, h3⟩ := h
  have hmem : ∀ j < 4224, j ∈ SP := by
    intro j hj
    rw [← list_or_testBit, h2, testBit_pow_sub_one']
    simpa using hj
  have hpw := (distinct_chain HS SP 0 h3).1
  have hnd : (SP.map HS).Nodup := hpw.nodup
  intro j hj j' hj' he
  exact List.inj_on_of_nodup_map hnd (hmem j hj) (hmem j' hj') he

structure RowCommon (S R ABk k : Nat) : Prop where
  lt : R < 2 ^ (11 * 693)
  inS : ∀ f < 693, S.testBit f = true → fd 11 R f = k
  outS : ∀ f < 693, S.testBit f = false → fd 11 R f < 1408 ∧ fd 11 R f ≠ k
  inj : ∀ f < 693, ∀ f' < 693, S.testBit f = false → S.testBit f' = false →
    fd 11 R f = fd 11 R f' → f = f'
  ab : ∀ j, ABk.testBit j = true ↔ ∃ f < 693, S.testBit f = false ∧ fd 11 R f = j
  ablt : ABk < 2 ^ 1408

theorem rowSum_aux (S R n : Nat) : Nat.rec (motive := fun _ => Nat) 0
    (fun f acc => Bool.rec (motive := fun _ => Nat)
      (Nat.add acc (Nat.shiftLeft 1 (at' 11 R f))) acc (bitK S f)) n =
      addS (fun f => S.testBit f) (fun f => fd 11 R f) n := by
  unfold addS
  refine rec_congr (fun i acc => ?_) n
  simp only [nIf_eq, bitK_eq_testBit, at'_eq]

theorem rowLor_aux (S R n : Nat) : Nat.rec (motive := fun _ => Nat) 0
    (fun f acc => Bool.rec (motive := fun _ => Nat)
      (Nat.lor acc (Nat.shiftLeft 1 (at' 11 R f))) acc (bitK S f)) n =
      lorS (fun f => S.testBit f) (fun f => fd 11 R f) n := by
  unfold lorS
  refine rec_congr (fun i acc => ?_) n
  simp only [nIf_eq, bitK_eq_testBit, at'_eq]

theorem rowTail_spec {S R ABk : Nat}
    (h1 : Nat.beq (Nat.rec (motive := fun _ => Nat) 0 (fun f acc =>
        Bool.rec (motive := fun _ => Nat) (Nat.add acc (Nat.shiftLeft 1 (at' 11 R f))) acc
          (bitK S f)) 693) ABk = true)
    (h2 : Nat.beq (Nat.rec (motive := fun _ => Nat) 0 (fun f acc =>
        Bool.rec (motive := fun _ => Nat) (Nat.lor acc (Nat.shiftLeft 1 (at' 11 R f))) acc
          (bitK S f)) 693) (Nat.rec (motive := fun _ => Nat) 0 (fun f acc => Bool.rec
            (motive := fun _ => Nat) (Nat.add acc (Nat.shiftLeft 1 (at' 11 R f))) acc
              (bitK S f)) 693) = true) :
    ABk = addS (fun f => S.testBit f) (fun f => fd 11 R f) 693 ∧
      lorS (fun f => S.testBit f) (fun f => fd 11 R f) 693 =
        addS (fun f => S.testBit f) (fun f => fd 11 R f) 693 := by
  rw [Nat.beq_eq, rowSum_aux] at h1
  rw [Nat.beq_eq, rowSum_aux, rowLor_aux] at h2
  exact ⟨h1.symm, h2⟩

theorem rowCommon_of {S R ABk k : Nat} (hR : R < 2 ^ (11 * 693))
    (hf : ∀ f < 693, S.testBit f = true → fd 11 R f = k)
    (hf2 : ∀ f < 693, S.testBit f = false → fd 11 R f < 1408 ∧ fd 11 R f ≠ k)
    (htail : ABk = addS (fun f => S.testBit f) (fun f => fd 11 R f) 693 ∧
      lorS (fun f => S.testBit f) (fun f => fd 11 R f) 693 =
        addS (fun f => S.testBit f) (fun f => fd 11 R f) 693) : RowCommon S R ABk k := by
  have hab : ∀ j, ABk.testBit j = true ↔ ∃ f < 693, S.testBit f = false ∧ fd 11 R f = j := by
    intro j
    rw [htail.1, ← htail.2, lorS, testBit_fold_or_skip]
  refine ⟨hR, hf, hf2, ?_, hab, ?_⟩
  · intro f hf1 f' hf1' h1 h2 h3
    exact ((lorS_le_addS (fun f => S.testBit f) (fun f => fd 11 R f) 693).2 htail.2) f hf1 f' hf1'
      (by simpa using h1) (by simpa using h2) h3
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    cases hb : ABk.testBit i
    · rfl
    · obtain ⟨f, hf1, hf2', hfi⟩ := (hab i).1 hb
      have := (hf2 f hf1 hf2').1
      omega

theorem rowsK_spec {TP HS ML RW AB : Nat → Nat} (h : rowsK TP HS ML RW AB 0 1 = true) :
    RowCommon (HS 0) (RW 0) (AB 0) 0 ∧
    ∀ f < 693, (HS 0).testBit f = false → HS (fd 11 (RW 0) f) = imgP (TP f) (ML 0) := by
  unfold rowsK at h
  rw [allN_lqt_iff] at h
  have h0 := h 0 (by omega)
  have hb : Nat.blt 0 1408 = true := rfl
  have e0 : Nat.add 0 0 = 0 := rfl
  simp only [e0, letB_eq, impB_eq, hb, Bool.not_true, Bool.false_or, andB_eq,
    Bool.and_eq_true, allN_lqt_iff] at h0
  obtain ⟨h1, h2, h3, h4⟩ := h0
  have hR : RW 0 < 2 ^ (11 * 693) := by
    have := Nat.blt_eq.mp h1
    have e : Nat.shiftLeft 1 (Nat.mul 11 693) = 2 ^ (11 * 693) := Nat.one_shiftLeft _
    rwa [e] at this
  have hper : ∀ f < 693, ((HS 0).testBit f = true → fd 11 (RW 0) f = 0) ∧
      ((HS 0).testBit f = false → fd 11 (RW 0) f < 1408 ∧ fd 11 (RW 0) f ≠ 0 ∧
        HS (fd 11 (RW 0) f) = imgP (TP f) (ML 0)) := by
    intro f hf
    have h5 := h2 f hf
    cases hbf : (HS 0).testBit f
    · rw [bitK_eq_testBit, hbf] at h5
      have h6 : (Nat.blt (at' 11 (RW 0) f) 1408 && (notB (Nat.beq (at' 11 (RW 0) f) 0) &&
          Nat.beq (HS (at' 11 (RW 0) f)) (imgP (TP f) (ML 0)))) = true := h5
      simp only [Bool.and_eq_true, Nat.blt_eq, notB_eq, Bool.not_eq_true', Nat.beq_eq, at'_eq,
        nat_beq_eq_false_iff] at h6
      exact ⟨by simp, fun _ => h6⟩
    · rw [bitK_eq_testBit, hbf] at h5
      have h6 : Nat.beq (at' 11 (RW 0) f) 0 = true := h5
      rw [Nat.beq_eq, at'_eq] at h6
      exact ⟨fun _ => h6, fun h => absurd h (by simp)⟩
  have htail := rowTail_spec (S := HS 0) (R := RW 0) (ABk := AB 0) h3 h4
  refine ⟨rowCommon_of hR (fun f hf hb => (hper f hf).1 hb) (fun f hf hb => ?_) htail,
    fun f hf hb => ((hper f hf).2 hb).2.2⟩
  have := (hper f hf).2 hb
  exact ⟨this.1, this.2.1⟩

theorem rowsR_spec {HS RW AB : Nat → Nat} {X Y J PA : Nat}
    (h : ∀ k < 11, rowsR HS RW AB X Y J PA (128 * k) 128 = true) {k : Nat} (hk0 : 0 < k)
    (hk : k < 1408) :
    RowCommon (HS k) (RW k) (AB k) k ∧ ∀ f < 693, (HS k).testBit f = false →
      fd 11 (RW k) f = fd 11 J (2 * fd 11 (RW (fd 12 PA k / 2))
        (fd 10 (if fd 12 PA k % 2 = 1 then compP 693 10 Y Y else X) f) + fd 12 PA k % 2) := by
  have h1 := h (k / 128) (by omega)
  unfold rowsR at h1
  simp only [letB_eq] at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (k % 128) (by omega)
  have e : Nat.add (128 * (k / 128)) (k % 128) = k := by rw [Nat.add_eq]; omega
  have hb1 : Nat.blt 0 k = true := Nat.blt_eq.mpr hk0
  have hb2 : Nat.blt k 1408 = true := Nat.blt_eq.mpr hk
  simp only [e, letB_eq, impB_eq, andB_eq, hb1, hb2, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, allN_lqt_iff] at h2
  obtain ⟨h3, h4, h5, h6⟩ := h2
  have hR : RW k < 2 ^ (11 * 693) := by
    have := Nat.blt_eq.mp h3
    have e : Nat.shiftLeft 1 (Nat.mul 11 693) = 2 ^ (11 * 693) := Nat.one_shiftLeft _
    rwa [e] at this
  have hper : ∀ f < 693, ((HS k).testBit f = true → fd 11 (RW k) f = k) ∧
      ((HS k).testBit f = false → fd 11 (RW k) f < 1408 ∧ fd 11 (RW k) f ≠ k ∧
        fd 11 (RW k) f = fd 11 J (2 * fd 11 (RW (fd 12 PA k / 2))
          (fd 10 (if fd 12 PA k % 2 = 1 then compP 693 10 Y Y else X) f) + fd 12 PA k % 2)) := by
    intro f hf
    have h7 := h4 f hf
    cases hbf : (HS k).testBit f
    · rw [bitK_eq_testBit, hbf] at h7
      have h8 : (Nat.blt (at' 11 (RW k) f) 1408 && (notB (Nat.beq (at' 11 (RW k) f) k) &&
          Nat.beq (at' 11 (RW k) f) (at' 11 J (Nat.add (Nat.mul 2 (at' 11 (RW (Nat.div
            (at' 12 PA k) 2)) (at' 10 (Bool.rec (motive := fun _ => Nat) X (compP 693 10 Y Y)
              (Nat.beq (Nat.mod (at' 12 PA k) 2) 1)) f))) (Nat.mod (at' 12 PA k) 2))))) = true :=
        h7
      simp only [Bool.and_eq_true, Nat.blt_eq, notB_eq, Bool.not_eq_true', Nat.beq_eq, at'_eq,
        nat_beq_eq_false_iff, nIf_eq] at h8
      refine ⟨by simp, fun _ => ?_⟩
      exact ⟨h8.1, h8.2.1, h8.2.2⟩
    · rw [bitK_eq_testBit, hbf] at h7
      have h8 : Nat.beq (at' 11 (RW k) f) k = true := h7
      rw [Nat.beq_eq, at'_eq] at h8
      exact ⟨fun _ => h8, fun h => absurd h (by simp)⟩
  have htail := rowTail_spec (S := HS k) (R := RW k) (ABk := AB k) h5 h6
  refine ⟨rowCommon_of hR (fun f hf hb => (hper f hf).1 hb) (fun f hf hb => ?_) htail,
    fun f hf hb => ((hper f hf).2 hb).2.2⟩
  have := (hper f hf).2 hb
  exact ⟨this.1, this.2.1⟩

theorem paK_spec {J PA : Nat} (h : paK J PA = true) {k : Nat} (hk0 : 0 < k) (hk : k < 1408) :
    fd 12 PA k < 2816 ∧ fd 11 J (fd 12 PA k) = k := by
  unfold paK at h
  rw [allN_lqt_iff] at h
  have h1 := h (k - 1) (by omega)
  have e : Nat.succ (k - 1) = k := by omega
  simp only [e, letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, at'_eq] at h1
  exact h1

theorem symK_spec {AB : Nat → Nat} (h : ∀ k < 11, symK AB (128 * k) 128 = true) {x v : Nat}
    (hx : x < 1408) (hv : v < 1408) : (AB x).testBit v = (AB v).testBit x := by
  have h1 := h (x / 128) (by omega)
  unfold symK at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (x % 128) (by omega)
  have e : Nat.add (128 * (x / 128)) (x % 128) = x := by rw [Nat.add_eq]; omega
  have hb : Nat.blt x 1408 = true := Nat.blt_eq.mpr hx
  simp only [e, letB_eq, impB_eq, hb, Bool.not_true, Bool.false_or, allN_lqt_iff] at h2
  have h3 := h2 v hv
  rw [bitK_eq_testBit, bitK_eq_testBit] at h3
  cases hb1 : (AB x).testBit v <;> cases hb2 : (AB v).testBit x <;>
    simp_all [bIf_eq, notB_eq]

theorem popK_land (a b : Nat) :
    popK (Nat.land a b) = cnt (fun p => a.testBit p && b.testBit p) 693 := by
  rw [popK_eq]
  have : (fun i => (Nat.land a b).testBit i) = fun p => a.testBit p && b.testBit p :=
    funext fun p => Nat.testBit_and a b p
  rw [this]

theorem interK_spec {HS AB PB : Nat → Nat} (h : interK HS AB PB = true) :
    (∀ i, 1 ≤ i → i < 1408 → cnt (fun p => (HS 0).testBit p && (HS i).testBit p) 693 =
      if (AB 0).testBit i = true then 30 else 18) ∧
    (∀ off, off = 0 ∨ off = 1408 ∨ off = 2816 → ∀ f < 693, (HS off).testBit f = true ∨
      cnt (fun p => (HS off).testBit p && (PB f).testBit p) 693 = 30) := by
  unfold interK at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi1 hi2 => ?_, fun off hoff f hf => ?_⟩
  · rw [allN_lqt_iff] at h1
    have h3 := h1 (i - 1) (by omega)
    have e : Nat.succ (i - 1) = i := by omega
    simp only [e, letB_eq, Nat.beq_eq, popK_land, bitK_eq_testBit, nIf_eq] at h3
    exact h3
  · rw [allL_lqt_iff] at h2
    have h3 := h2 off (by simpa using hoff)
    simp only [letB_eq, allN_lqt_iff] at h3
    have h4 := h3 f hf
    simp only [orB_eq, Bool.or_eq_true, bitK_eq_testBit, Nat.beq_eq, popK_land] at h4
    exact h4

theorem diamK_spec {AB : Nat → Nat} (h : ∀ k < 11, diamK AB (128 * k) 128 = true) {v : Nat}
    (hv0 : 0 < v) (hv : v < 1408) (hn : (AB 0).testBit v = false) :
    Nat.land (AB 0) (AB v) ≠ 0 ∧ ∀ w < 1408, 0 < w → (AB 0).testBit w = false →
      (AB v).testBit w = true → Nat.land (Nat.land (AB 0) (AB v)) (AB w) ≠ 0 := by
  have h1 := h (v / 128) (by omega)
  unfold diamK at h1
  simp only [letB_eq] at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (v % 128) (by omega)
  have e : Nat.add (128 * (v / 128)) (v % 128) = v := by rw [Nat.add_eq]; omega
  have hb1 : Nat.blt 0 v = true := Nat.blt_eq.mpr hv0
  have hb2 : Nat.blt v 1408 = true := Nat.blt_eq.mpr hv
  simp only [e, letB_eq, impB_eq, andB_eq, hb1, hb2, bitK_eq_testBit, hn, notB_eq, Bool.and_eq_true,
    Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, Bool.not_eq_true',
    Bool.not_not, allN_lqt_iff] at h2
  obtain ⟨h3, h4⟩ := h2
  refine ⟨(nat_beq_eq_false_iff _ _).1 (by simpa using h3), fun w hw hw0 hw1 hw2 => ?_⟩
  have h5 := h4 w hw
  have hb3 : Nat.blt 0 w = true := Nat.blt_eq.mpr hw0
  simp only [hb3, hw1, hw2, Bool.not_true, Bool.not_false, Bool.and_self, Bool.false_or,
    Bool.not_eq_true'] at h5
  exact (nat_beq_eq_false_iff _ _).1 h5

@[expose] noncomputable def seenS (B : Nat) (AB : Nat → Nat) (Mv : Nat) : Nat → Nat
  | 0 => B
  | i + 1 => if 0 < seenS B AB Mv i ∧
        (i = 0 ∨ Nat.land (seenS B AB Mv i) (AB (fd 11 Mv (i + 1))) ≠ 0)
      then Nat.lor (seenS B AB Mv i) (Nat.shiftLeft 1 (fd 11 Mv (i + 1))) else 0

theorem seen_rec_eq (B : Nat) (AB : Nat → Nat) (Mv m : Nat) :
    Nat.rec (motive := fun _ => Nat) B
      (fun i seen => letN seen fun seen => Bool.rec (motive := fun _ => Nat) 0
        (Nat.lor seen (Nat.shiftLeft 1 (at' 11 Mv (Nat.succ i))))
        (andB (Nat.blt 0 seen) (orB (Nat.beq i 0)
          (notB (Nat.beq (Nat.land seen (AB (at' 11 Mv (Nat.succ i)))) 0))))) m =
        seenS B AB Mv m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show letN (Nat.rec (motive := fun _ => Nat) B
      (fun i seen => letN seen fun seen => Bool.rec (motive := fun _ => Nat) 0
        (Nat.lor seen (Nat.shiftLeft 1 (at' 11 Mv (Nat.succ i))))
        (andB (Nat.blt 0 seen) (orB (Nat.beq i 0)
          (notB (Nat.beq (Nat.land seen (AB (at' 11 Mv (Nat.succ i)))) 0))))) m) _ = _
    rw [ih, letN_eq]
    simp only [seenS, nIf_eq, andB_eq, orB_eq, notB_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', at'_eq, Nat.succ_eq_add_one, nat_beq_eq_false_iff]

theorem seenS_succ (B : Nat) (AB : Nat → Nat) (Mv i : Nat) :
    seenS B AB Mv (i + 1) = if 0 < seenS B AB Mv i ∧
        (i = 0 ∨ Nat.land (seenS B AB Mv i) (AB (fd 11 Mv (i + 1))) ≠ 0)
      then Nat.lor (seenS B AB Mv i) (Nat.shiftLeft 1 (fd 11 Mv (i + 1))) else 0 := rfl

theorem seenS_ne_zero {B : Nat} {AB : Nat → Nat} {Mv m : Nat} (h : seenS B AB Mv m ≠ 0) :
    ∀ n ≤ m, seenS B AB Mv n ≠ 0 := by
  intro n hn h0
  have : ∀ k, seenS B AB Mv (n + k) = 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [← Nat.add_assoc, seenS_succ, ih]
      simp
  have := this (m - n)
  rw [show n + (m - n) = m by omega] at this
  exact h this

theorem seenS_step {B : Nat} {AB : Nat → Nat} {Mv m : Nat} (h : seenS B AB Mv m ≠ 0) {i : Nat}
    (hi : i < m) : 0 < seenS B AB Mv i ∧
      (i = 0 ∨ Nat.land (seenS B AB Mv i) (AB (fd 11 Mv (i + 1))) ≠ 0) := by
  have h1 := seenS_ne_zero h (i + 1) hi
  rw [seenS_succ] at h1
  by_cases hc : 0 < seenS B AB Mv i ∧
      (i = 0 ∨ Nat.land (seenS B AB Mv i) (AB (fd 11 Mv (i + 1))) ≠ 0)
  · exact hc
  · rw [if_neg hc] at h1
    exact absurd rfl h1

theorem seenS_testBit {B : Nat} {AB : Nat → Nat} {Mv m : Nat} (h : seenS B AB Mv m ≠ 0) :
    ∀ n ≤ m, ∀ u, (seenS B AB Mv n).testBit u = true ↔
      (B.testBit u = true ∨ ∃ j < n, fd 11 Mv (j + 1) = u) := by
  intro n
  induction n with
  | zero =>
    intro _ u
    constructor
    · intro hu
      exact Or.inl hu
    · rintro (hu | ⟨j, hj, _⟩)
      · exact hu
      · exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    intro hn u
    have hc := seenS_step h (by omega : n < m)
    rw [seenS_succ, if_pos hc, Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, ih (by omega) u,
      show Nat.shiftLeft 1 (fd 11 Mv (n + 1)) = 2 ^ fd 11 Mv (n + 1) from Nat.one_shiftLeft _,
      Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro ((hu | ⟨j, hj, hju⟩) | hu)
      · exact Or.inl hu
      · exact Or.inr ⟨j, by omega, hju⟩
      · exact Or.inr ⟨n, by omega, hu⟩
    · rintro (hu | ⟨j, hj, hju⟩)
      · exact Or.inl (Or.inl hu)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inl (Or.inr ⟨j, hj, hju⟩)
        · exact Or.inr hju

theorem lorM_aux (Mv n : Nat) : Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (at' 11 Mv (Nat.succ i)))) n =
      lorS (fun _ => false) (fun i => fd 11 Mv (i + 1)) n := by
  unfold lorS
  refine rec_congr (fun i acc => ?_) n
  simp only [at'_eq, Bool.false_eq_true, ↓reduceIte, Nat.succ_eq_add_one]

theorem muK_spec {AB MT : Nat → Nat} (hAB : ∀ x < 1408, AB x < 2 ^ 1408)
    (h : ∀ k < 11, muK AB MT (128 * k) 128 = true) {v : Nat} (hv0 : 0 < v) (hv : v < 1408)
    (hn : (AB 0).testBit v = false) :
    fd 11 (MT v) 0 ≠ 0 ∧
    (∀ x, (Nat.land (AB 0) (AB v)).testBit x = true ↔
      ∃ i < fd 11 (MT v) 0, fd 11 (MT v) (i + 1) = x) ∧
    ∀ i < fd 11 (MT v) 0, 0 < i → ∃ j < i,
      (AB (fd 11 (MT v) (i + 1))).testBit (fd 11 (MT v) (j + 1)) = true := by
  have h1 := h (v / 128) (by omega)
  unfold muK at h1
  simp only [letB_eq] at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (v % 128) (by omega)
  have e : Nat.add (128 * (v / 128)) (v % 128) = v := by rw [Nat.add_eq]; omega
  have hb1 : Nat.blt 0 v = true := Nat.blt_eq.mpr hv0
  have hb2 : Nat.blt v 1408 = true := Nat.blt_eq.mpr hv
  simp only [e, letB_eq] at h2
  rw [seen_rec_eq, lorM_aux] at h2
  simp only [impB_eq, andB_eq, hb1, hb2, bitK_eq_testBit, hn, notB_eq, Bool.and_eq_true,
    Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, Bool.not_eq_true', at'_eq,
    nat_beq_eq_false_iff, Nat.beq_eq] at h2
  obtain ⟨hm, hlor, hseen⟩ := h2
  have hC : ∀ x, (Nat.land (AB 0) (AB v)).testBit x = true ↔
      ∃ i < fd 11 (MT v) 0, fd 11 (MT v) (i + 1) = x := by
    intro x
    rw [← hlor, lorS, testBit_fold_or_skip]
    simp
  refine ⟨hm, hC, fun i hi hi0 => ?_⟩
  have hs := seenS_step hseen hi
  have hCl : Nat.land (AB 0) (AB v) < 2 ^ 1408 := Nat.and_lt_two_pow (AB 0) (hAB v hv)
  have hlt : ∀ j < fd 11 (MT v) 0, fd 11 (MT v) (j + 1) < 1408 := by
    intro j hj
    by_contra hcon
    have h3 := (hC (fd 11 (MT v) (j + 1))).2 ⟨j, hj, rfl⟩
    have h4 := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hCl (Nat.pow_le_pow_right
      (by norm_num) (Nat.not_lt.1 hcon)))
    rw [h3] at h4
    exact absurd h4 (by simp)
  rcases hs.2 with h0 | hne
  · omega
  · by_contra hnone
    apply hne
    apply Nat.eq_of_testBit_eq
    intro u
    rw [Nat.zero_testBit]
    show (Nat.land (seenS (Nat.shiftLeft 1 1408) AB (MT v) i)
      (AB (fd 11 (MT v) (i + 1)))).testBit u = false
    rw [show Nat.land (seenS (Nat.shiftLeft 1 1408) AB (MT v) i) (AB (fd 11 (MT v) (i + 1))) =
      seenS (Nat.shiftLeft 1 1408) AB (MT v) i &&& AB (fd 11 (MT v) (i + 1)) from rfl,
      Nat.testBit_and]
    cases hb : (seenS (Nat.shiftLeft 1 1408) AB (MT v) i).testBit u
    · rfl
    · cases hb' : (AB (fd 11 (MT v) (i + 1))).testBit u
      · rfl
      · exfalso
        rcases (seenS_testBit hseen i (by omega) u).1 hb with hB | ⟨j, hj, hju⟩
        · rw [show Nat.shiftLeft 1 1408 = 2 ^ 1408 from Nat.one_shiftLeft _, Nat.testBit_two_pow,
            decide_eq_true_iff] at hB
          have := hAB (fd 11 (MT v) (i + 1)) (hlt i hi)
          have h5 := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le this
            (Nat.pow_le_pow_right (by norm_num) (by omega : 1408 ≤ u)))
          rw [h5] at hb'
          exact absurd hb' (by simp)
        · exact hnone ⟨j, by omega, by rw [← hju] at hb'; exact hb'⟩

@[expose] def invBody (S : Flags) (row : Array Nat) (f : Nat) (r : Array Nat) :
    Id (ForInStep (Array Nat)) :=
  if (!S[f]!) = true then pure (ForInStep.yield (r.set! row[f]! f)) else pure (ForInStep.yield r)

theorem xiInv_getElem (H : Array Flags) (Im : Array (Array Nat)) {k : Nat} (hk : k < 1408) :
    (xiInv H Im)[k]! =
      Id.run (forIn [:693] (Array.replicate 1408 693) (invBody H[k]! Im[k]!)) := by
  unfold xiInv
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rfl

@[expose] def InvInv (S : Flags) (row : Array Nat) (m : Nat) (r : Array Nat) : Prop :=
  r.size = 1408 ∧ (∀ f < m, S[f]! = false → r[row[f]!]! = f) ∧
    (∀ i < 1408, (∀ f < m, S[f]! = false → row[f]! ≠ i) → r[i]! = 693)

theorem xiInv_loop {S : Flags} {row : Array Nat}
    (hrow : ∀ f < 693, S[f]! = false → row[f]! < 1408)
    (hinj : ∀ f < 693, ∀ f' < 693, S[f]! = false → S[f']! = false → row[f]! = row[f']! →
      f = f') :
    InvInv S row 693 (Id.run (forIn [:693] (Array.replicate 1408 693) (invBody S row))) := by
  refine forIn_range_inv (InvInv S row) (InvInv S row 693) (invBody S row) 693 _
    (fun q r hq hI => ?_) (fun r hr => hr) ?_
  · obtain ⟨hs, h2, h3⟩ := hI
    unfold invBody
    cases hS : S[q]!
    · have hp : row[q]! < 1408 := hrow q hq hS
      have hne : ∀ f < q, S[f]! = false → row[f]! ≠ row[q]! := fun f hf hSf h =>
        absurd (hinj f (by omega) q hq hSf hS h) (by omega)
      show InvInv S row (q + 1) (r.set! row[q]! q)
      refine ⟨by rw [Array.size_set!, hs], fun f hf hSf => ?_, fun i hi hall => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf | rfl
        · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hne f hf hSf h.symm)]
          exact h2 f hf hSf
        · exact Array.getElem!_set!_self _ _ _ (by omega)
      · have hi' : row[q]! ≠ i := hall q (by omega) hS
        rw [Array.getElem!_set!_ne _ _ _ _ hi']
        exact h3 i hi (fun f hf hSf => hall f (by omega) hSf)
    · show InvInv S row (q + 1) r
      refine ⟨hs, fun f hf hSf => ?_, fun i hi hall => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf | rfl
        · exact h2 f hf hSf
        · rw [hS] at hSf
          exact absurd hSf (by simp)
      · exact h3 i hi (fun f hf hSf => hall f (by omega) hSf)
  · refine ⟨by simp, fun f hf => absurd hf (Nat.not_lt_zero _), fun i hi _ => ?_⟩
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_replicate]

end CFSG.KC.Misc.Xi

end
