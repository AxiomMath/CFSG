module

public import CFSG.Certificates.Kernel.Fi22Rk.PbN
public import CFSG.Certificates.Kernel.Fi22Rk.PbChecks
import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.KC.Fi22RkS

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.KLie.CT (orB notB anyN sumN)

noncomputable abbrev LAN (N : Nat) (LK : Nat → Nat) : Array (Array Nat) :=
  ofN N fun k => unpack 243 8 (LK k)

variable {N : Nat} {MUK LK EK PLK SL MTK FMK : Nat → Nat}

section Table

variable (hP : ∀ k < N, PP 243 8 (LK k)) (hinj : ∀ a < N, ∀ b < N, LK a = LK b → a = b)
  (hL0 : LK 0 = pidn 243 8) (hmt : mtKN N LK MTK = true)

theorem la_getN {k : Nat} (hk : k < N) : (LAN N LK)[k]! = unpack 243 8 (LK k) := ofN_get _ hk

include hP hinj in
theorem eqA_idxN {a b : Nat} (ha : a < N) (hb : b < N) :
    eqA 243 (LAN N LK)[a]! (LAN N LK)[b]! = (a == b) := by
  rw [la_getN ha, la_getN hb, eqA_unpack (hP a ha).1 (hP b hb).1]
  refine Bool.eq_iff_iff.mpr ?_
  rw [Nat.beq_eq, beq_iff_eq]
  exact ⟨hinj a ha b hb, fun e => by rw [e]⟩

include hmt in
theorem mt_factsN {k l : Nat} (hk : k < N) (hl : l < N) :
    mt MTK k l < N ∧ LK (mt MTK k l) = ps (LK k) (LK l) := by
  unfold mtKN at hmt
  have h3 := allN_spec (allN_spec hmt k hk) l hl
  rw [strictB_eq] at h3
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h3
  exact ⟨Nat.blt_eq.mp h4, Nat.eq_of_beq_eq_true h5⟩

include hP hmt in
theorem comp_idxN {a b : Nat} (ha : a < N) (hb : b < N) :
    compA 243 (LAN N LK)[a]! (LAN N LK)[b]! = (LAN N LK)[mt MTK a b]! := by
  rw [la_getN ha, la_getN hb, la_getN (mt_factsN hmt ha hb).1, (mt_factsN hmt ha hb).2]
  exact compA_unpack (hP a ha).1 (hP b hb).1

include hL0 in
theorem id_idxN (hN1 : 0 < N) : idA 243 = (LAN N LK)[0]! := by
  rw [la_getN hN1, hL0]
  exact idA_eq (by decide)

include hP hinj hmt in
theorem commA_idxN {k l : Nat} (hk : k < N) (hl : l < N) :
    commA (LAN N LK)[k]! (LAN N LK)[l]! = cm MTK k l := by
  unfold commA cm
  rw [comp_idxN hP hmt hk hl, comp_idxN hP hmt hl hk,
    eqA_idxN hP hinj (mt_factsN hmt hk hl).1 (mt_factsN hmt hl hk).1, nbeq']

include hP hL0 hmt in
theorem pow_idxN (hN1 : 0 < N) {k i : Nat} (hk : k < N) (hi : i < 3) :
    powA 243 (LAN N LK)[k]! i = (LAN N LK)[pwI MTK k i]! ∧ pwI MTK k i < N := by
  have h0 := id_idxN hL0 hN1
  have m0 := mt_factsN hmt hk hN1
  have m1 := mt_factsN hmt hk m0.1
  interval_cases i
  · exact ⟨h0, hN1⟩
  · refine ⟨?_, m0.1⟩
    change compA 243 (LAN N LK)[k]! (idA 243) = _
    rw [h0, comp_idxN hP hmt hk hN1]
    rfl
  · refine ⟨?_, m1.1⟩
    change compA 243 (LAN N LK)[k]! (compA 243 (LAN N LK)[k]! (idA 243)) = _
    rw [h0, comp_idxN hP hmt hk hN1, comp_idxN hP hmt hk m0.1]
    rfl

end Table

variable (hFM : ∀ k < N, Nat.shiftRight (FMK k) 243 = 0 ∧ ∀ v < 243,
    fld(FMK k, v, nat_lit 1) = Bool.rec (motive := fun _ => Nat) 0 1
      (Nat.beq (pg 8 255 (LK k) v) v))

include hFM in
theorem fix1_eqN {k : Nat} (hk : k < N) : fix1 (LAN N LK)[k]! = pop (FMK k) := by
  rw [pop_eq, la_getN hk]
  unfold fix1
  exact countP_congr' fun v => (fm_bit (hFM k hk) v.2).symm

include hFM in
theorem fix2_eqN {k l : Nat} (hk : k < N) (hl : l < N) :
    fix2 (LAN N LK)[k]! (LAN N LK)[l]! = pop (Nat.land (FMK k) (FMK l)) := by
  rw [pop_eq, la_getN hk, la_getN hl]
  unfold fix2
  exact countP_congr' fun v => by
    rw [testBit_land, fm_bit (hFM k hk) v.2, fm_bit (hFM l hl) v.2]

include hFM in
theorem fix3_eqN {k l r : Nat} (hk : k < N) (hl : l < N) (hr : r < N) :
    fix3 (LAN N LK)[k]! (LAN N LK)[l]! (LAN N LK)[r]! =
      pop (Nat.land (Nat.land (FMK k) (FMK l)) (FMK r)) := by
  rw [pop_eq, la_getN hk, la_getN hl, la_getN hr]
  unfold fix3
  exact countP_congr' fun v => by
    rw [testBit_land, testBit_land, fm_bit (hFM k hk) v.2, fm_bit (hFM l hl) v.2,
      fm_bit (hFM r hr) v.2]

theorem tree_factsN (h : treeKN N MUK LK PLK MTK FMK = true) :
    (∀ k < N, k ≠ 0 → parP PLK k < k ∧ labP PLK k < 2 ∧
      LK k = ps (LK (parP PLK k)) (MUK (labP PLK k))) ∧
    (∀ l < 2, ∃ r < N, MUK l = LK r) ∧ (∀ k < N, ∃ r < N, mt MTK k r = 0) ∧
    (∀ k < N, Nat.shiftRight (FMK k) 243 = 0 ∧ ∀ v < 243,
      fld(FMK k, v, nat_lit 1) = Bool.rec (motive := fun _ => Nat) 0 1
        (Nat.beq (pg 8 255 (LK k) v) v)) := by
  unfold treeKN at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun k hk hk0 => ?_, fun l hl => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have a := allN_spec h1 k hk
    rw [orB_eq', nbeq', Bool.or_eq_true, beq_iff_eq] at a
    rcases a with a | a
    · exact absurd a hk0
    · rw [strictB_eq, strictB_eq] at a
      obtain ⟨b1, b⟩ := (bAnd_iff _ _).1 a
      obtain ⟨b2, b3⟩ := (bAnd_iff _ _).1 b
      exact ⟨Nat.blt_eq.mp b1, Nat.blt_eq.mp b2, Nat.eq_of_beq_eq_true b3⟩
  · obtain ⟨r, hr, e⟩ := anyN_iff.1 (allN_spec h2 l hl)
    exact ⟨r, hr, Nat.eq_of_beq_eq_true e⟩
  · obtain ⟨r, hr, e⟩ := anyN_iff.1 (allN_spec h3 k hk)
    exact ⟨r, hr, Nat.eq_of_beq_eq_true e⟩
  · have a := allN_spec h4 k hk
    rw [strictB_eq, strictB_eq] at a
    obtain ⟨b1, b2⟩ := (bAnd_iff _ _).1 a
    exact ⟨Nat.eq_of_beq_eq_true b1, fun v hv => Nat.eq_of_beq_eq_true (allN_spec b2 v hv)⟩

variable {mus : Array (Array Nat)} (hMs : mus.size = 2)
  (hM : ∀ l < 2, mus[l]! = unpack 243 8 (MUK l))
  (hMc : ∀ l < 2, canonK 243 8 (mask 8) (243 * 8) (MUK l) = true)
  (hrun : pbRunKN N MUK LK EK PLK SL = true) (htree : treeKN N MUK LK PLK MTK FMK = true)
  (hmt : mtKN N LK MTK = true) (hN1 : 1 ≤ N) (hN2 : N ≤ 243)

include hMs hM hMc hrun htree hmt hN1 hN2 in
theorem pbOK_ofN : pbOK mus N = true := by
  obtain ⟨hL0, -, -, hinj, -⟩ := run_factsN hrun
  have hP := fun k (hk : k < N) => PP_LN hrun hk
  obtain ⟨t1, t2, t3, -⟩ := tree_factsN htree
  unfold pbOK
  rw [pbBFS_eqN hMs hM hMc hrun hN1 hN2]
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨ofN_size _ _, ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun l hl => ?_⟩,
    fun k hk l hl => ?_⟩, fun k hk => ?_⟩, fun k hk l hl => ?_⟩
  · change eqA 243 (LAN N LK)[0]! (idA 243) = true
    rw [id_idxN hL0 hN1, eqA_idxN hP hinj hN1 hN1]
    rfl
  · change isInvA 243 (LAN N LK)[k]! (invCand 243 (LAN N LK)[k]!) = true
    rw [la_getN hk]
    exact isInvA_PP (hP k hk)
  · rw [Bool.or_eq_true, beq_iff_eq]
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      obtain ⟨a1, a2, a3⟩ := t1 k hk hk0
      rw [ofN_get _ hk, ofN_get _ hk]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨a1, a2⟩, ?_⟩
      change eqA 243 (LAN N LK)[k]! (compA 243 (LAN N LK)[parP PLK k]! mus[labP PLK k]!) = true
      have e : unpack 243 8 (pcomp 243 8 (mask 8) (LK (parP PLK k)) (MUK (labP PLK k))) =
          unpack 243 8 (LK k) := by
        rw [a3]
        rfl
      rw [la_getN hk, la_getN (by omega), hM _ a2, compA_unpack (hP _ (by omega)).1 (hMc _ a2),
        e, eqA_unpack (hP k hk).1 (hP k hk).1]
      exact Nat.beq_refl _
  · obtain ⟨r, hr, e⟩ := t2 l hl
    rw [anyLt_iff']
    refine ⟨r, hr, ?_⟩
    change eqA 243 mus[l]! (LAN N LK)[r]! = true
    rw [hM l hl, la_getN hr, e, eqA_unpack (hP r hr).1 (hP r hr).1]
    exact Nat.beq_refl _
  · rw [anyLt_iff']
    refine ⟨mt MTK k l, (mt_factsN hmt hk hl).1, ?_⟩
    change eqA 243 (compA 243 (LAN N LK)[k]! (LAN N LK)[l]!) (LAN N LK)[mt MTK k l]! = true
    rw [comp_idxN hP hmt hk hl,
      eqA_idxN hP hinj (mt_factsN hmt hk hl).1 (mt_factsN hmt hk hl).1]
    exact beq_self_eq_true _
  · obtain ⟨r, hr, e⟩ := t3 k hk
    rw [anyLt_iff']
    refine ⟨r, hr, ?_⟩
    change eqA 243 (compA 243 (LAN N LK)[k]! (LAN N LK)[r]!) (idA 243) = true
    rw [comp_idxN hP hmt hk hr, id_idxN hL0 hN1, e, eqA_idxN hP hinj hN1 hN1]
    rfl
  · rw [Bool.or_eq_true, beq_iff_eq]
    by_cases e : k = l
    · exact Or.inl e
    · right
      change (!eqA 243 (LAN N LK)[k]! (LAN N LK)[l]!) = true
      rw [eqA_idxN hP hinj hk hl, Bool.not_eq_true', beq_eq_false_iff_ne]
      exact e

include hMs hM hMc hrun htree hmt hN1 hN2 in
theorem fixOK_ofN (h : ∀ k < N, fixAtN N MTK FMK k = true) : fixOK mus N = true := by
  obtain ⟨hL0, -, -, hinj, -⟩ := run_factsN hrun
  have hP := fun k (hk : k < N) => PP_LN hrun hk
  have hFM := (tree_factsN htree).2.2.2
  have hid := id_idxN hL0 hN1
  have heq := fun a (ha : a < N) b (hb : b < N) => eqA_idxN hP hinj (a := a) (b := b) ha hb
  have hex : ∀ k < N, ∀ l < N, pairEx (LAN N LK)[k]! (LAN N LK)[l]! = exK MTK k l := by
    intro k hk l hl
    unfold pairEx exK
    rw [hid, heq k hk 0 hN1, heq l hl 0 hN1, heq l hl k hk,
      comp_idxN hP hmt hk hk, heq l hl _ (mt_factsN hmt hk hk).1, commA_idxN hP hinj hmt hk hl,
      orB_eq', orB_eq', orB_eq', orB_eq', notB_eq, nbeq', nbeq', nbeq', nbeq']
    simp only [Bool.or_assoc]
  unfold fixOK
  rw [pbBFS_eqN hMs hM hMc hrun hN1 hN2]
  simp only [Bool.and_eq_true, allLt_iff]
  have F : ∀ k < N, (k = 0 ∨ pop (FMK k) ≤ 27) ∧ ∀ l < N, exK MTK k l = true ∨
      (pop (Nat.land (FMK k) (FMK l)) ≤ 9 ∧ ∀ r < N, cm MTK k r = false ∨ cm MTK l r = false ∨
        (∃ i < 3, ∃ j < 3, r = mt MTK (pwI MTK k i) (pwI MTK l j)) ∨
        pop (Nat.land (Nat.land (FMK k) (FMK l)) (FMK r)) ≤ 3) := by
    intro k hk
    have a := h k hk
    unfold fixAtN at a
    rw [strictB_eq] at a
    obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 a
    rw [orB_eq', Bool.or_eq_true, nbeq', beq_iff_eq, Nat.ble_eq] at a1
    refine ⟨a1, fun l hl => ?_⟩
    have b := allN_spec a2 l hl
    rw [orB_eq', Bool.or_eq_true, strictB_eq] at b
    rcases b with b | b
    · exact Or.inl b
    · rw [bAnd_iff] at b
      obtain ⟨b1, b2⟩ := b
      refine Or.inr ⟨Nat.ble_eq.mp b1, fun r hr => ?_⟩
      have c := allN_spec b2 r hr
      simp only [orB_eq', notB_eq, Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq] at c
      rcases c with c | c | c | c
      · exact Or.inl c
      · exact Or.inr (Or.inl c)
      · right
        right
        left
        obtain ⟨i, hi, c⟩ := anyN_iff.1 c
        obtain ⟨j, hj, c⟩ := anyN_iff.1 c
        exact ⟨i, hi, j, hj, Nat.eq_of_beq_eq_true c⟩
      · exact Or.inr (Or.inr (Or.inr c))
  refine ⟨⟨fun k hk => ?_, fun k hk l hl => ?_⟩, fun k hk l hl => ?_⟩
  · change (eqA 243 (LAN N LK)[k]! (idA 243) || decide (fix1 (LAN N LK)[k]! ≤ 27)) = true
    rw [hid, heq k hk 0 hN1, fix1_eqN hFM hk, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    exact (F k hk).1
  · change (pairEx (LAN N LK)[k]! (LAN N LK)[l]! ||
      decide (fix2 (LAN N LK)[k]! (LAN N LK)[l]! ≤ 9)) = true
    rw [hex k hk l hl, fix2_eqN hFM hk hl, Bool.or_eq_true, decide_eq_true_eq]
    rcases (F k hk).2 l hl with a | a
    · exact Or.inl a
    · exact Or.inr a.1
  · change (pairEx (LAN N LK)[k]! (LAN N LK)[l]! || allLt N fun r =>
      (!commA (LAN N LK)[k]! (LAN N LK)[r]! || !commA (LAN N LK)[l]! (LAN N LK)[r]! ||
      (anyLt 3 fun i => anyLt 3 fun j => eqA 243 (LAN N LK)[r]!
        (compA 243 (powA 243 (LAN N LK)[k]! i) (powA 243 (LAN N LK)[l]! j)))) ||
      decide (fix3 (LAN N LK)[k]! (LAN N LK)[l]! (LAN N LK)[r]! ≤ 3)) = true
    rw [hex k hk l hl, Bool.or_eq_true]
    rcases (F k hk).2 l hl with a | a
    · exact Or.inl a
    · right
      rw [allLt_iff]
      intro r hr
      rw [commA_idxN hP hinj hmt hk hr, commA_idxN hP hinj hmt hl hr, fix3_eqN hFM hk hl hr]
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      rcases a.2 r hr with c | c | c | c
      · exact Or.inl (Or.inl (Or.inl c))
      · exact Or.inl (Or.inl (Or.inr c))
      · left
        right
        obtain ⟨i, hi, j, hj, e⟩ := c
        rw [anyLt_iff']
        refine ⟨i, hi, ?_⟩
        rw [anyLt_iff']
        refine ⟨j, hj, ?_⟩
        obtain ⟨pi, pil⟩ := pow_idxN hP hL0 hmt hN1 hk hi
        obtain ⟨pj, pjl⟩ := pow_idxN hP hL0 hmt hN1 hl hj
        rw [pi, pj, comp_idxN hP hmt pil pjl, heq r hr _ (mt_factsN hmt pil pjl).1, e]
        exact beq_self_eq_true _
      · exact Or.inr c

end CFSG.KC.Fi22RkS

end
