module

public import CFSG.Certificates.Kernel.Fi22Rk.Pb
import CFSG.Certificates.Kernel.Fi24Pl.Sound

public section

namespace CFSG.KC.Fi22RkS

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.KLie.CT (orB notB anyN sumN)

noncomputable abbrev LA (LK : Nat → Nat) : Array (Array Nat) := ofN 81 fun k => unpack 243 8 (LK k)

theorem nbeq' (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, beq_iff_eq])

theorem orB_eq' (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem bAnd_eq' (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem anyN_iff {N : Nat} {f : Nat → Bool} : anyN N f = true ↔ ∃ i < N, f i = true := by
  rw [anyN_eq, List.any_eq_true]
  simp

theorem anyLt_iff' {N : Nat} {p : Nat → Bool} : anyLt N p = true ↔ ∃ i < N, p i = true := by
  unfold anyLt
  rw [Bool.not_eq_true', ← Bool.not_eq_true, allLt_iff]
  simp

theorem anyLt_eq_anyN (N : Nat) (p : Nat → Bool) : anyLt N p = anyN N p :=
  Bool.eq_iff_iff.mpr (anyLt_iff'.trans anyN_iff.symm)

variable {MUK LK EK PLK SL MTK FMK : Nat → Nat}

section Table

variable (hP : ∀ k < 81, PP 243 8 (LK k)) (hinj : ∀ a < 81, ∀ b < 81, LK a = LK b → a = b)
  (hL0 : LK 0 = pidn 243 8) (hmt : ∀ c < 9, mtC LK MTK c = true)

theorem la_get {k : Nat} (hk : k < 81) : (LA LK)[k]! = unpack 243 8 (LK k) := ofN_get _ hk

include hP hinj in
theorem eqA_idx {a b : Nat} (ha : a < 81) (hb : b < 81) :
    eqA 243 (LA LK)[a]! (LA LK)[b]! = (a == b) := by
  rw [la_get ha, la_get hb, eqA_unpack (hP a ha).1 (hP b hb).1]
  refine Bool.eq_iff_iff.mpr ?_
  rw [Nat.beq_eq, beq_iff_eq]
  exact ⟨hinj a ha b hb, fun e => by rw [e]⟩

include hmt in
theorem mt_facts {k l : Nat} (hk : k < 81) (hl : l < 81) :
    mt MTK k l < 81 ∧ LK (mt MTK k l) = ps (LK k) (LK l) := by
  have h1 := hmt (k / 9) (by omega)
  unfold mtC at h1
  have h2 := allN_spec h1 (k % 9) (Nat.mod_lt _ (by decide))
  rw [strictB_eq] at h2
  have e : Nat.add (Nat.mul 9 (k / 9)) (k % 9) = k := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h2
  have h3 := allN_spec h2 l hl
  rw [strictB_eq] at h3
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h3
  exact ⟨Nat.blt_eq.mp h4, Nat.eq_of_beq_eq_true h5⟩

include hP hmt in
theorem comp_idx {a b : Nat} (ha : a < 81) (hb : b < 81) :
    compA 243 (LA LK)[a]! (LA LK)[b]! = (LA LK)[mt MTK a b]! := by
  rw [la_get ha, la_get hb, la_get (mt_facts hmt ha hb).1, (mt_facts hmt ha hb).2]
  exact compA_unpack (hP a ha).1 (hP b hb).1

include hL0 in
theorem id_idx : idA 243 = (LA LK)[0]! := by
  rw [la_get (by decide), hL0]
  exact idA_eq (by decide)

include hP hinj hmt in
theorem commA_idx {k l : Nat} (hk : k < 81) (hl : l < 81) :
    commA (LA LK)[k]! (LA LK)[l]! = cm MTK k l := by
  unfold commA cm
  rw [comp_idx hP hmt hk hl, comp_idx hP hmt hl hk,
    eqA_idx hP hinj (mt_facts hmt hk hl).1 (mt_facts hmt hl hk).1, nbeq']

include hP hL0 hmt in
theorem pow_idx {k i : Nat} (hk : k < 81) (hi : i < 3) :
    powA 243 (LA LK)[k]! i = (LA LK)[pwI MTK k i]! ∧ pwI MTK k i < 81 := by
  have h0 := id_idx hL0
  have m0 := mt_facts hmt hk (by decide : 0 < 81)
  have m1 := mt_facts hmt hk m0.1
  interval_cases i
  · exact ⟨h0, by change 0 < 81; decide⟩
  · refine ⟨?_, m0.1⟩
    change compA 243 (LA LK)[k]! (idA 243) = _
    rw [h0, comp_idx hP hmt hk (by decide)]
    rfl
  · refine ⟨?_, m1.1⟩
    change compA 243 (LA LK)[k]! (compA 243 (LA LK)[k]! (idA 243)) = _
    rw [h0, comp_idx hP hmt hk (by decide), comp_idx hP hmt hk m0.1]
    rfl

end Table

theorem pop_eq (b : Nat) : pop b = (List.finRange 243).countP (fun i => Nat.testBit b i.val) :=
  CFSG.KC.Fi24PlS.popK_eq b

theorem fm_bit {p f : Nat} (hf : (Nat.shiftRight f 243 = 0 ∧ ∀ v < 243,
    fld(f, v, nat_lit 1) = Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (pg 8 255 p v) v)))
    {v : Nat} (hv : v < 243) : Nat.testBit f v = ((unpack 243 8 p)[v]! == v) := by
  have h1 := hf.2 v hv
  rw [CFSG.KC.Fi24PlS.fld_one_eq] at h1
  rw [get_unpack hv]
  change Nat.testBit f v = (pg 8 255 p v == v)
  rw [← nbeq']
  cases hb : Nat.testBit f v <;> cases hc : Nat.beq (pg 8 255 p v) v <;> rw [hb, hc] at h1 <;>
    revert h1 <;> decide

variable (hFM : ∀ k < 81, Nat.shiftRight (FMK k) 243 = 0 ∧ ∀ v < 243,
    fld(FMK k, v, nat_lit 1) = Bool.rec (motive := fun _ => Nat) 0 1
      (Nat.beq (pg 8 255 (LK k) v) v))

theorem countP_congr' {f g : Fin 243 → Bool} (h : ∀ v : Fin 243, f v = g v) :
    (List.finRange 243).countP f = (List.finRange 243).countP g := by
  rw [show f = g from funext h]

include hFM in
theorem fix1_eq {k : Nat} (hk : k < 81) : fix1 (LA LK)[k]! = pop (FMK k) := by
  rw [pop_eq, la_get hk]
  unfold fix1
  exact countP_congr' fun v => (fm_bit (hFM k hk) v.2).symm

theorem testBit_land (a b i : Nat) : Nat.testBit (Nat.land a b) i = (Nat.testBit a i && Nat.testBit b i) :=
  Nat.testBit_and a b i

include hFM in
theorem fix2_eq {k l : Nat} (hk : k < 81) (hl : l < 81) :
    fix2 (LA LK)[k]! (LA LK)[l]! = pop (Nat.land (FMK k) (FMK l)) := by
  rw [pop_eq, la_get hk, la_get hl]
  unfold fix2
  exact countP_congr' fun v => by
    rw [testBit_land, fm_bit (hFM k hk) v.2, fm_bit (hFM l hl) v.2]

include hFM in
theorem fix3_eq {k l r : Nat} (hk : k < 81) (hl : l < 81) (hr : r < 81) :
    fix3 (LA LK)[k]! (LA LK)[l]! (LA LK)[r]! = pop (Nat.land (Nat.land (FMK k) (FMK l)) (FMK r)) := by
  rw [pop_eq, la_get hk, la_get hl, la_get hr]
  unfold fix3
  exact countP_congr' fun v => by
    rw [testBit_land, testBit_land, fm_bit (hFM k hk) v.2, fm_bit (hFM l hl) v.2,
      fm_bit (hFM r hr) v.2]

theorem tree_facts (h : treeK MUK LK PLK MTK FMK = true) :
    (∀ k < 81, k ≠ 0 → parP PLK k < k ∧ labP PLK k < 2 ∧
      LK k = ps (LK (parP PLK k)) (MUK (labP PLK k))) ∧
    (∀ l < 2, ∃ r < 81, MUK l = LK r) ∧ (∀ k < 81, ∃ r < 81, mt MTK k r = 0) ∧
    (∀ k < 81, Nat.shiftRight (FMK k) 243 = 0 ∧ ∀ v < 243,
      fld(FMK k, v, nat_lit 1) = Bool.rec (motive := fun _ => Nat) 0 1
        (Nat.beq (pg 8 255 (LK k) v) v)) := by
  unfold treeK at h
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
  (hrun : pbRunK MUK LK EK PLK SL = true) (htree : treeK MUK LK PLK MTK FMK = true)
  (hmt : ∀ c < 9, mtC LK MTK c = true)

include hMs hM hMc hrun htree hmt in
theorem pbOK_of : pbOK mus 81 = true := by
  obtain ⟨hL0, -, -, hinj, -⟩ := run_facts hrun
  have hP := fun k (hk : k < 81) => PP_L hrun hk
  obtain ⟨t1, t2, t3, -⟩ := tree_facts htree
  unfold pbOK
  rw [pbBFS_eq hMs hM hMc hrun]
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨ofN_size _ _, ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun l hl => ?_⟩,
    fun k hk l hl => ?_⟩, fun k hk => ?_⟩, fun k hk l hl => ?_⟩
  · change eqA 243 (LA LK)[0]! (idA 243) = true
    rw [id_idx hL0, eqA_idx hP hinj (by decide) (by decide)]
    rfl
  · change isInvA 243 (LA LK)[k]! (invCand 243 (LA LK)[k]!) = true
    rw [la_get hk]
    exact isInvA_PP (hP k hk)
  · rw [Bool.or_eq_true, beq_iff_eq]
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      obtain ⟨a1, a2, a3⟩ := t1 k hk hk0
      rw [ofN_get _ hk, ofN_get _ hk]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨a1, a2⟩, ?_⟩
      change eqA 243 (LA LK)[k]! (compA 243 (LA LK)[parP PLK k]! mus[labP PLK k]!) = true
      have e : unpack 243 8 (pcomp 243 8 (mask 8) (LK (parP PLK k)) (MUK (labP PLK k))) =
          unpack 243 8 (LK k) := by
        rw [a3]
        rfl
      rw [la_get hk, la_get (by omega), hM _ a2, compA_unpack (hP _ (by omega)).1 (hMc _ a2), e,
        eqA_unpack (hP k hk).1 (hP k hk).1]
      exact Nat.beq_refl _
  · obtain ⟨r, hr, e⟩ := t2 l hl
    rw [anyLt_iff']
    refine ⟨r, hr, ?_⟩
    change eqA 243 mus[l]! (LA LK)[r]! = true
    rw [hM l hl, la_get hr, e, eqA_unpack (hP r hr).1 (hP r hr).1]
    exact Nat.beq_refl _
  · rw [anyLt_iff']
    refine ⟨mt MTK k l, (mt_facts hmt hk hl).1, ?_⟩
    change eqA 243 (compA 243 (LA LK)[k]! (LA LK)[l]!) (LA LK)[mt MTK k l]! = true
    rw [comp_idx hP hmt hk hl, eqA_idx hP hinj (mt_facts hmt hk hl).1 (mt_facts hmt hk hl).1]
    exact beq_self_eq_true _
  · obtain ⟨r, hr, e⟩ := t3 k hk
    rw [anyLt_iff']
    refine ⟨r, hr, ?_⟩
    change eqA 243 (compA 243 (LA LK)[k]! (LA LK)[r]!) (idA 243) = true
    rw [comp_idx hP hmt hk hr, id_idx hL0, e, eqA_idx hP hinj (by decide) (by decide)]
    rfl
  · rw [Bool.or_eq_true, beq_iff_eq]
    by_cases e : k = l
    · exact Or.inl e
    · right
      change (!eqA 243 (LA LK)[k]! (LA LK)[l]!) = true
      rw [eqA_idx hP hinj hk hl, Bool.not_eq_true', beq_eq_false_iff_ne]
      exact e

include hMs hM hMc hrun htree hmt in
theorem nonabOK_of (h : nonabK MTK = true) : nonabOK mus 81 = true := by
  obtain ⟨-, -, -, hinj, -⟩ := run_facts hrun
  have hP := fun k (hk : k < 81) => PP_L hrun hk
  unfold nonabOK nonabK at *
  rw [pbBFS_eq hMs hM hMc hrun]
  obtain ⟨k, hk, hk'⟩ := anyN_iff.1 h
  obtain ⟨l, hl, hl'⟩ := anyN_iff.1 hk'
  rw [anyLt_iff']
  refine ⟨k, hk, ?_⟩
  rw [anyLt_iff']
  refine ⟨l, hl, ?_⟩
  change (!commA (LA LK)[k]! (LA LK)[l]!) = true
  rw [commA_idx hP hinj hmt hk hl, ← notB_eq]
  exact hl'

include hMs hM hMc hrun htree hmt in
theorem fixOK_of (h : ∀ c < 9, (allN 9 fun r => fixAt MTK FMK (Nat.add (Nat.mul 9 c) r)) = true) :
    fixOK mus 81 = true := by
  obtain ⟨hL0, -, -, hinj, -⟩ := run_facts hrun
  have hP := fun k (hk : k < 81) => PP_L hrun hk
  have hFM := (tree_facts htree).2.2.2
  have hfx : ∀ k < 81, fixAt MTK FMK k = true := fun k hk => by
    have a := allN_spec (h (k / 9) (by omega)) (k % 9) (Nat.mod_lt _ (by decide))
    have e : Nat.add (Nat.mul 9 (k / 9)) (k % 9) = k := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rwa [e] at a
  have hid := id_idx hL0
  have heq := fun a (ha : a < 81) b (hb : b < 81) => eqA_idx hP hinj (a := a) (b := b) ha hb
  have hex : ∀ k < 81, ∀ l < 81, pairEx (LA LK)[k]! (LA LK)[l]! = exK MTK k l := by
    intro k hk l hl
    unfold pairEx exK
    rw [hid, heq k hk 0 (by decide), heq l hl 0 (by decide), heq l hl k hk,
      comp_idx hP hmt hk hk, heq l hl _ (mt_facts hmt hk hk).1, commA_idx hP hinj hmt hk hl,
      orB_eq', orB_eq', orB_eq', orB_eq', notB_eq, nbeq', nbeq', nbeq', nbeq']
    simp only [Bool.or_assoc]
  unfold fixOK
  rw [pbBFS_eq hMs hM hMc hrun]
  simp only [Bool.and_eq_true, allLt_iff]
  have F : ∀ k < 81, (k = 0 ∨ pop (FMK k) ≤ 27) ∧ ∀ l < 81, exK MTK k l = true ∨
      (pop (Nat.land (FMK k) (FMK l)) ≤ 9 ∧ ∀ r < 81, cm MTK k r = false ∨ cm MTK l r = false ∨
        (∃ i < 3, ∃ j < 3, r = mt MTK (pwI MTK k i) (pwI MTK l j)) ∨
        pop (Nat.land (Nat.land (FMK k) (FMK l)) (FMK r)) ≤ 3) := by
    intro k hk
    have a := hfx k hk
    unfold fixAt at a
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
  · change (eqA 243 (LA LK)[k]! (idA 243) || decide (fix1 (LA LK)[k]! ≤ 27)) = true
    rw [hid, heq k hk 0 (by decide), fix1_eq hFM hk, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    exact (F k hk).1
  · change (pairEx (LA LK)[k]! (LA LK)[l]! || decide (fix2 (LA LK)[k]! (LA LK)[l]! ≤ 9)) = true
    rw [hex k hk l hl, fix2_eq hFM hk hl, Bool.or_eq_true, decide_eq_true_eq]
    rcases (F k hk).2 l hl with a | a
    · exact Or.inl a
    · exact Or.inr a.1
  · change (pairEx (LA LK)[k]! (LA LK)[l]! || allLt 81 fun r =>
      (!commA (LA LK)[k]! (LA LK)[r]! || !commA (LA LK)[l]! (LA LK)[r]! ||
      (anyLt 3 fun i => anyLt 3 fun j => eqA 243 (LA LK)[r]!
        (compA 243 (powA 243 (LA LK)[k]! i) (powA 243 (LA LK)[l]! j)))) ||
      decide (fix3 (LA LK)[k]! (LA LK)[l]! (LA LK)[r]! ≤ 3)) = true
    rw [hex k hk l hl, Bool.or_eq_true]
    rcases (F k hk).2 l hl with a | a
    · exact Or.inl a
    · right
      rw [allLt_iff]
      intro r hr
      rw [commA_idx hP hinj hmt hk hr, commA_idx hP hinj hmt hl hr, fix3_eq hFM hk hl hr]
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
        obtain ⟨pi, pil⟩ := pow_idx hP hL0 hmt hk hi
        obtain ⟨pj, pjl⟩ := pow_idx hP hL0 hmt hl hj
        rw [pi, pj, comp_idx hP hmt pil pjl, heq r hr _ (mt_facts hmt pil pjl).1, e]
        exact beq_self_eq_true _
      · exact Or.inr c

end CFSG.KC.Fi22RkS

end
