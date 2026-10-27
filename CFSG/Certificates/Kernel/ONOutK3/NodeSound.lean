module

public import Certificates.Data.Kernel.ONOutK3.Check
public import CFSG.Certificates.Kernel.ONOutK3.Bfs3
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KS.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3 CFSG.KS.Bfs3 CFSG.KS.BfsReplay
open CFSG.ComponentClassification.SolMax.ONOut

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem band_t {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem bif_t {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c <;> simp_all

theorem beqT {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem bltT {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem bleT {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem beqTr {a b : Nat} (h : a = b) : Nat.beq a b = true := by subst h; exact Nat.beq_refl a

theorem bltTr {a b : Nat} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem beqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem bltF {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (bltT e) h

theorem allBlk_iff (b : Nat) (f : Nat → Bool) (len : Nat) :
    allBlk b f len = true ↔ ∀ l < len, f (b + l) = true := by
  induction len with
  | zero => simp [allBlk]
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f n) (f (Nat.add b n)) = true ↔ _
    constructor
    · intro h l hl
      obtain ⟨h1, h2⟩ := band_t h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact (ih.1 h2) l h
      · subst h
        exact h1
    · intro h
      have e : f (Nat.add b n) = true := h n (Nat.lt_succ_self n)
      rw [e]
      exact ih.2 fun l hl => h l (Nat.lt_succ_of_lt hl)

theorem shr_eq (r n : Nat) : Nat.shiftRight r n = r / 2 ^ n := Nat.shiftRight_eq_div_pow r n

theorem shl_eq (r n : Nat) : Nat.shiftLeft r n = r * 2 ^ n := Nat.shiftLeft_eq r n

theorem land_mod (x n : Nat) : Nat.land x (2 ^ n - 1) = x % 2 ^ n :=
  Nat.and_two_pow_sub_one_eq_mod x n

theorem M18_eq : M18 = 2 ^ 18 - 1 := rfl
theorem M54_eq : M54 = 2 ^ 54 - 1 := rfl

theorem tA_eq (r : Nat) : tA r = r % 2 ^ 18 := by
  unfold tA
  rw [M18_eq, land_mod, shr_eq, Nat.pow_zero, Nat.div_one]

theorem tB_eq (r : Nat) : tB r = r / 2 ^ 18 % 2 ^ 18 := by
  unfold tB
  rw [M18_eq, land_mod, shr_eq]

theorem tC_eq (r : Nat) : tC r = r / 2 ^ 36 % 2 ^ 18 := by
  unfold tC
  rw [M18_eq, land_mod, shr_eq]

theorem tK_eq (r : Nat) : tK r = r % 2 ^ 54 := by
  unfold tK
  rw [M54_eq, land_mod, shr_eq, Nat.pow_zero, Nat.div_one]

theorem tK_split (r : Nat) : tK r = tA r + 2 ^ 18 * tB r + 2 ^ 36 * tC r := by
  rw [tK_eq, tA_eq, tB_eq, tC_eq]
  omega

@[expose] noncomputable def Tn (R : Nat → Nat) (k : Nat) : Pt3 :=
  (tA (nrec R k), tB (nrec R k), tC (nrec R k))

@[expose] def stepG (G : Nat → Nat → Nat) (l : Nat) (t : Pt3) : Pt3 := map3 (G l) t

theorem tK_of_Tn {R : Nat → Nat} {a b : Nat} (h : Tn R a = Tn R b) :
    tK (nrec R a) = tK (nrec R b) := by
  unfold Tn at h
  simp only [Prod.mk.injEq] at h
  rw [tK_split, tK_split, h.1, h.2.1, h.2.2]

theorem BK_triple {r : Nat} (h : tK r = BK) : (tA r, tB r, tC r) = base3 := by
  have hA : tA r = tK r % 2 ^ 18 := by rw [tA_eq, tK_eq]; omega
  have hB : tB r = tK r / 2 ^ 18 % 2 ^ 18 := by rw [tB_eq, tK_eq]; omega
  have hC : tC r = tK r / 2 ^ 36 % 2 ^ 18 := by rw [tC_eq, tK_eq]; omega
  rw [hA, hB, hC, h]
  rfl

variable {G : Nat → Nat → Nat} {R SR : Nat → Nat} {UL UW : Nat → Nat} {FK : Nat}
  {TC : Nat → Nat}

theorem close_spec {k r j : Nat} (h : closeOK G R k r j = true) :
    posF r j < CNT ∧ G j (tA r) = tA (nrec R (posF r j)) ∧ G j (tB r) = tB (nrec R (posF r j)) ∧
      G j (tC r) = tC (nrec R (posF r j)) ∧
      (posF r j = 0 ∨ parF (nrec R (posF r j)) < k ∨
        (parF (nrec R (posF r j)) = k ∧ labF (nrec R (posF r j)) ≤ j)) := by
  unfold closeOK at h
  simp only [sB] at h
  obtain ⟨h1, h⟩ := band_t h
  obtain ⟨h2, h⟩ := band_t h
  obtain ⟨h3, h⟩ := band_t h
  obtain ⟨h4, h5⟩ := band_t h
  refine ⟨bltT h1, beqT h2, beqT h3, beqT h4, ?_⟩
  by_cases e0 : posF r j = 0
  · exact Or.inl e0
  · have := (bif_t h5).2 (beqF e0)
    by_cases e1 : parF (nrec R (posF r j)) < k
    · exact Or.inr (Or.inl e1)
    · have h6 := (bif_t this).2 (bltF e1)
      obtain ⟨a, b⟩ := band_t h6
      exact Or.inr (Or.inr ⟨beqT a, bleT b⟩)

structure NodeAt (G : Nat → Nat → Nat) (R : Nat → Nat) (UL UW : Nat → Nat) (FK k : Nat) : Prop where
  ltA : tA (nrec R k) < NP
  ltB : tB (nrec R k) < NP
  ltC : tC (nrec R k) < NP
  close : ∀ j < 3, closeOK G R k (nrec R k) j = true
  root : k = 0 → tK (nrec R k) = BK ∧ parF (nrec R k) = 0 ∧ labF (nrec R k) = 0 ∧
    sigF (nrec R k) = 0 ∧ depF (nrec R k) = 0 ∧ wrdF (nrec R k) = 0
  tree : k ≠ 0 → parF (nrec R k) < k ∧ labF (nrec R k) < 3 ∧
    posF (nrec R (parF (nrec R k))) (labF (nrec R k)) = k ∧
    depF (nrec R k) = Nat.succ (depF (nrec R (parF (nrec R k)))) ∧
    wrdF (nrec R k) = wrdF (nrec R (parF (nrec R k))) +
      labF (nrec R k) * 2 ^ (2 * depF (nrec R (parF (nrec R k)))) ∧
    sigF (nrec R k) = walk R (UL (labF (nrec R k))) (UW (labF (nrec R k)))
      (sigF (nrec R (parF (nrec R k))))
  order : k ≠ 0 → k + 1 < CNT →
    lexB (parF (nrec R k)) (labF (nrec R k)) (parF (nrec R (k + 1))) (labF (nrec R (k + 1))) = true
  cover : sigF (nrec R k) = k → memK FK 120 (tK (nrec R k)) = true

theorem nodeAt_of {k : Nat} (h : nodeOK G R UL UW FK k = true) : NodeAt G R UL UW FK k := by
  unfold nodeOK at h
  rw [sB] at h
  obtain ⟨hA, h⟩ := band_t h
  obtain ⟨hB, h⟩ := band_t h
  obtain ⟨hC, h⟩ := band_t h
  obtain ⟨c0, h⟩ := band_t h
  obtain ⟨c1, h⟩ := band_t h
  obtain ⟨c2, h⟩ := band_t h
  obtain ⟨ht, h⟩ := band_t h
  obtain ⟨ho, hc⟩ := band_t h
  refine ⟨bltT hA, bltT hB, bltT hC, fun j hj => ?_, fun e => ?_,
    fun e => ?_, fun e he => ?_, fun e => ?_⟩
  · interval_cases j <;> assumption
  · unfold treeAt at ht
    have h0 := (bif_t ht).1 (beqTr e)
    obtain ⟨a1, h0⟩ := band_t h0
    obtain ⟨a2, h0⟩ := band_t h0
    obtain ⟨a3, h0⟩ := band_t h0
    obtain ⟨a4, h0⟩ := band_t h0
    obtain ⟨a5, a6⟩ := band_t h0
    exact ⟨beqT a1, beqT a2, beqT a3, beqT a4, beqT a5,
      beqT a6⟩
  · unfold treeAt at ht
    have h1 := (bif_t ht).2 (beqF e)
    simp only [sB] at h1
    obtain ⟨a1, h1⟩ := band_t h1
    obtain ⟨a2, h1⟩ := band_t h1
    obtain ⟨a3, h1⟩ := band_t h1
    obtain ⟨a4, h1⟩ := band_t h1
    obtain ⟨a5, a6⟩ := band_t h1
    refine ⟨bltT a1, bltT a2, beqT a3, beqT a4, ?_, beqT a6⟩
    have a5' := beqT a5
    rw [a5']
    change Nat.add _ (Nat.shiftLeft _ (Nat.mul 2 _)) = _
    rw [shl_eq]
    rfl
  · unfold orderAt at ho
    have h1 := (bif_t ho).2 (beqF e)
    have h2 := (bif_t h1).1 (bltTr he)
    rw [sB] at h2
    exact h2
  · exact (bif_t hc).1 (beqTr e)

theorem nodes_of (hN : ∀ s < 315, sliceOK G R UL UW FK TC s = true) {k : Nat} (hk : k < CNT) :
    NodeAt G R UL UW FK k := by
  have hs := hN (k / 512) (by change k < 161280 at hk; omega)
  unfold sliceOK at hs
  have := (allBlk_iff _ _ _).1 (band_t hs).1 (k % 512) (Nat.mod_lt _ (by norm_num))
  rw [show Nat.mul (k / 512) 512 + k % 512 = k by
    change k / 512 * 512 + k % 512 = k; omega] at this
  exact nodeAt_of this

theorem counts_of (hN : ∀ s < 315, sliceOK G R UL UW FK TC s = true) {s : Nat} (hs : s < 315) :
    sumBlk (Nat.mul s 512) (tVal R) 512 = TC s := by
  have h := hN s hs
  unfold sliceOK at h
  exact beqT (band_t h).2

theorem sort_spec (hS : ∀ s < 64, sortSl R SR s = true) {i : Nat} (hi : i < CNT) :
    fld(srec SR i, nat_lit 54, M18) < CNT ∧
      fld(srec SR i, nat_lit 0, M54) = tK (nrec R (fld(srec SR i, nat_lit 54, M18))) ∧
      (i + 1 < CNT → fld(srec SR i, nat_lit 0, M54) < fld(srec SR (i + 1), nat_lit 0, M54)) := by
  have hs := hS (i / 2520) (by change i < 161280 at hi; omega)
  unfold sortSl at hs
  have h := (allBlk_iff _ _ _).1 hs (i % 2520) (Nat.mod_lt _ (by norm_num))
  rw [show Nat.mul (i / 2520) 2520 + i % 2520 = i by
    change i / 2520 * 2520 + i % 2520 = i; omega] at h
  unfold sortOK at h
  rw [sB, sB] at h
  obtain ⟨h1, h⟩ := band_t h
  obtain ⟨h2, h3⟩ := band_t h
  refine ⟨bltT h1, beqT h2, fun hi1 => ?_⟩
  exact bltT ((bif_t h3).1 (bltTr hi1))

theorem sort_inj (hS : ∀ s < 64, sortSl R SR s = true) :
    ∀ a < CNT, ∀ b < CNT, tK (nrec R a) = tK (nrec R b) → a = b := by
  let key := fun i => fld(srec SR i, nat_lit 54, M18)
  let kv := fun i => fld(srec SR i, nat_lit 0, M54)
  have hmono : ∀ i j, i < j → j < CNT → kv i < kv j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact Nat.lt_trans (ih h (by omega)) ((sort_spec hS (by omega)).2.2 hj)
      · subst h
        exact (sort_spec hS (by omega)).2.2 hj
  have hinj : ∀ i < CNT, ∀ j < CNT, key i = key j → i = j := by
    intro i hi j hj e
    by_contra hne
    have hk : kv i = kv j := by
      change fld(srec SR i, nat_lit 0, M54) = fld(srec SR j, nat_lit 0, M54)
      rw [(sort_spec hS hi).2.1, (sort_spec hS hj).2.1]
      exact congrArg (fun x => tK (nrec R x)) e
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd hk (Nat.ne_of_lt (hmono i j h hj))
    · exact absurd hk.symm (Nat.ne_of_lt (hmono j i h hi))
  have hsurj : ∀ a < CNT, ∃ i < CNT, key i = a := by
    intro a ha
    obtain ⟨i, hi, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range CNT)
      (t := Finset.range CNT) (fun i _ => key i)
      (fun i hi => Finset.mem_range.2 (sort_spec hS (Finset.mem_range.1 hi)).1)
      (fun i j hi hj e => hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e)
      le_rfl a (Finset.mem_range.2 ha)
    exact ⟨i, Finset.mem_range.1 hi, e.symm⟩
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  obtain ⟨j, hj, rfl⟩ := hsurj b hb
  have : kv i = kv j := by
    change fld(srec SR i, nat_lit 0, M54) = fld(srec SR j, nat_lit 0, M54)
    rw [(sort_spec hS hi).2.1, (sort_spec hS hj).2.1]
    exact e
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd this (Nat.ne_of_lt (hmono i j h hj))
  · rw [h]
  · exact absurd this.symm (Nat.ne_of_lt (hmono j i h hi))

theorem pos_spec (hN : ∀ s < 315, sliceOK G R UL UW FK TC s = true) {h : Nat} (hh : h < CNT)
    {j : Nat} (hj : j < 3) :
    posF (nrec R h) j < CNT ∧ stepG G j (Tn R h) = Tn R (posF (nrec R h) j) ∧
      (posF (nrec R h) j = 0 ∨ parF (nrec R (posF (nrec R h) j)) < h ∨
        (parF (nrec R (posF (nrec R h) j)) = h ∧ labF (nrec R (posF (nrec R h) j)) ≤ j)) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := close_spec ((nodes_of hN hh).close j hj)
  refine ⟨a1, ?_, a5⟩
  unfold stepG Tn map3
  rw [a2, a3, a4]

theorem node_replay (hN : ∀ s < 315, sliceOK G R UL UW FK TC s = true)
    (hS : ∀ s < 64, sortSl R SR s = true) :
    R3 (stepG G) 3 base3 161280 (Tn R) (fun k => parF (nrec R k)) (fun k => labF (nrec R k))
      (fun h j => posF (nrec R h) j) := by
  have h0 := (nodes_of hN (k := 0) (by decide)).root rfl
  refine ⟨by norm_num, ?_, h0.2.1, h0.2.2.1, fun a ha b hb e => sort_inj hS a ha b hb (tK_of_Tn e),
    fun i hi0 hi => ?_, fun i hi0 hi => ?_, fun h hh j hj => ?_⟩
  · exact BK_triple h0.1
  · obtain ⟨t1, t2, t3, -⟩ := (nodes_of hN hi).tree (by omega)
    refine ⟨t1, t2, ?_⟩
    have := (pos_spec hN (h := parF (nrec R i)) (by change parF (nrec R i) < 161280; omega) t2).2.1
    rw [t3] at this
    exact this.symm
  · have := (nodes_of hN (k := i) (by change i < 161280; omega)).order (by omega)
      (by change i + 1 < 161280; exact hi)
    unfold lexB at this
    unfold LexLt
    by_cases e : parF (nrec R i) < parF (nrec R (i + 1))
    · exact Or.inl e
    · obtain ⟨a, b⟩ := band_t ((bif_t this).2 (bltF e))
      exact Or.inr ⟨beqT a, bltT b⟩
  · obtain ⟨p1, p2, p3⟩ := pos_spec hN hh hj
    refine ⟨p1, p2, ?_⟩
    rcases p3 with e | e | ⟨e1, e2⟩
    · exact Or.inl e
    · right
      unfold LexLt
      omega
    · right
      unfold LexLt
      omega

end CFSG.KS.ONK3

end
