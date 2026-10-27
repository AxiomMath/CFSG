module

public import Certificates.Data.Kernel.PlusFrameK
public import CFSG.Certificates.Kernel.PlusQuandleSound

public section

namespace CFSG.KC.PlusFrameK

open CFSG.KD.PlusQuandle CFSG.KC.PlusQuandle CFSG.OddTranspositions.PartThree
open CFSG.OddTranspositions.PartThree.PlusFrame

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change (f n && allN n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h2 k h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem anyN_iff {n : Nat} {f : Nat → Bool} : anyN n f = true ↔ ∃ k < n, f k = true := by
  induction n with
  | zero => exact ⟨fun h => absurd (show false = true from h) Bool.false_ne_true,
      fun ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    change (f n || anyN n f) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h' | h'
      · exact Or.inr ⟨k, h', h⟩
      · exact Or.inl (h' ▸ h)

theorem rd_eq (P q : Nat) : rd P q = (P >>> (6 * q)) &&& (2 ^ 6 - 1) := rfl

theorem testBit_rd (P q i : Nat) : (rd P q).testBit i = (decide (i < 6) && P.testBit (6 * q + i)) := by
  rw [rd_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem rd_lt (P q : Nat) : rd P q < 64 := by
  rw [rd_eq]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem testBit_lt64 {v i : Nat} (hv : v < 64) (hi : 6 ≤ i) : v.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show v < 2 ^ 6 by omega)
    (Nat.pow_le_pow_right (n := 2) (by norm_num) hi))

theorem rd_wr {P p v q : Nat} (hv : v < 64) : rd (wr P p v) q = if q = p then v else rd P q := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hw : rd P p ^^^ v < 64 := Nat.xor_lt_two_pow (n := 6) (rd_lt P p) hv
  rw [testBit_rd, wr, Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hi : i < 6
  · simp only [hi, decide_true, Bool.true_and]
    split_ifs with hq
    · subst hq
      have e : 6 * q + i - 6 * q = i := by omega
      rw [e, Nat.testBit_xor, testBit_rd]
      simp [hi, show 6 * q + i ≥ 6 * q by omega]
    · rw [testBit_rd]
      simp only [hi, decide_true, Bool.true_and]
      rcases Nat.lt_or_gt_of_ne hq with h | h
      · simp [show ¬(6 * q + i ≥ 6 * p) by omega]
      · rw [testBit_lt64 hw (by omega)]
        simp
  · simp only [hi, decide_false, Bool.false_and]
    split_ifs
    · exact (testBit_lt64 hv (by omega)).symm
    · rw [testBit_rd]
      simp [hi]

theorem rd_zero (q : Nat) : rd 0 q = 0 := by
  rw [rd_eq, Nat.zero_shiftRight, Nat.zero_and]

theorem frame_vals : frameArr[(0 : Nat)]! = 18 ∧ frameArr[(1 : Nat)]! = 31 ∧
    frameArr[(2 : Nat)]! = 36 ∧ frameArr[(3 : Nat)]! = 41 := ⟨rfl, rfl, rfl, rfl⟩

theorem isFr_eq (p : Nat) : isFr p = isFrame p := by
  rw [Bool.eq_iff_iff]
  simp only [isFr, isFrame, Bool.or_eq_true, Nat.beq_eq, List.any_eq_true, List.mem_finRange,
    true_and, beq_iff_eq]
  constructor
  · rintro (((h | h) | h) | h) <;> subst h
    exacts [⟨0, frame_vals.1⟩, ⟨1, frame_vals.2.1⟩, ⟨2, frame_vals.2.2.1⟩, ⟨3, frame_vals.2.2.2⟩]
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl (Or.inl (hi.symm.trans frame_vals.1)))
    · exact Or.inl (Or.inl (Or.inr (hi.symm.trans frame_vals.2.1)))
    · exact Or.inl (Or.inr (hi.symm.trans frame_vals.2.2.1))
    · exact Or.inr (hi.symm.trans frame_vals.2.2.2)

theorem initV_eq (a b p : Nat) : initV a b p = initFun a b p := by
  unfold initV initFun
  rw [isFr_eq]
  cases isFrame p
  · by_cases h0 : p = 0
    · simp [h0]
    · by_cases h1 : p = 1
      · simp [h1]
      · simp [h0, h1, Nat.beq_eq]
  · simp

theorem initV_lt {a b p : Nat} (ha : a < 60) (hb : b < 60) (hp : p < 60) : initV a b p < 60 := by
  unfold initV
  cases isFr p
  · cases Nat.beq p 0
    · cases Nat.beq p 1 <;> simp [ha, hb]
    · simpa using ha
  · simpa using hp

theorem initK_rd {a b : Nat} (ha : a < 60) (hb : b < 60) :
    ∀ n ≤ 60, ∀ q, rd (initK a b n) q = if q < n then initV a b q else 0 := by
  intro n
  induction n with
  | zero => intro _ q; simp [initK, rd_zero]
  | succ n ih =>
    intro hn q
    have e : initK a b (n + 1) = wr (initK a b n) n (initV a b n) := by
      change force (initK a b n) (fun P => wr P n (initV a b n)) = _
      rw [force_eq]
    rw [e, rd_wr (by have := initV_lt ha hb (show n < 60 by omega); omega), ih (by omega)]
    split_ifs <;> first | rfl | omega | (subst_vars; rfl)

theorem plusT_eq {R : Nat → Nat} (hR : rowsOK R = true) {i j : Nat} (hi : i < 60) (hj : j < 60) :
    (plusTable[i]!)[j]! = tq R i j := (tq_spec hR hi hj).1

theorem ds_facts {DS : Nat → Nat} (h : dsOK DS = true) {k : Nat} (hk : k < 60) :
    derivOrder[k]! = lane 12 (DS 0) k ∧ derivSrc[k]! = lane 12 (DS 1) k ∧
      lane 12 (DS 0) k < 60 ∧ lane 12 (DS 1) k ≤ 3600 := by
  simp only [dsOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h4 := List.all_eq_true.1 h3 k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h4
  exact ⟨getElem!_of_map_eq h1 hk, getElem!_of_map_eq h2 hk, h4.1, h4.2⟩

theorem get_of_map {f : Array Nat} {P : Nat} (h : f.toList = (List.range 60).map (rd P)) {x : Nat}
    (hx : x < 60) : f[x]! = rd P x := getElem!_of_map_eq h.symm hx

theorem der_inv {R DS : Nat → Nat} (hR : rowsOK R = true) (hDS : dsOK DS = true) {a b : Nat}
    (ha : a < 60) (hb : b < 60) : ∀ k ≤ 60,
    (deriveFun a b (initArr a b) k).toList = (List.range 60).map (rd (derK R DS a b k)) ∧
      ∀ q < 60, rd (derK R DS a b k) q < 60 := by
  intro k
  induction k with
  | zero =>
    intro _
    have e : derK R DS a b 0 = initK a b 60 := rfl
    rw [e]
    refine ⟨?_, fun q hq => ?_⟩
    · simp only [deriveFun, initArr, List.toList_toArray]
      apply List.map_congr_left
      intro q hq
      rw [initK_rd ha hb 60 le_rfl, if_pos (List.mem_range.1 hq), initV_eq]
    · rw [initK_rd ha hb 60 le_rfl, if_pos hq]
      exact initV_lt ha hb hq
  | succ k ih =>
    intro hk
    obtain ⟨hf, hbd⟩ := ih (by omega)
    obtain ⟨eo, es, ho, hs⟩ := ds_facts hDS (show k < 60 by omega)
    set P := derK R DS a b k with hP
    set o := lane 12 (DS 0) k
    set s := lane 12 (DS 1) k
    have hx : (s - 1) / 60 < 60 := by omega
    have hy : (s - 1) % 60 < 60 := Nat.mod_lt _ (by norm_num)
    set v := cond (Nat.beq s 0) (initV a b o) (tq R (rd P ((s - 1) / 60)) (rd P ((s - 1) % 60)))
      with hv
    have hv60 : v < 60 := by
      rw [hv]
      cases Nat.beq s 0
      · exact (tq_spec hR (hbd _ hx) (hbd _ hy)).2
      · exact initV_lt ha hb ho
    have eK : derK R DS a b (k + 1) = wr P o v := by
      change force P (fun P => stepK R a b P o s) = _
      rw [force_eq]
      rfl
    have eV : stepVal a b (deriveFun a b (initArr a b) k) k = v := by
      unfold stepVal
      rw [es, eo]
      by_cases h0 : s = 0
      · rw [if_pos h0, hv, h0, ← initV_eq]
        rfl
      · have hb0 : Nat.beq s 0 = false := by
          cases h : Nat.beq s 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) h0
        rw [if_neg h0, hv, hb0]
        simp only [cond_false]
        rw [get_of_map hf hx, get_of_map hf hy, plusT_eq hR (hbd _ hx) (hbd _ hy)]
    have eD : deriveFun a b (initArr a b) (k + 1) =
        (deriveFun a b (initArr a b) k).set! o v := by
      rw [deriveFun, eV, eo]
    rw [eK, eD]
    refine ⟨?_, fun q hq => ?_⟩
    · rw [Array.set!, Array.toList_setIfInBounds, hf]
      apply List.ext_getElem
      · simp
      · intro q h1 h2
        simp only [List.getElem_set, List.getElem_map, List.getElem_range]
        rw [rd_wr (by omega)]
        by_cases h3 : q = o
        · subst h3
          simp
        · simp [h3, Ne.symm h3]
    · rw [rd_wr (by omega)]
      split_ifs
      · exact hv60
      · exact hbd q hq

theorem hom_eq {R : Nat → Nat} (hR : rowsOK R = true) {f : Array Nat} {P : Nat}
    (hf : f.toList = (List.range 60).map (rd P)) (hb : ∀ q < 60, rd P q < 60) :
    isTableHomArr f = homK R P := by
  rw [Bool.eq_iff_iff, homK, allN_iff]
  unfold isTableHomArr
  rw [List.all_eq_true]
  have key : ∀ i < 60, ∀ j < 60,
      (f[(plusTable[i]!)[j]!]! == (plusTable[f[i]!]!)[f[j]!]!) =
        Nat.beq (rd P (tq R i j)) (tq R (rd P i) (rd P j)) := by
    intro i hi j hj
    have ht := (tq_spec hR hi hj).2
    rw [plusT_eq hR hi hj, get_of_map hf ht, get_of_map hf hi, get_of_map hf hj,
      plusT_eq hR (hb i hi) (hb j hj)]
    rfl
  constructor
  · intro h i hi
    rw [allN_iff]
    intro j hj
    rw [← key i hi j hj]
    exact List.all_eq_true.1 (h i (List.mem_range.2 hi)) j (List.mem_range.2 hj)
  · intro h i hi
    rw [List.all_eq_true]
    intro j hj
    rw [key i (List.mem_range.1 hi) j (List.mem_range.1 hj)]
    exact allN_iff.1 (h i (List.mem_range.1 hi)) j (List.mem_range.1 hj)

theorem match_eq {DA : Nat → Nat} (hDA : daOK DA = true) {f : Array Nat} {P : Nat}
    (hf : f.toList = (List.range 60).map (rd P)) :
    ((dActions ()).any fun g => matchesArr f g) = matchK DA P := by
  simp only [daOK, beq_iff_eq] at hDA
  rw [Bool.eq_iff_iff, matchK, anyN_iff, List.any_eq_true]
  have hm : ∀ (g : Array Nat) (k : Nat), g.toList = (List.range 60).map (rd (DA k)) →
      (matchesArr f g = true ↔ ∀ p < 60, rd P p = rd (DA k) p) := by
    intro g k hg
    unfold matchesArr
    rw [List.all_eq_true]
    constructor
    · intro h p hp
      have := h p (List.mem_range.2 hp)
      rw [get_of_map hf hp, get_of_map hg hp, beq_iff_eq] at this
      exact this
    · intro h p hp
      rw [get_of_map hf (List.mem_range.1 hp), get_of_map hg (List.mem_range.1 hp), beq_iff_eq]
      exact h p (List.mem_range.1 hp)
  constructor
  · rintro ⟨g, hg, hmg⟩
    have : g.toList ∈ (dActions ()).map Array.toList := List.mem_map_of_mem hg
    rw [← hDA, List.mem_map] at this
    obtain ⟨k, hk, hgk⟩ := this
    exact ⟨k, List.mem_range.1 hk, by rw [allN_iff]; intro p hp; rw [Nat.beq_eq]; exact (hm g k hgk.symm).1 hmg p hp⟩
  · rintro ⟨k, hk, hall⟩
    have : (List.range 60).map (rd (DA k)) ∈ (dActions ()).map Array.toList := by
      rw [← hDA]
      exact List.mem_map_of_mem (List.mem_range.2 hk)
    rw [List.mem_map] at this
    obtain ⟨g, hg, hgk⟩ := this
    refine ⟨g, hg, (hm g k hgk).2 fun p hp => ?_⟩
    have := allN_iff.1 hall p hp
    rwa [Nat.beq_eq] at this

theorem autCheck_of {R DS DA : Nat → Nat} (hR : rowsOK R = true) (hDS : dsOK DS = true)
    (hDA : daOK DA = true) (h : ∀ a < 60, autK R DS DA a = true) : autCheck () = true := by
  unfold autCheck
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  obtain ⟨hf, hbd⟩ := der_inv hR hDS ha' hb' 60 le_rfl
  have hk := allN_iff.1 (h a ha') b hb'
  rw [force_eq] at hk
  change (!(isTableHomArr (deriveFun a b (initArr a b) 60)) ||
    ((dActions ()).any fun g => matchesArr (deriveFun a b (initArr a b) 60) g)) = true
  rw [hom_eq hR hf hbd, match_eq hDA hf]
  exact hk

theorem autK_of_autOK {R DS DA : Nat → Nat} {lo hi a : Nat} (h : autOK R DS DA lo hi = true)
    (hlo : lo ≤ a) (hhi : a < hi) : autK R DS DA a = true := by
  have := allN_iff.1 h (a - lo) (by omega)
  rwa [Nat.add_sub_cancel' hlo] at this

end CFSG.KC.PlusFrameK
