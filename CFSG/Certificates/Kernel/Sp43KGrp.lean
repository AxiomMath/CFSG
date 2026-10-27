module

public import Certificates.Data.Kernel.Sp43KSp
public import CFSG.Certificates.Kernel.Sp43KListSound
public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Group

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43 CFSG.Sp43.Native

@[expose] def InG (t : ℕ) : Prop := ExT t ∧ toMT t ∈ Matrix.symplecticGroup (Fin 2) (ZMod 3)

noncomputable def ofT (t : ℕ) : G := by
  classical exact if h : InG t then ⟨toMT t, h.2⟩ else 1

theorem coe_ofT {t : ℕ} (h : InG t) :
    ((ofT t : G) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) = toMT t := by
  unfold ofT
  rw [dif_pos h]

theorem inG_oneT : InG oneT := ⟨exT_oneT, by rw [toMT_oneT]; exact Submonoid.one_mem _⟩

theorem inG_mulT {a b : ℕ} (ha : InG a) (hb : InG b) : InG (mulT a b) :=
  ⟨exT_mulT ha.1 hb.1, by rw [toMT_mulT ha.1 hb.1]; exact Submonoid.mul_mem _ ha.2 hb.2⟩

theorem ofT_oneT : ofT oneT = 1 := by
  apply Subtype.ext
  rw [coe_ofT inG_oneT, toMT_oneT]
  rfl

theorem ofT_mulT {a b : ℕ} (ha : InG a) (hb : InG b) : ofT (mulT a b) = ofT a * ofT b := by
  apply Subtype.ext
  rw [coe_ofT (inG_mulT ha hb), toMT_mulT ha.1 hb.1, Submonoid.coe_mul, coe_ofT ha, coe_ofT hb]

theorem ofT_inj {a b : ℕ} (ha : InG a) (hb : InG b) (ha' : okT a = true) (hb' : okT b = true)
    (h : ofT a = ofT b) : a = b := by
  apply toMT_inj ha' hb'
  rw [← coe_ofT ha, ← coe_ofT hb, h]

theorem toMT_eq_toM (t : ℕ) : toMT t = toM (toCT t) := by
  ext x y
  simp only [toMT, toM, ent, toCT, dig_horner, List.getD_eq_getElem?_getD, val2, testBit_high]
  have hn : 4 * ix x + ix y < 16 := by
    rcases x with i | i <;> rcases y with j | j <;> simp only [ix] <;> omega
  rw [List.getElem?_map, List.getElem?_range hn]
  simp only [Option.map_some, Option.getD_some, digT]
  split_ifs <;> rfl

private theorem mem_spCodes_rows (c : ℕ) (hc : c < 3 ^ 16)
    (h23 : omg (c / 6561 % 81) (c / 531441 % 81) = 0)
    (h12 : omg (c / 81 % 81) (c / 6561 % 81) = 0)
    (h13 : omg (c / 81 % 81) (c / 531441 % 81) = 2)
    (h01 : omg (c % 81) (c / 81 % 81) = 0) (h02 : omg (c % 81) (c / 6561 % 81) = 2)
    (h03 : omg (c % 81) (c / 531441 % 81) = 0) : c ∈ spCodes () := by
  simp only [spCodes, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range,
    Bool.and_eq_true, beq_iff_eq]
  norm_num at hc
  exact ⟨c / 531441 % 81, by omega, c / 6561 % 81, ⟨by omega, h23⟩, c / 81 % 81,
    ⟨by omega, h12, h13⟩, c % 81, ⟨by omega, ⟨h01, h02⟩, h03⟩, by omega⟩

theorem inG_of_spT {t : ℕ} (ho : okT t = true) (hs : spT t = true) : InG t := by
  refine ⟨(okT_spec ho).1, ?_⟩
  simp only [spT, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨h23, h12⟩, h13⟩, h01⟩, h02⟩, h03⟩ := hs
  have hc : toCT t < 3 ^ 16 := lt_of_lt_of_eq (horner_lt _) (by simp)
  rw [toMT_eq_toM]
  exact ((mem_spCodes_iff _).1 (mem_spCodes_rows _ hc h23 h12 h13 h01 h02 h03)).2

@[expose] noncomputable def sub2T (a b : ℕ) : Subgroup G := Subgroup.closure {ofT a, ofT b}

private theorem genT_spec {a b : ℕ} (ha : InG a) (hb : InG b) {l : ℕ} (hl : l < 2) :
    InG (genT a b l) ∧ ofT (genT a b l) ∈ sub2T a b := by
  interval_cases l
  · exact ⟨ha, Subgroup.subset_closure (by simp [genT])⟩
  · exact ⟨hb, Subgroup.subset_closure (by simp [genT])⟩

private theorem lstOne_parts {a b n P D i : ℕ} {r : ℕ × ℕ × ℕ × ℕ}
    (h : lstOne a b n P D i r = true) :
    okT (fldT P i) = true ∧ (i + 1 = n ∨ fldT P i < fldT P (i + 1)) ∧
      ((fldT D i = 0 ∧ fldT P i = oneT) ∨
        (((r.1 < n ∧ r.2.1 < 2) ∧ fldT D r.1 < fldT D i) ∧
          fldT P i = mulT (fldT P r.1) (genT a b r.2.1))) ∧
      r.2.2.1 < n ∧ fldT P r.2.2.1 = mulT (fldT P i) a ∧
      r.2.2.2 < n ∧ fldT P r.2.2.2 = mulT (fldT P i) b := by
  simp only [lstOne, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

private theorem pow_mem_of_mul_mem (S : Set G) (x : G) (hx : ∀ y ∈ S, y * x ∈ S) (k : ℕ) :
    ∀ y ∈ S, y * x ^ k ∈ S := by
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih => intro y hy; rw [pow_succ, ← mul_assoc]; exact hx _ (ih y hy)

private theorem inv_mem_of_mul_mem (S : Set G) (x : G) (hx : ∀ y ∈ S, y * x ∈ S) :
    ∀ y ∈ S, y * x⁻¹ ∈ S := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h1 : x * x ^ (Nat.card G - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_card_eq_one']
  rw [inv_eq_of_mul_eq_one_right h1]
  exact pow_mem_of_mul_mem S x hx _

theorem lst_spec {a b n P D : ℕ} {R : ℕ → ℕ × ℕ × ℕ × ℕ} (ha : InG a) (hb : InG b)
    (hn : 0 < n) (h : ∀ i < n, lstOne a b n P D i (R i) = true) :
    (∀ i < n, okT (fldT P i) = true ∧ InG (fldT P i)) ∧
      (∀ i < n, ∀ j < n, fldT P i = fldT P j → i = j) ∧
      (∀ x, x ∈ sub2T a b ↔ ∃ i < n, ofT (fldT P i) = x) ∧ Nat.card (sub2T a b) = n := by
  have hp := fun i hi => lstOne_parts (h i hi)
  have hmem : ∀ i < n, InG (fldT P i) ∧ ofT (fldT P i) ∈ sub2T a b := by
    suffices H : ∀ d i, i < n → fldT D i = d → InG (fldT P i) ∧ ofT (fldT P i) ∈ sub2T a b from
      fun i hi => H _ i hi rfl
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd
      obtain ⟨-, -, htree, -⟩ := hp i hi
      rcases htree with ⟨-, h1⟩ | ⟨⟨⟨hr, hl⟩, hlt⟩, heq⟩
      · rw [h1, ofT_oneT]
        exact ⟨inG_oneT, Subgroup.one_mem _⟩
      · obtain ⟨hs, hm⟩ := ih _ (by omega) _ hr rfl
        obtain ⟨hgs, hgm⟩ := genT_spec ha hb hl
        rw [heq, ofT_mulT hs hgs]
        exact ⟨inG_mulT hs hgs, Subgroup.mul_mem _ hm hgm⟩
  have hlt : ∀ j, ∀ i, i < j → j < n → fldT P i < fldT P j := by
    intro j
    induction j with
    | zero => intro i hij; omega
    | succ j ih =>
      intro i hij hj
      have hstep : fldT P j < fldT P (j + 1) := by
        rcases (hp j (by omega)).2.1 with e | e
        · omega
        · exact e
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact (ih i h' (by omega)).trans hstep
      · exact hstep
  have hinj : ∀ i < n, ∀ j < n, fldT P i = fldT P j → i = j := by
    intro i hi j hj e
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact absurd e (hlt j i h1 hj).ne
    · exact h1
    · exact absurd e.symm (hlt i j h1 hi).ne
  set S : Set G := {x | ∃ i < n, ofT (fldT P i) = x}
  have hgen : ∀ l < 2, ∀ y ∈ S, y * ofT (genT a b l) ∈ S := by
    rintro l hl _ ⟨i, hi, rfl⟩
    obtain ⟨-, -, -, hqa, ea, hqb, eb⟩ := hp i hi
    interval_cases l
    · refine ⟨_, hqa, ?_⟩
      rw [ea, ofT_mulT (hmem i hi).1 ha]
      rfl
    · refine ⟨_, hqb, ?_⟩
      rw [eb, ofT_mulT (hmem i hi).1 hb]
      rfl
  have key : ∀ x ∈ sub2T a b, ∀ y ∈ S, y * x ∈ S := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {ofT a, ofT b} := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hgen 0 (by norm_num)
      · exact hgen 1 (by norm_num)
    | one => intro y hy; simpa using hy
    | mul x y _ _ hx hy => intro z hz; rw [← mul_assoc]; exact hy _ (hx z hz)
    | inv x _ hx => exact inv_mem_of_mul_mem S x hx
  have hiff : ∀ x, x ∈ sub2T a b ↔ ∃ i < n, ofT (fldT P i) = x := by
    intro x
    constructor
    · intro hx
      have h0 := (hmem 0 hn).2
      have := key _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h0) hx) _ ⟨0, hn, rfl⟩
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at this
    · rintro ⟨i, hi, rfl⟩
      exact (hmem i hi).2
  refine ⟨fun i hi => ⟨(hp i hi).1, (hmem i hi).1⟩, hinj, hiff, ?_⟩
  have hbij : Function.Bijective (fun i : Fin n =>
      (⟨ofT (fldT P i), (hmem i i.2).2⟩ : sub2T a b)) := by
    constructor
    · intro i j hij
      exact Fin.ext (hinj i i.2 j j.2 (ofT_inj (hmem i i.2).1 (hmem j j.2).1 (hp i i.2).1
        (hp j j.2).1 (congrArg Subtype.val hij)))
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, hix⟩ := (hiff x).1 hx
      exact ⟨⟨i, hi⟩, Subtype.ext hix⟩
  exact (Nat.card_eq_of_bijective _ hbij).symm.trans (Nat.card_fin n)

theorem lstK_spec {a b n P D s e : ℕ} {R : List (ℕ × ℕ × ℕ × ℕ)}
    (h : lstK a b n P D s e R = true) :
    okT a = true ∧ okT b = true ∧ ∀ i, s ≤ i → i < e →
      i < n ∧ lstOne a b n P D i (R.getD (i - s) (0, 0, 0, 0)) = true := by
  simp only [lstK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, (lstGo_spec R s h3).2⟩

end CFSG.KC.Sp43K

end
