module

public import CFSG.Certificates.Kernel.O8OrthMatProved
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.KC.O8.DickPf

open Matrix Module QuadraticMap CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8 CFSG.KC.O8.OrthPf
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain
  CFSG.RankThree.OrthogonalInvolutions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Vd := Fin 6 → ZMod 2

@[expose] def ofVec (v : Vd) : ℕ := bitsOf 6 fun j => if h : j < 6 then v ⟨j, h⟩ == 1 else false

theorem testBit_ofVec (v : Vd) (j : ℕ) :
    (ofVec v).testBit j = if h : j < 6 then v ⟨j, h⟩ == 1 else false := by
  rw [ofVec, testBit_bitsOf]
  by_cases h : j < 6 <;> simp [h]

theorem ofVec_lt (v : Vd) : ofVec v < 64 := by
  have : ofVec v < 2 ^ 6 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [testBit_ofVec, dif_neg (by omega)]
  simpa using this

theorem dtoVec_ofVec (v : Vd) : toVec 6 (ofVec v) = v := by
  funext j
  rw [toVec, testBit_ofVec, dif_pos j.isLt, bz_beq_one]

theorem testBit_lt64 {x : ℕ} (hx : x < 64) {i : ℕ} (hi : 6 ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hi : 2 ^ 6 ≤ 2 ^ i))

theorem ofVec_toVec {x : ℕ} (hx : x < 64) : ofVec (toVec 6 x) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofVec]
  by_cases hi : i < 6
  · rw [dif_pos hi]
    change (bz (x.testBit i) == 1) = x.testBit i
    cases x.testBit i <;> rfl
  · rw [dif_neg hi, testBit_lt64 hx (by omega)]

theorem dtoVec_inj {x y : ℕ} (hx : x < 64) (hy : y < 64) (h : toVec 6 x = toVec 6 y) : x = y := by
  rw [← ofVec_toVec hx, ← ofVec_toVec hy, h]

theorem dtoVec_xor (x y : ℕ) : toVec 6 (x ^^^ y) = toVec 6 x + toVec 6 y := by
  funext j
  simp only [toVec, Nat.testBit_xor, bz_xor, Pi.add_apply]

theorem dtoVec_zero : toVec 6 0 = 0 := by
  funext j
  simp [toVec]

theorem dtoVec_two_pow (j : Fin 6) : toVec 6 (2 ^ (j : ℕ)) = Pi.single j 1 := by
  funext i
  rw [toVec, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have : (j : ℕ) ≠ i := fun e => h (Fin.ext e.symm)
    simp [this, h]

theorem xor_lt64 {x y : ℕ} (hx : x < 64) (hy : y < 64) : x ^^^ y < 64 :=
  Nat.xor_lt_two_pow (n := 6) hx hy

theorem pow_lt64 (j : Fin 6) : 2 ^ (j : ℕ) < 64 :=
  Nat.pow_lt_pow_right (by omega) j.isLt

theorem ofVec_add (v w : Vd) : ofVec (v + w) = ofVec v ^^^ ofVec w := by
  apply dtoVec_inj (ofVec_lt _) (xor_lt64 (ofVec_lt v) (ofVec_lt w))
  rw [dtoVec_xor, dtoVec_ofVec, dtoVec_ofVec, dtoVec_ofVec]

theorem ofVec_zero : ofVec 0 = 0 := by
  apply dtoVec_inj (ofVec_lt _) (by omega)
  rw [dtoVec_ofVec, dtoVec_zero]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem sub_eq_add_d (a b : Vd) : a - b = a + b := by
  funext k
  simp only [Pi.sub_apply, Pi.add_apply]
  generalize a k = x
  generalize b k = y
  revert x y
  decide

theorem sum_single_d (x : Vd) : ∑ j, x j • (Pi.single j 1 : Vd) = x := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem bfG_comm (q : ℕ → Bool) (x y : ℕ) : bfG q x y = bfG q y x := by
  rw [bfG, bfG, Nat.xor_comm]
  cases q (y ^^^ x) <;> cases q x <;> cases q y <;> rfl

theorem bfG_self {q : ℕ → Bool} (h0 : q 0 = false) (x : ℕ) : bfG q x x = false := by
  rw [bfG, Nat.xor_self, h0]
  cases q x <;> rfl

theorem formOK_spec {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) (hf : formOK Q = true) :
    q 0 = false ∧ (∀ x < 64, ∀ y < 64, ∀ z < 64, bfG q (x ^^^ y) z = (bfG q x z ^^ bfG q y z)) ∧
      ∀ x < 64, x ≠ 0 → ∃ y < 64, bfG q x y = true := by
  have hbf : ∀ x < 64, ∀ y < 64, bfK Q x y = (bfG q x y).toNat := by
    intro x hx y hy
    rw [bfK_eq, ← hq x hx, ← hq y hy, ← hq _ (xor_lt64 hx hy)]
    rfl
  change andB (Nat.beq (qK Q 0) 0) (andB (allN 64 fun x => allN 64 fun y => allN 64 fun z =>
      Nat.beq (bfK Q (x ^^^ y) z) (bfK Q x z ^^^ bfK Q y z))
    (allN 63 fun x => notB (allN 64 fun y => Nat.beq (bfK Q (x + 1) y) 0))) = true at hf
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hf
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [qK_bind hq (by omega)] at h0
    revert h0
    cases q 0 <;> decide
  · simp only [allN_eq, List.all_eq_true, List.mem_range] at h1
    intro x hx y hy z hz
    have h := h1 x hx y hy z hz
    rw [hbf _ (xor_lt64 hx hy) z hz, hbf x hx z hz, hbf y hy z hz] at h
    change Nat.beq (bfG q (x ^^^ y) z).toNat (Nat.xor (bfG q x z).toNat (bfG q y z).toNat) = true at h
    rw [xor_toNat, nbeq_toNat] at h
    exact beq_iff_eq.1 h
  · intro x hx hx0
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    rw [allN_eq, List.all_eq_true] at h2
    have h := h2 x' (List.mem_range.2 (by omega))
    simp only [notB_eq, allN_eq] at h
    by_contra hne
    have hall : ((List.range 64).all fun y => Nat.beq (bfK Q (x' + 1) y) 0) = true := by
      rw [List.all_eq_true]
      intro y hy
      have hy' := List.mem_range.1 hy
      rw [hbf _ hx y hy']
      cases h' : bfG q (x' + 1) y
      · rfl
      · exact absurd ⟨y, hy', h'⟩ hne
    rw [hall] at h
    exact absurd h (by decide)

@[expose] def qF (q : ℕ → Bool) (v : Vd) : ZMod 2 := bz (q (ofVec v))

theorem sub_sub_z2 : ∀ a b c : ZMod 2, a - b - c = a + b + c := by decide

theorem polar_qF (q : ℕ → Bool) (v w : Vd) :
    polar (qF q) v w = bz (bfG q (ofVec v) (ofVec w)) := by
  rw [polar, qF, qF, qF, ofVec_add, bfG, bz_xor, bz_xor, sub_sub_z2]

theorem qF_toVec {q : ℕ → Bool} {a : ℕ} (ha : a < 64) : qF q (toVec 6 a) = bz (q a) := by
  rw [qF, ofVec_toVec ha]

theorem polar_toVec {q : ℕ → Bool} {a b : ℕ} (ha : a < 64) (hb : b < 64) :
    polar (qF q) (toVec 6 a) (toVec 6 b) = bz (bfG q a b) := by
  rw [polar_qF, ofVec_toVec ha, ofVec_toVec hb]

@[expose] def qForm (q : ℕ → Bool) (h0 : q 0 = false)
    (hb : ∀ x < 64, ∀ y < 64, ∀ z < 64, bfG q (x ^^^ y) z = (bfG q x z ^^ bfG q y z)) :
    QuadraticForm (ZMod 2) Vd :=
  QuadraticMap.ofPolar (qF q)
    (fun a x => by
      rcases zmod2_cases a with rfl | rfl
      · rw [zero_smul, mul_zero, zero_smul, qF, ofVec_zero, h0]
        rfl
      · rw [one_smul, one_mul, one_smul])
    (fun x x' y => by
      rw [polar_qF, polar_qF, polar_qF, ofVec_add, hb _ (ofVec_lt x) _ (ofVec_lt x') _ (ofVec_lt y),
        bz_xor])
    (fun a x y => by
      rcases zmod2_cases a with rfl | rfl
      · rw [zero_smul, zero_smul, polar_qF, ofVec_zero, bfG, Nat.zero_xor, h0]
        cases q (ofVec y) <;> rfl
      · rw [one_smul, one_smul])

theorem qForm_nondeg {q : ℕ → Bool} (h0 : q 0 = false)
    (hb : ∀ x < 64, ∀ y < 64, ∀ z < 64, bfG q (x ^^^ y) z = (bfG q x z ^^ bfG q y z))
    (hn : ∀ x < 64, x ≠ 0 → ∃ y < 64, bfG q x y = true) :
    (qForm q h0 hb).polarBilin.Nondegenerate := by
  have key : ∀ v : Vd, (∀ w, polar (qF q) v w = 0) → v = 0 := by
    intro v hv
    by_contra hne
    have hx : ofVec v ≠ 0 := fun h => hne (by rw [← dtoVec_ofVec v, h, dtoVec_zero])
    obtain ⟨y, hy, hby⟩ := hn _ (ofVec_lt v) hx
    have h := hv (toVec 6 y)
    rw [polar_qF, ofVec_toVec hy, hby] at h
    exact absurd h (by decide)
  refine ⟨fun v hv => key v fun w => hv w, fun w hw => key w fun v => ?_⟩
  rw [polar_comm]
  exact hw v

theorem polar_expand0 (Q : QuadraticForm (ZMod 2) Vd) (z x : Vd) :
    polar Q z x = ∑ j, x j • polar Q z (Pi.single j 1) := by
  conv_lhs => rw [← sum_single_d x]
  rw [← polarBilin_apply_apply, map_sum]
  simp only [map_smul, polarBilin_apply_apply]

theorem polar_expand (Q : QuadraticForm (ZMod 2) Vd) (T : Vd →ₗ[ZMod 2] Vd) (z x : Vd) :
    polar Q z (T x) = ∑ j, x j • polar Q z (T (Pi.single j 1)) := by
  conv_lhs => rw [← sum_single_d x]
  rw [map_sum, ← polarBilin_apply_apply, map_sum]
  simp only [map_smul, polarBilin_apply_apply]

theorem polar_map_of_basis (Q : QuadraticForm (ZMod 2) Vd) (T : Vd →ₗ[ZMod 2] Vd)
    (h2 : ∀ i j, polar Q (T (Pi.single i 1)) (T (Pi.single j 1)) =
      polar Q (Pi.single i 1) (Pi.single j 1)) (x y : Vd) :
    polar Q (T x) (T y) = polar Q x y := by
  have h1 : ∀ i (y : Vd), polar Q (T (Pi.single i 1)) (T y) = polar Q (Pi.single i 1) y := by
    intro i y
    rw [polar_expand Q T, polar_expand0 Q _ y]
    simp only [h2]
  rw [polar_comm, polar_expand Q T]
  simp only [polar_comm Q (T y), h1]
  rw [polar_comm Q x y, polar_expand0 Q y x]
  simp only [polar_comm Q y]

theorem map_of_basis (Q : QuadraticForm (ZMod 2) Vd) (T : Vd →ₗ[ZMod 2] Vd)
    (h1 : ∀ j, Q (T (Pi.single j 1)) = Q (Pi.single j 1))
    (h2 : ∀ i j, polar Q (T (Pi.single i 1)) (T (Pi.single j 1)) =
      polar Q (Pi.single i 1) (Pi.single j 1)) (v : Vd) :
    Q (T v) = Q v := by
  have hp := polar_map_of_basis Q T h2
  have key : ∀ s : Finset (Fin 6),
      Q (T (∑ j ∈ s, v j • Pi.single j 1)) = Q (∑ j ∈ s, v j • Pi.single j 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, map_add, QuadraticMap.map_add (⇑Q), QuadraticMap.map_add (⇑Q), hp,
        ih, map_smul, QuadraticMap.map_smul, QuadraticMap.map_smul, h1]
  have := key Finset.univ
  rwa [sum_single_d] at this

@[expose] def colMat (L : List ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => toVec 6 (L.getD j 0) i

theorem colMat_mulVec_single (L : List ℕ) (j : Fin 6) :
    colMat L *ᵥ Pi.single j 1 = toVec 6 (L.getD j 0) := by
  rw [mulVec_single_one]
  rfl

@[expose] def colsOf (A : Array ℕ) : List ℕ := (List.range 6).map fun j => bmulVec 6 6 A (2 ^ j)

theorem getD_colsOf (A : Array ℕ) {j : ℕ} (hj : j < 6) : (colsOf A).getD j 0 = bmulVec 6 6 A (2 ^ j) := by
  simp [colsOf, List.getD_eq_getElem?_getD, hj]

theorem colsOf_lt (A : Array ℕ) : ∀ x ∈ colsOf A, x < 64 := by
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact bmulVec_lt _ _

theorem colMat_colsOf (A : Array ℕ) : colMat (colsOf A) = toMat 6 6 A := by
  ext i j
  change toVec 6 ((colsOf A).getD j 0) i = _
  rw [getD_colsOf A j.isLt, toVec_bmulVec, dtoVec_two_pow, mulVec_single_one]
  rfl

theorem bmulVec_zero (A : Array ℕ) : bmulVec 6 6 A 0 = 0 :=
  dtoVec_inj (bmulVec_lt _ _) (by omega) (by rw [toVec_bmulVec, dtoVec_zero, mulVec_zero])

theorem getD_map_zero {f : ℕ → ℕ} (hf : f 0 = 0) :
    ∀ (l : List ℕ) (n : ℕ), (l.map f).getD n 0 = f (l.getD n 0)
  | [], n => by rw [List.map_nil, List.getD_nil, hf]
  | a :: l, 0 => by rw [List.map_cons, List.getD_cons_zero, List.getD_cons_zero]
  | a :: l, n + 1 => by
    rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ, getD_map_zero hf l n]

theorem colMat_map (A : Array ℕ) (C : List ℕ) :
    colMat (C.map (bmulVec 6 6 A)) = toMat 6 6 A * colMat C := by
  ext i j
  change toVec 6 ((C.map (bmulVec 6 6 A)).getD j 0) i = _
  rw [getD_map_zero (bmulVec_zero A), toVec_bmulVec, mul_apply]
  rfl

theorem colAt_colsOfRows (M : ℕ) {j : ℕ} (hj : j < 6) : colAt (colsOfRows M) j = bvecK M (2 ^ j) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (fget (colsOfRows M) j 6).testBit i = _
  rw [testBit_fget]
  by_cases hi : i < 6
  · have e : colsOfRows M = orN 6 fun j => bvecK M (2 ^ j) <<< (6 * j) := by
      unfold colsOfRows
      simp only [pw2_eq]
      rfl
    rw [e, decide_eq_true hi, Bool.true_and, show j * 6 + i = 6 * j + i by ring,
      testBit_orN_rows (fun j _ => bvecK_lt _ _) hj hi]
  · rw [decide_eq_false hi, Bool.false_and, testBit_lt64 (bvecK_lt _ _) (by omega)]

theorem dick_of_dickK {M : ℕ} (h : dickK (colsOfRows M) = 0) : dickC (colsOf (decR M)) = false := by
  rw [dickK_eq_dickC (X := colsOfRows M) (L := colsOf (decR M))
    (fun j hj => by rw [getD_colsOf _ hj, colAt_colsOfRows M hj, bvecK_eq])] at h
  cases hd : dickC (colsOf (decR M))
  · rfl
  · rw [hd] at h
    exact absurd h (by decide)

theorem dick_vec (L : List ℕ) (j : Fin 6) :
    toVec 6 (L.getD j 0 ^^^ 2 ^ (j : ℕ)) = (mulVecLin (colMat L) - 1) (Pi.single j 1) := by
  rw [dtoVec_xor, dtoVec_two_pow, LinearMap.sub_apply, mulVecLin_apply, colMat_mulVec_single,
    Module.End.one_apply, sub_eq_add_d]

theorem dick_span {L : List ℕ} (hL : ∀ j < 6, L.getD j 0 < 64) {x : ℕ} (hx : x < 64) :
    InSp (fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j) x ↔
      toVec 6 x ∈ LinearMap.range (mulVecLin (colMat L) - 1) := by
  have hS : ∀ a, (∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j) → a < 2 ^ 6 := by
    rintro a ⟨j, hj, rfl⟩
    exact xor_lt64 (hL j hj) (pow_lt64 ⟨j, hj⟩)
  have hmem : ∀ y, InSp (fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j) y →
      toVec 6 y ∈ LinearMap.range (mulVecLin (colMat L) - 1) := by
    intro y h
    induction h with
    | zero =>
      rw [dtoVec_zero]
      exact Submodule.zero_mem _
    | @add a b ha _ ih =>
      obtain ⟨j, hj, rfl⟩ := ha
      rw [dtoVec_xor]
      refine Submodule.add_mem _ ?_ ih
      have := dick_vec L ⟨j, hj⟩
      rw [this]
      exact LinearMap.mem_range_self _ _
  constructor
  · exact hmem x
  · intro h
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 h
    have hex : ∀ s : Finset (Fin 6), ∃ y, InSp (fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j) y ∧
        toVec 6 y = ∑ j ∈ s, u j • (mulVecLin (colMat L) - 1) (Pi.single j 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨0, InSp.zero, by rw [dtoVec_zero, Finset.sum_empty]⟩
      | insert a s ha ih =>
        obtain ⟨y, hy, hyv⟩ := ih
        rw [Finset.sum_insert ha]
        rcases zmod2_cases (u a) with h | h
        · exact ⟨y, hy, by rw [h, zero_smul, zero_add, hyv]⟩
        · refine ⟨(L.getD a 0 ^^^ 2 ^ (a : ℕ)) ^^^ y, InSp.add ⟨a, a.isLt, rfl⟩ hy, ?_⟩
          rw [dtoVec_xor, hyv, h, one_smul, dick_vec]
    obtain ⟨y, hy, hyv⟩ := hex Finset.univ
    have hu' : (mulVecLin (colMat L) - 1) u =
        ∑ j, u j • (mulVecLin (colMat L) - 1) (Pi.single j 1) := by
      conv_lhs => rw [← sum_single_d u]
      rw [map_sum]
      simp only [map_smul]
    have hyx : y = x := dtoVec_inj (InSp.lt hS hy) hx (by rw [hyv, ← hu', hu])
    rw [← hyx]
    exact hy

theorem card_spanF_eq {L : List ℕ} (hL : ∀ j < 6, L.getD j 0 < 64) :
    (spanF fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j).card =
      2 ^ finrank (ZMod 2) (LinearMap.range (mulVecLin (colMat L) - 1)) := by
  classical
  have e : (LinearMap.range (mulVecLin (colMat L) - 1) : Set Vd) =
      (((spanF fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j).image (toVec 6) : Finset Vd) : Set Vd) := by
    ext v
    rw [Finset.coe_image, Set.mem_image, SetLike.mem_coe]
    constructor
    · intro hv
      refine ⟨ofVec v, ?_, dtoVec_ofVec v⟩
      rw [Finset.mem_coe, mem_spanF]
      refine ⟨ofVec_lt v, (dick_span hL (ofVec_lt v)).2 ?_⟩
      rwa [dtoVec_ofVec]
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.mem_coe, mem_spanF] at hx
      exact (dick_span hL hx.1).1 hx.2
  have hinj : Set.InjOn (toVec 6)
      ((spanF fun a => ∃ j < 6, a = L.getD j 0 ^^^ 2 ^ j) : Set ℕ) := fun x hx y hy h =>
    dtoVec_inj (mem_spanF.1 hx).1 (mem_spanF.1 hy).1 h
  rw [← Finset.card_image_of_injOn hinj, ← Set.ncard_coe_finset, ← e, ← Nat.card_coe_set_eq]
  change Nat.card (LinearMap.range (mulVecLin (colMat L) - 1)) = _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem dickC_eq {L : List ℕ} (hL : ∀ j < 6, L.getD j 0 < 64) (g : Vd ≃ₗ[ZMod 2] Vd)
    (hg : ∀ v, g v = colMat L *ᵥ v) :
    dickC L = decide (finrank (ZMod 2) (commSpace g) % 2 = 1) := by
  obtain ⟨c, h1, h2⟩ := dickC_spec hL
  have hW : LinearMap.range (mulVecLin (colMat L) - 1) = commSpace g := by
    ext v
    rw [mem_commSpace, LinearMap.mem_range]
    simp only [LinearMap.sub_apply, mulVecLin_apply, Module.End.one_apply, hg]
  have hc : c = finrank (ZMod 2) (commSpace g) := by
    apply Nat.pow_right_injective (le_refl 2)
    change 2 ^ c = 2 ^ _
    rw [← h2, card_spanF_eq hL, hW]
  rw [h1, hc]

theorem even_of_dick {n : ℕ} (h : false = decide (n % 2 = 1)) : (n : ZMod 2) = 0 := by
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  have := h.symm
  rw [decide_eq_false_iff_not] at this
  omega

@[expose] def LeafP (q : ℕ → Bool) (cs : List ℕ) : Prop :=
  (∀ x ∈ cs, x < 64) ∧ ∀ k < cs.length, q (cs.getD k 0) = q (2 ^ k) ∧
    ∀ i < k, bfG q (cs.getD i 0) (cs.getD k 0) = bfG q (2 ^ i) (2 ^ k)

theorem leafP_append {q : ℕ → Bool} {cs : List ℕ} {c : ℕ} (h : LeafP q cs)
    (hc : c ∈ extendColsG q cs) : LeafP q (cs ++ [c]) := by
  simp only [extendColsG, List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hc
  obtain ⟨hc64, hqc, hbc⟩ := hc
  have gd : ∀ i < cs.length, (cs ++ [c]).getD i 0 = cs.getD i 0 := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have gl : (cs ++ [c]).getD cs.length 0 = c := by
    simp [List.getD_eq_getElem?_getD]
  refine ⟨fun x hx => ?_, fun k hk => ?_⟩
  · rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.1 x hx
    · exact hc64
  · rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [gd k hk]
      refine ⟨(h.2 k hk).1, fun i hi => ?_⟩
      rw [gd i (by omega)]
      exact (h.2 k hk).2 i hi
    · rw [gl]
      refine ⟨hqc, fun i hi => ?_⟩
      rw [gd i hi]
      exact hbc i hi

theorem leafP_oColsAuxG {q : ℕ → Bool} : ∀ (n : ℕ) (cs C : List ℕ), C ∈ oColsAuxG q n cs →
    LeafP q cs → LeafP q C
  | 0, cs, C, hC, h => by
    simp only [oColsAuxG, List.mem_singleton] at hC
    subst hC
    exact h
  | n + 1, cs, C, hC, h => by
    simp only [oColsAuxG, List.mem_flatMap] at hC
    obtain ⟨c, hc, hC⟩ := hC
    exact leafP_oColsAuxG n _ C hC (leafP_append h hc)

theorem dick_gen {q : ℕ → Bool} {h0 : q 0 = false}
    {hb : ∀ x < 64, ∀ y < 64, ∀ z < 64, bfG q (x ^^^ y) z = (bfG q x z ^^ bfG q y z)}
    (hQ : (qForm q h0 hb).polarBilin.Nondegenerate) {A B : Array ℕ}
    (hAB : toMat 6 6 A * toMat 6 6 B = 1) (hBA : toMat 6 6 B * toMat 6 6 A = 1)
    (hAq : ∀ v, qF q (toMat 6 6 A *ᵥ v) = qF q v) (hAd : dickC (colsOf A) = false)
    {C : List ℕ} (hc : ∀ x ∈ C, x < 64) (hl : C.length = 6) (hP : LeafP q C)
    (hdC : dickC C = false) : dickC (C.map (bmulVec 6 6 A)) = false := by
  obtain ⟨eA, heA⟩ : ∃ e : Vd ≃ₗ[ZMod 2] Vd, ∀ v, e v = toMat 6 6 A *ᵥ v :=
    ⟨LinearEquiv.ofLinear (mulVecLin (toMat 6 6 A)) (mulVecLin (toMat 6 6 B))
      (LinearMap.ext fun v => by simp [mulVec_mulVec, hAB])
      (LinearMap.ext fun v => by simp [mulVec_mulVec, hBA]), fun v => rfl⟩
  have hT1 : ∀ j, qForm q h0 hb (mulVecLin (colMat C) (Pi.single j 1)) =
      qForm q h0 hb (Pi.single j 1) := by
    intro j
    rw [mulVecLin_apply, colMat_mulVec_single, ← dtoVec_two_pow]
    change qF q _ = qF q _
    rw [qF_toVec (getD_lt hP.1 j), qF_toVec (pow_lt64 j),
      (hP.2 j (by rw [hl]; exact j.isLt)).1]
  have hT2 : ∀ i j, polar (qForm q h0 hb) (mulVecLin (colMat C) (Pi.single i 1))
      (mulVecLin (colMat C) (Pi.single j 1)) = polar (qForm q h0 hb) (Pi.single i 1) (Pi.single j 1) := by
    intro i j
    rw [mulVecLin_apply, mulVecLin_apply, colMat_mulVec_single, colMat_mulVec_single,
      ← dtoVec_two_pow, ← dtoVec_two_pow]
    change polar (qF q) _ _ = polar (qF q) _ _
    rw [polar_toVec (getD_lt hP.1 i) (getD_lt hP.1 j), polar_toVec (pow_lt64 i) (pow_lt64 j)]
    congr 1
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact (hP.2 j (by rw [hl]; exact j.isLt)).2 i h
    · have : i = j := Fin.ext h
      subst this
      rw [bfG_self h0, bfG_self h0]
    · rw [bfG_comm, bfG_comm q (2 ^ (i : ℕ))]
      exact (hP.2 i (by rw [hl]; exact i.isLt)).2 j h
  have hpol := polar_map_of_basis _ _ hT2
  have hinj : Function.Injective (mulVecLin (colMat C)) := by
    intro x y hxy
    rw [← sub_eq_zero]
    apply hQ.1
    intro z
    rw [polarBilin_apply_apply, ← hpol, map_sub, hxy, sub_self]
    exact QuadraticMap.polar_zero_left (Q := qForm q h0 hb) _
  obtain ⟨eC, heC⟩ : ∃ e : Vd ≃ₗ[ZMod 2] Vd, ∀ v, e v = colMat C *ᵥ v :=
    ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun v => by
      rw [LinearEquiv.coe_ofInjectiveEndo, mulVecLin_apply]⟩
  have hmA : eA ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm q h0 hb) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => by
      rw [heA]
      exact hAq v
  have hmC : eC ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm q h0 hb) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => by
      rw [heC, ← mulVecLin_apply]
      exact map_of_basis _ _ hT1 hT2 v
  have key := natCast_finrank_commSpace_mul hQ hmA hmC
  have dA := dickC_eq (fun j _ => getD_lt (colsOf_lt A) j) eA (by rw [colMat_colsOf]; exact heA)
  have dC := dickC_eq (fun j _ => getD_lt hc j) eC heC
  have hcm : ∀ x ∈ C.map (bmulVec 6 6 A), x < 64 := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact bmulVec_lt _ _
  have dAC := dickC_eq (fun j _ => getD_lt hcm j) (eA * eC) (fun v => by
    rw [colMat_map, ← mulVec_mulVec]
    change eA (eC v) = _
    rw [heA, heC])
  rw [hAd] at dA
  rw [hdC] at dC
  rw [even_of_dick dA, even_of_dick dC, add_zero, ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
    at key
  rw [dAC, decide_eq_false_iff_not]
  omega

theorem dick_sound_proved {q : ℕ → Bool} {G GI : ℕ → Array ℕ} {Q GP GIP : Nat} (hq : QBind q Q)
    (hf : formOK Q = true) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hGI : ∀ s < 6, GI s = decR (mat GIP s)) (hgen : genCheckG q G GI = true)
    (h : genDickOK GP GIP = true) : dickCheckG q G GI = true := by
  obtain ⟨h0, hb, hn⟩ := formOK_spec hq hf
  have hQ := qForm_nondeg h0 hb hn
  have hgen' : ∀ i < 6, toMat 6 6 (G i) * toMat 6 6 (GI i) = 1 ∧
      toMat 6 6 (GI i) * toMat 6 6 (G i) = 1 ∧ ∀ v, qF q (toMat 6 6 (G i) *ᵥ v) = qF q v := by
    intro i hi
    rw [genCheckG, List.all_eq_true] at hgen
    have h' := hgen i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    refine ⟨by rw [← toMat_bmul, toMat_eq_one_of_bIsId h1], by rw [← toMat_bmul,
      toMat_eq_one_of_bIsId h2], fun v => ?_⟩
    rw [← dtoVec_ofVec v, ← toVec_bmulVec, qF_toVec (bmulVec_lt _ _), qF_toVec (ofVec_lt v),
      h3 _ (ofVec_lt v)]
  have hgd : ∀ i < 6, dickC (colsOf (G i)) = false ∧ dickC (colsOf (GI i)) = false := by
    change allN 6 (fun i => andB (Nat.beq (dickK (colsOfRows (mat GP i))) 0)
      (Nat.beq (dickK (colsOfRows (mat GIP i))) 0)) = true at h
    rw [allN_eq, List.all_eq_true] at h
    intro i hi
    have h' := h i (List.mem_range.2 hi)
    simp only [andB_eq, Bool.and_eq_true] at h'
    rw [hG i hi, hGI i hi]
    exact ⟨dick_of_dickK (Nat.eq_of_beq_eq_true h'.1), dick_of_dickK (Nat.eq_of_beq_eq_true h'.2)⟩
  rw [dickCheckG, List.all_eq_true]
  intro C hC
  obtain ⟨hl, hc⟩ := mem_oColsAuxG 6 [] C hC (by simp)
  have hl6 : C.length = 6 := by simpa using hl
  have hP := leafP_oColsAuxG 6 [] C hC ⟨by simp, by simp⟩
  cases hdC : dickC C
  · rw [Bool.false_or, List.all_eq_true]
    intro i hi
    have hi6 := List.mem_range.1 hi
    obtain ⟨h1, h2, h3⟩ := hgen' i hi6
    obtain ⟨d1, d2⟩ := hgd i hi6
    have h3' : ∀ v, qF q (toMat 6 6 (GI i) *ᵥ v) = qF q v := fun v => by
      rw [← h3, mulVec_mulVec, h1, one_mulVec]
    rw [dick_gen hQ h1 h2 h3 d1 hc hl6 hP hdC, dick_gen hQ h2 h1 h3' d2 hc hl6 hP hdC]
    rfl
  · rfl

end CFSG.KC.O8.DickPf

end
