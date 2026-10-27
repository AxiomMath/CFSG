module

public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import CFSG.Certificates.Kernel.Misc.Spec.Words
public import CFSG.Certificates.Kernel.Misc.Spec.ArrMat
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.Spec

open CFSG.Fischer

@[expose] def blk (c a b : ℕ) : ℕ :=
  if a = 0 then (if b = 0 then c % 2 else c / 2 % 2)
  else if b = 0 then c / 2 % 2 else (c % 2 + c / 2 % 2) % 2

@[expose] def blkZ (x : F4) (a b : ℕ) : ZMod 2 := ((blk x.code.val a b : ℕ) : ZMod 2)

theorem blkZ_add (x y : F4) (a b : ℕ) : blkZ (x + y) a b = blkZ x a b + blkZ y a b := by
  unfold blkZ blk
  split_ifs
  · revert x y; decide +kernel
  · revert x y; decide +kernel
  · revert x y; decide +kernel
  · revert x y; decide +kernel

theorem blkZ_zero (a b : ℕ) : blkZ 0 a b = 0 := by
  unfold blkZ blk
  split_ifs <;> decide +kernel

theorem blkZ_mul_aux : ∀ x y : F4, ∀ a < 2, ∀ b < 2,
    blkZ (x * y) a b = blkZ x a 0 * blkZ y 0 b + blkZ x a 1 * blkZ y 1 b := by
  decide +kernel

theorem blkZ_mul (x y : F4) {a b : ℕ} (ha : a < 2) (hb : b < 2) :
    blkZ (x * y) a b = blkZ x a 0 * blkZ y 0 b + blkZ x a 1 * blkZ y 1 b :=
  blkZ_mul_aux x y a ha b hb

theorem blkZ_one_aux : ∀ a < 2, ∀ b < 2, blkZ 1 a b = if a = b then 1 else 0 := by
  decide +kernel

theorem blkZ_one {a b : ℕ} (ha : a < 2) (hb : b < 2) :
    blkZ 1 a b = if a = b then 1 else 0 :=
  blkZ_one_aux a ha b hb

theorem blkZ_sum {ι : Type*} (s : Finset ι) (z : ι → F4) (a b : ℕ) :
    blkZ (∑ j ∈ s, z j) a b = ∑ j ∈ s, blkZ (z j) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using blkZ_zero a b
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, blkZ_add, ih]

@[expose] def mget (M : Matrix (Fin 14) (Fin 14) F4) (i j : ℕ) : F4 :=
  if h : i < 14 ∧ j < 14 then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem mget_fin (M : Matrix (Fin 14) (Fin 14) F4) (i j : Fin 14) : mget M i.val j.val = M i j := by
  unfold mget
  rw [dif_pos ⟨i.isLt, j.isLt⟩]

@[expose] def blowMat (M : Matrix (Fin 14) (Fin 14) F4) : Matrix (Fin 28) (Fin 28) (ZMod 2) :=
  Matrix.of fun R C => blkZ (mget M (R.val / 2) (C.val / 2)) (R.val % 2) (C.val % 2)

theorem mget_mul (M N : Matrix (Fin 14) (Fin 14) F4) {i k : ℕ} (hi : i < 14) (hk : k < 14) :
    mget (M * N) i k = ∑ j ∈ Finset.range 14, mget M i j * mget N j k := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => mget M i j * mget N j k) 14]
  have e : mget (M * N) i k = (M * N) ⟨i, hi⟩ ⟨k, hk⟩ := by
    have := mget_fin (M * N) ⟨i, hi⟩ ⟨k, hk⟩
    exact this
  rw [e, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := mget_fin M ⟨i, hi⟩ j
  have h2 := mget_fin N j ⟨k, hk⟩
  simp only at h1 h2
  rw [h1, h2]

theorem sum_range_double (F : ℕ → ZMod 2) (m : ℕ) :
    ∑ J ∈ Finset.range (2 * m), F J = ∑ j ∈ Finset.range m, (F (2 * j) + F (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]

theorem blowMat_mul (M N : Matrix (Fin 14) (Fin 14) F4) :
    blowMat (M * N) = blowMat M * blowMat N := by
  ext R C
  have hi : R.val / 2 < 14 := by have := R.isLt; omega
  have hk : C.val / 2 < 14 := by have := C.isLt; omega
  have ha : R.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have hb : C.val % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [Matrix.mul_apply]
  simp only [blowMat, Matrix.of_apply]
  rw [mget_mul M N hi hk, blkZ_sum]
  rw [Fin.sum_univ_eq_sum_range (fun J => blkZ (mget M (R.val / 2) (J / 2)) (R.val % 2)
      (J % 2) * blkZ (mget N (J / 2) (C.val / 2)) (J % 2) (C.val % 2)) 28]
  refine Eq.trans ?_ (sum_range_double (fun J => blkZ (mget M (R.val / 2) (J / 2)) (R.val % 2)
      (J % 2) * blkZ (mget N (J / 2) (C.val / 2)) (J % 2) (C.val % 2)) 14).symm
  refine Finset.sum_congr rfl fun j _ => ?_
  have e0 : 2 * j / 2 = j := by omega
  have e1 : 2 * j % 2 = 0 := by omega
  have e2 : (2 * j + 1) / 2 = j := by omega
  have e3 : (2 * j + 1) % 2 = 1 := by omega
  rw [blkZ_mul _ _ ha hb, e0, e1, e2, e3]

theorem mget_one {i k : ℕ} (hi : i < 14) (hk : k < 14) :
    mget (1 : Matrix (Fin 14) (Fin 14) F4) i k = if i = k then 1 else 0 := by
  have h := mget_fin (1 : Matrix (Fin 14) (Fin 14) F4) ⟨i, hi⟩ ⟨k, hk⟩
  simp only at h
  rw [h, Matrix.one_apply]
  by_cases hik : i = k <;> simp [hik, Fin.ext_iff]

theorem blowMat_one : blowMat 1 = 1 := by
  ext R C
  have hi : R.val / 2 < 14 := by have := R.isLt; omega
  have hk : C.val / 2 < 14 := by have := C.isLt; omega
  have ha : R.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have hb : C.val % 2 < 2 := Nat.mod_lt _ (by omega)
  simp only [blowMat, Matrix.of_apply]
  rw [mget_one hi hk, Matrix.one_apply]
  by_cases h : R.val / 2 = C.val / 2
  · by_cases h2 : R.val % 2 = C.val % 2
    · have hRC : R = C := Fin.ext (by omega)
      rw [if_pos h, blkZ_one ha hb, if_pos h2, if_pos hRC]
    · have hRC : R ≠ C := fun e => h2 (by rw [e])
      rw [if_pos h, blkZ_one ha hb, if_neg h2, if_neg hRC]
  · have hRC : R ≠ C := fun e => h (by rw [e])
    rw [if_neg h, blkZ_zero, if_neg hRC]

theorem blowMat_injective : Function.Injective blowMat := by
  intro M N h
  ext i j
  have h1 := congrFun (congrFun h ⟨2 * i.val, by omega⟩) ⟨2 * j.val, by omega⟩
  have h2 := congrFun (congrFun h ⟨2 * i.val, by omega⟩) ⟨2 * j.val + 1, by omega⟩
  simp only [blowMat, Matrix.of_apply] at h1 h2
  have e0 : 2 * i.val / 2 = i.val := by omega
  have e1 : 2 * i.val % 2 = 0 := by omega
  have e2 : 2 * j.val / 2 = j.val := by omega
  have e3 : 2 * j.val % 2 = 0 := by omega
  have e4 : (2 * j.val + 1) / 2 = j.val := by omega
  have e5 : (2 * j.val + 1) % 2 = 1 := by omega
  rw [e0, e1, e2, e3, mget_fin, mget_fin] at h1
  rw [e0, e1, e4, e5, mget_fin, mget_fin] at h2
  unfold blkZ blk at h1 h2
  simp only [if_true, one_ne_zero, if_false] at h1 h2
  rw [ZMod.natCast_eq_natCast_iff'] at h1 h2
  have hx := (M i j).code.isLt
  have hy := (N i j).code.isLt
  have hc : (M i j).code = (N i j).code := Fin.ext (by omega)
  cases hM : M i j
  cases hN : N i j
  rw [hM, hN] at hc
  simp_all

@[expose] def blkBits (N p d : ℕ) : ℕ :=
  ((d &&& 1) <<< p ||| ((d >>> 1) &&& 1) <<< (p + 1)) |||
    (((d >>> 1) &&& 1) <<< (p + N) ||| ((d &&& 1) ^^^ ((d >>> 1) &&& 1)) <<< (p + N + 1))

theorem testBit_shl_bit {x : ℕ} (hx : x < 2) (p q : ℕ) :
    (x <<< p).testBit q = decide (q = p ∧ x = 1) := by
  rw [Nat.testBit_shiftLeft]
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
  · simp
  · rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero,
      and_true]
    omega

theorem pos_iff {N R C a b : ℕ} (hC : C < N) (hb : b < N) :
    N * R + C = N * a + b ↔ R = a ∧ C = b := by
  constructor
  · intro h
    exact pos_unique hC hb h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem testBit_blkBits {N i j d R C : ℕ} (hj : 2 * j + 2 ≤ N) (hC : C < N) :
    (blkBits N (2 * N * i + 2 * j) d).testBit (N * R + C) = true ↔
      (R / 2 = i ∧ C / 2 = j ∧ blk d (R % 2) (C % 2) = 1) := by
  have hx0 : d &&& 1 < 2 := by rw [Nat.and_one_is_mod]; omega
  have hx1 : (d >>> 1) &&& 1 < 2 := by rw [Nat.and_one_is_mod]; omega
  have hx2 : ((d &&& 1) ^^^ ((d >>> 1) &&& 1)) < 2 := Nat.xor_lt_two_pow (n := 1) hx0 hx1
  have h00 : N * R + C = 2 * N * i + 2 * j ↔ R = 2 * i ∧ C = 2 * j := by
    rw [show 2 * N * i + 2 * j = N * (2 * i) + 2 * j by ring]
    exact pos_iff hC (by omega)
  have h01 : N * R + C = 2 * N * i + 2 * j + 1 ↔ R = 2 * i ∧ C = 2 * j + 1 := by
    rw [show 2 * N * i + 2 * j + 1 = N * (2 * i) + (2 * j + 1) by ring]
    exact pos_iff hC (by omega)
  have h10 : N * R + C = 2 * N * i + 2 * j + N ↔ R = 2 * i + 1 ∧ C = 2 * j := by
    rw [show 2 * N * i + 2 * j + N = N * (2 * i + 1) + 2 * j by ring]
    exact pos_iff hC (by omega)
  have h11 : N * R + C = 2 * N * i + 2 * j + N + 1 ↔ R = 2 * i + 1 ∧ C = 2 * j + 1 := by
    rw [show 2 * N * i + 2 * j + N + 1 = N * (2 * i + 1) + (2 * j + 1) by ring]
    exact pos_iff hC (by omega)
  unfold blkBits
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, testBit_shl_bit hx0, testBit_shl_bit hx1,
    testBit_shl_bit hx1, testBit_shl_bit hx2]
  simp only [Bool.or_eq_true, decide_eq_true_eq, h00, h01, h10, h11, Nat.and_one_is_mod,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rcases Nat.mod_two_eq_zero_or_one d with h0 | h0 <;>
  rcases Nat.mod_two_eq_zero_or_one (d / 2) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one R with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one C with hb | hb <;>
  simp [blk, h0, h1, ha, hb] <;> omega

theorem blowEntry_eq (i j d : ℕ) :
    CFSG.KC.Misc.G24.blowEntry i j d = blkBits 28 (2 * 28 * i + 2 * j) d := by
  unfold CFSG.KC.Misc.G24.blowEntry blkBits
  simp only [CFSG.KS.PK.letN_eq]
  rfl

theorem blk_lt (d a b : ℕ) : blk d a b < 2 := by
  unfold blk
  split_ifs <;> omega

theorem blk_mod (d a b : ℕ) : blk (d % 4) a b = blk d a b := by
  unfold blk
  split_ifs <;> omega

@[expose] noncomputable def rowOr (i : ℕ) (r : List ℕ) (acc : ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => acc)
    (fun d _ ih2 j => Nat.lor (CFSG.KC.Misc.G24.blowEntry i j d) (ih2 (Nat.succ j))) r

theorem blowRows_cons (r : List ℕ) (rs : List (List ℕ)) (i acc : ℕ) :
    CFSG.KC.Misc.G24.blowRows (r :: rs) i acc =
      CFSG.KC.Misc.G24.blowRows rs (i + 1) (rowOr i r acc 0) := rfl

theorem blowRows_nil (i acc : ℕ) : CFSG.KC.Misc.G24.blowRows [] i acc = acc := rfl

theorem rowOr_nil (i acc j : ℕ) : rowOr i [] acc j = acc := rfl

theorem rowOr_cons (i d : ℕ) (r : List ℕ) (acc j : ℕ) :
    rowOr i (d :: r) acc j =
      CFSG.KC.Misc.G24.blowEntry i j d ||| rowOr i r acc (j + 1) := rfl

theorem testBit_rowOr (i : ℕ) (r : List ℕ) (acc q : ℕ) : ∀ j,
    (rowOr i r acc j).testBit q = true ↔
      acc.testBit q = true ∨ ∃ t < r.length,
        (CFSG.KC.Misc.G24.blowEntry i (j + t) (r.getD t 0)).testBit q = true := by
  induction r with
  | nil => intro j; simp [rowOr_nil]
  | cons d r ih =>
    intro j
    rw [rowOr_cons, Nat.testBit_or, Bool.or_eq_true, ih (j + 1)]
    constructor
    · rintro (h | h | ⟨t, ht, h⟩)
      · exact Or.inr ⟨0, by simp, by simpa using h⟩
      · exact Or.inl h
      · refine Or.inr ⟨t + 1, by simpa using ht, ?_⟩
        rw [show j + (t + 1) = j + 1 + t by omega]
        simpa using h
    · rintro (h | ⟨t, ht, h⟩)
      · exact Or.inr (Or.inl h)
      · cases t with
        | zero => exact Or.inl (by simpa using h)
        | succ t =>
          refine Or.inr (Or.inr ⟨t, by simpa using ht, ?_⟩)
          rw [show j + 1 + t = j + (t + 1) by omega]
          simpa using h

theorem testBit_blowRows (rs : List (List ℕ)) (q : ℕ) : ∀ (acc i : ℕ),
    (CFSG.KC.Misc.G24.blowRows rs i acc).testBit q = true ↔
      acc.testBit q = true ∨ ∃ s < rs.length, ∃ t < (rs.getD s []).length,
        (CFSG.KC.Misc.G24.blowEntry (i + s) t ((rs.getD s []).getD t 0)).testBit q = true := by
  induction rs with
  | nil => intro acc i; simp [blowRows_nil]
  | cons r rs ih =>
    intro acc i
    rw [blowRows_cons, ih, testBit_rowOr]
    constructor
    · rintro ((h | ⟨t, ht, h⟩) | ⟨s, hs, t, ht, h⟩)
      · exact Or.inl h
      · refine Or.inr ⟨0, by simp, t, by simpa using ht, ?_⟩
        simpa using h
      · refine Or.inr ⟨s + 1, by simpa using hs, t, by simpa using ht, ?_⟩
        rw [show i + (s + 1) = i + 1 + s by omega]
        simpa using h
    · rintro (h | ⟨s, hs, t, ht, h⟩)
      · exact Or.inl (Or.inl h)
      · cases s with
        | zero => exact Or.inl (Or.inr ⟨t, by simpa using ht, by simpa using h⟩)
        | succ s =>
          refine Or.inr ⟨s, by simpa using hs, t, by simpa using ht, ?_⟩
          rw [show i + 1 + s = i + (s + 1) by omega]
          simpa using h

theorem shape4_iff (ds : List (List ℕ)) : CFSG.KC.Misc.G24.shape4 ds = true ↔
    ds.length = 14 ∧ ∀ r ∈ ds, r.length = 14 ∧ ∀ d ∈ r, d < 4 := by
  unfold CFSG.KC.Misc.G24.shape4
  rw [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.allLL_iff, lenLLK_eq]
  refine and_congr Iff.rfl (forall_congr' fun r => forall_congr' fun _ => ?_)
  rw [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.lenN_misc_eq,
    CFSG.KS.PK.allL_lqt_iff]
  simp only [Nat.blt_eq]

@[expose] def digMat (ds : List (List ℕ)) : Matrix (Fin 14) (Fin 14) F4 :=
  Matrix.of fun i j => ⟨⟨(ds.getD i.val []).getD j.val 0 % 4, Nat.mod_lt _ (by norm_num)⟩⟩

theorem pkMat_blow14 {ds : List (List ℕ)} (h : CFSG.KC.Misc.G24.shape4 ds = true) :
    pkMat 28 (CFSG.KC.Misc.G24.blow14 ds) = blowMat (digMat ds) := by
  obtain ⟨hlen, hrows⟩ := (shape4_iff ds).1 h
  ext R C
  have hi : R.val / 2 < 14 := by have := R.isLt; omega
  have hk : C.val / 2 < 14 := by have := C.isLt; omega
  have hC : C.val < 28 := C.isLt
  have hmem : ∀ s < 14, (ds.getD s []).length = 14 := by
    intro s hs
    have : ds.getD s [] ∈ ds := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp
    exact (hrows _ this).1
  have hbit : (CFSG.KC.Misc.G24.blow14 ds).testBit (28 * R.val + C.val) = true ↔
      blk ((ds.getD (R.val / 2) []).getD (C.val / 2) 0) (R.val % 2) (C.val % 2) = 1 := by
    unfold CFSG.KC.Misc.G24.blow14
    rw [testBit_blowRows]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, blowEntry_eq, Nat.zero_add]
    constructor
    · rintro ⟨s, hs, t, ht, hh⟩
      rw [hmem s (by omega)] at ht
      have := (testBit_blkBits (N := 28) (i := s) (j := t) (by omega) hC).1 hh
      obtain ⟨h1, h2, h3⟩ := this
      rw [← h1, ← h2] at *
      exact h3
    · intro hh
      refine ⟨R.val / 2, by omega, C.val / 2, by rw [hmem _ hi]; omega, ?_⟩
      exact (testBit_blkBits (N := 28) (by omega) hC).2 ⟨rfl, rfl, hh⟩
  have hd : (mget (digMat ds) (R.val / 2) (C.val / 2)).code.val =
      (ds.getD (R.val / 2) []).getD (C.val / 2) 0 % 4 := by
    unfold mget
    rw [dif_pos ⟨hi, hk⟩]
    rfl
  simp only [pkMat, blowMat, blkZ, Matrix.of_apply, hd, blk_mod]
  have hlt := blk_lt ((ds.getD (R.val / 2) []).getD (C.val / 2) 0) (R.val % 2) (C.val % 2)
  by_cases hb : (CFSG.KC.Misc.G24.blow14 ds).testBit (28 * R.val + C.val) = true
  · rw [if_pos hb, hbit.1 hb]
    simp
  · have hb1 : ¬ blk ((ds.getD (R.val / 2) []).getD (C.val / 2) 0) (R.val % 2) (C.val % 2) = 1 :=
      fun e => hb (hbit.2 e)
    have hb0 : blk ((ds.getD (R.val / 2) []).getD (C.val / 2) 0) (R.val % 2) (C.val % 2) = 0 := by
      omega
    rw [if_neg hb, hb0]
    simp

theorem pkMat_wordF4 {Gb : List ℕ} {G : ℕ → Matrix (Fin 14) (Fin 14) F4}
    (hG : ∀ i < 6, pkMat 28 (Gb.getD i 0) = blowMat (G i)) (w : List (Fin 6 × Bool)) :
    pkMat 28 (CFSG.KC.Misc.G24.wordF4 Gb (encG w)) =
      blowMat (wordProd (fun l : Fin 6 × Bool => G l.1.val) w) := by
  induction w with
  | nil =>
    show pkMat 28 (CFSG.KC.Misc.G24.oneF2 28) = blowMat 1
    rw [pkMat_oneF2, blowMat_one]
  | cons l w ih =>
    have hl : encL l / 2 = l.1.val := by
      unfold encL
      split <;> omega
    have e : CFSG.KC.Misc.G24.wordF4 Gb (encG (l :: w)) =
        CFSG.KC.Misc.G24.mulF2 28 (Gb.getD l.1.val 0)
          (CFSG.KC.Misc.G24.wordF4 Gb (encG w)) := by
      show CFSG.KC.Misc.G24.mulF2 28 (CFSG.KC.Misc.G24.nthV Gb (encL l / 2))
        (CFSG.KC.Misc.G24.wordF4 Gb (encG w)) = _
      rw [nthV_eq, hl]
    rw [e, pkMat_mulF2, ih, hG l.1.val l.1.isLt]
    show _ = blowMat (G l.1.val * wordProd (fun l : Fin 6 × Bool => G l.1.val) w)
    rw [blowMat_mul]

end CFSG.KC.Misc.Spec

end
