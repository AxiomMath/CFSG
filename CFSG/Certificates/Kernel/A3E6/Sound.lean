module

public import Certificates.Data.Kernel.A3E6.Frames
public import CFSG.Certificates.Kernel.A3E6.GlueFrame
public import CFSG.LieType.Chevalley.C2E6RootOperators

public section

namespace CFSG.KC.A3E6

open Certificates.A3E6K CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType.LieCore.A3E6K
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm)
open CFSG.LieType.Chevalley (IsRoot.neg)
open CFSG.StandardType.LieCore (ggLiePair)
open Matrix

abbrev rt (k : ℕ) : E6V := e6Certificate.root k

@[expose] noncomputable def fh (f : List (List (List ℕ))) (k : ℕ) : ℕ := nth (hdH f) k

@[expose] noncomputable def decode (f : List (List (List ℕ))) : Frame where
  p := rt (fh f 0)
  q := rt (fh f 1)
  r := rt (fh f 2)
  b₀ := rt (fh f 3)
  b₁ := rt (fh f 4)
  v := decodeVec (fh f 5)
  A := fun k j => (aX (fh f 6) k j : ℤ) - 64

@[expose] def framesOf (Ls : List (List (List (List (List ℕ))))) : Set Frame :=
  {F | ∃ f ∈ Ls.flatten, F = decode f}

theorem andB_eq_true {a b : Bool} : Certificates.A3E6K.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [Certificates.A3E6K.andB]

theorem notB_eq_true {a : Bool} : Certificates.A3E6K.notB a = true ↔ a = false := by
  cases a <;> simp [Certificates.A3E6K.notB]

theorem beq_true {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem allN_sound {n : ℕ} {f : ℕ → Bool} (h : allN n f = true) : ∀ k < n, f k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have h' : Certificates.A3E6K.andB (f n) (allN n f) = true := h
    obtain ⟨h1, h2⟩ := andB_eq_true.mp h'
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h2 k hk
    · exact h1

theorem letNB_eq (y : ℕ) (k : ℕ → Bool) : letNB y k = k y := by
  cases y <;> rfl

theorem sumN_six (f : ℕ → ℕ) : sumN 6 f = 0 + f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := rfl

theorem fld_eq (x w i : ℕ) : fld x w i = x / 2 ^ (w * i) % 2 ^ w := by
  change (x >>> (w * i)) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fld_lt (x w i : ℕ) : fld x w i < 2 ^ w := by
  rw [fld_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem bitB_eq (x n : ℕ) : bitB x n = x.testBit n := by
  change Nat.blt 0 (x &&& (1 <<< n)) = _
  rw [Nat.one_shiftLeft]
  cases hb : x.testBit n
  · have h0 : x &&& 2 ^ n = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : n = i
      · subst hi
        simp [hb]
      · simp [hi]
    rw [h0]
    rfl
  · have hne : x &&& 2 ^ n ≠ 0 := fun h0 => by
      have := congrArg (fun y => y.testBit n) h0
      simp [Nat.testBit_and, Nat.testBit_two_pow, hb] at this
    simpa [Nat.blt_eq] using Nat.pos_of_ne_zero hne

theorem cd_eq (c j : ℕ) : cd c j = c / 16 ^ j % 16 := by
  change (c >>> (4 * j)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem dv (c : ℕ) (j : Fin 6) : decodeVec (τ := Tag.E6) c j = (cd c j.val : ℤ) - 8 := by
  rw [cd_eq]
  rfl

theorem dv' (c : ℕ) (j : Fin Tag.E6.rank) : decodeVec (τ := Tag.E6) c j = (cd c j.val : ℤ) - 8 := by
  rw [cd_eq]
  rfl

theorem rel_eq (T i k : ℕ) (hk : k < 72) : rel T i k = (row72 T i).testBit k := by
  change bitB T (72 * i + k) = (fld T 72 i).testBit k
  rw [bitB_eq, fld_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hk, Nat.add_comm]

theorem maskN_testBit (n : ℕ) (g : ℕ → Bool) (k : ℕ) :
    (maskN n g).testBit k = (decide (k < n) && g k) := by
  induction n with
  | zero =>
    change (0 : ℕ).testBit k = _
    simp
  | succ n ih =>
    change (maskN n g ||| Bool.rec (motive := fun _ => ℕ) 0 (1 <<< n) (g n)).testBit k = _
    rw [Nat.testBit_or, ih]
    by_cases hkn : k = n
    · subst hkn
      cases hg : g k <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow]
    · have hlt : (k < n + 1) = (k < n) := by
        apply propext
        omega
      cases hg : g n <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hlt, Ne.symm hkn]

theorem popc_eq (x n : ℕ) :
    popc x n = ((Finset.range n).filter fun k => x.testBit k = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change popc x n + ((x >>> n) &&& 1) = _
    rw [ih, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Finset.range_add_one,
      Finset.filter_insert]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases h : x / 2 ^ n % 2 = 1
    · rw [if_pos (by simp [h]), Finset.card_insert_of_notMem (by simp), h]
    · rw [if_neg (by simp [h])]
      omega

theorem iform_e6 (x y : Fin 6 → ℤ) : iform (τ := Tag.E6) x y =
    2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5)
      - (x 0 * y 2 + x 2 * y 0) - (x 1 * y 3 + x 3 * y 1) - (x 2 * y 3 + x 3 * y 2)
      - (x 3 * y 4 + x 4 * y 3) - (x 4 * y 5 + x 5 * y 4) := by
  have hC : Tag.E6.symmetrizedCartan = (!![2, 0, -1, 0, 0, 0; 0, 2, 0, -1, 0, 0;
      -1, 0, 2, -1, 0, 0; 0, -1, -1, 2, -1, 0; 0, 0, 0, -1, 2, -1; 0, 0, 0, 0, -1, 2] :
      Matrix (Fin 6) (Fin 6) ℤ) := by
    funext i j
    fin_cases i <;> fin_cases j <;> decide
  change ∑ i : Fin 6, ∑ j : Fin 6, x i * Tag.E6.symmetrizedCartan i j * y j = _
  rw [hC]
  simp only [Fin.sum_univ_six]
  simp
  ring

theorem fpos_eq (x y : ℕ) : fpos x y =
    2 * (0 + (cd x 0 * cd y 0 + 64) + (cd x 1 * cd y 1 + 64) + (cd x 2 * cd y 2 + 64) +
      (cd x 3 * cd y 3 + 64) + (cd x 4 * cd y 4 + 64) + (cd x 5 * cd y 5 + 64)) +
    8 * ((cd x 0 + cd y 2 + (cd x 2 + cd y 0)) + (cd x 1 + cd y 3 + (cd x 3 + cd y 1)) +
      (cd x 2 + cd y 3 + (cd x 3 + cd y 2)) + (cd x 3 + cd y 4 + (cd x 4 + cd y 3)) +
      (cd x 4 + cd y 5 + (cd x 5 + cd y 4))) := rfl

theorem fneg_eq (x y : ℕ) : fneg x y =
    16 * (0 + (cd x 0 + cd y 0) + (cd x 1 + cd y 1) + (cd x 2 + cd y 2) + (cd x 3 + cd y 3) +
      (cd x 4 + cd y 4) + (cd x 5 + cd y 5)) +
    ((cd x 0 * cd y 2 + cd x 2 * cd y 0 + 128) + (cd x 1 * cd y 3 + cd x 3 * cd y 1 + 128) +
      (cd x 2 * cd y 3 + cd x 3 * cd y 2 + 128) + (cd x 3 * cd y 4 + cd x 4 * cd y 3 + 128) +
      (cd x 4 * cd y 5 + cd x 5 * cd y 4 + 128)) := rfl

theorem fpos_sub_fneg (x y : ℕ) :
    (fpos x y : ℤ) - fneg x y = iform (decodeVec (τ := Tag.E6) x) (decodeVec y) := by
  rw [iform_e6 (decodeVec (τ := Tag.E6) x) (decodeVec (τ := Tag.E6) y)]
  simp only [dv]
  rw [fpos_eq, fneg_eq]
  push_cast
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  have h3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have h4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  rw [h3, h4, h5]
  ring

theorem formZ_iff (x y : ℕ) :
    formZ x y = true ↔ iform (decodeVec (τ := Tag.E6) x) (decodeVec y) = 0 := by
  have h := fpos_sub_fneg x y
  rw [formZ, beq_true]
  omega

theorem formM_iff (x y : ℕ) :
    formM x y = true ↔ iform (decodeVec (τ := Tag.E6) x) (decodeVec y) = -1 := by
  have h := fpos_sub_fneg x y
  change Nat.beq (fpos x y + 1) (fneg x y) = true ↔ _
  rw [beq_true]
  omega

theorem rootsOK_aux {R : ℕ} : ∀ (C : List ℕ) (k : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun k => Nat.beq k 72)
      (fun c _ ih k => Certificates.A3E6K.andB (Nat.beq (rc R k) c) (ih (Nat.succ k))) C k = true →
    ∀ i < C.length, rc R (k + i) = C.getD i 0
  | [], _, _, i, hi => absurd hi (by simp)
  | c :: C, k, h, i, hi => by
    have h' : Certificates.A3E6K.andB (Nat.beq (rc R k) c) (List.rec (motive := fun _ => ℕ → Bool)
        (fun k => Nat.beq k 72) (fun c _ ih k => Certificates.A3E6K.andB (Nat.beq (rc R k) c) (ih (Nat.succ k)))
        C (k + 1)) = true := h
    obtain ⟨h1, h2⟩ := andB_eq_true.mp h'
    cases i with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ i =>
      have := rootsOK_aux C (k + 1) h2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem length_roots : e6Certificate.roots.length = 72 := by decide

theorem roots_sound {R : ℕ} (h : rootsOK R e6Certificate.roots = true) {k : ℕ} (hk : k < 72) :
    decodeVec (rc R k) = rt k := by
  have := rootsOK_aux _ 0 h k (by rw [length_roots]; exact hk)
  rw [Nat.zero_add] at this
  rw [this]
  rfl

theorem masks_sound {R Z N : ℕ} (hR : rootsOK R e6Certificate.roots = true)
    (h : ∀ i < 72, masksAt R Z N i = true) {i k : ℕ} (hi : i < 72) (hk : k < 72) :
    (rel Z i k = true ↔ iform (rt i) (rt k) = 0) ∧
      (rel N i k = true ↔ iform (rt i) (rt k) = -1) := by
  obtain ⟨hz, hn⟩ := andB_eq_true.mp (h i hi)
  rw [rel_eq _ _ _ hk, rel_eq _ _ _ hk, beq_true.mp hz, beq_true.mp hn, maskN_testBit,
    maskN_testBit]
  simp only [hk, decide_true, Bool.true_and]
  rw [formZ_iff, formM_iff, roots_sound hR hi, roots_sound hR hk]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem framesStruct_sound {R Z N P t₀ t₁ : ℕ} {L : List (List (List (List ℕ)))}
    (h : framesStruct R Z N P L t₀ t₁ = true) :
    t₀ + L.length = t₁ ∧ ∀ r (hr : r < L.length), structOK R Z N P (hdH L[r]) (t₀ + r) = true := by
  induction L generalizing t₀ with
  | nil => exact ⟨by simpa [framesStruct] using h, fun r hr => absurd hr (by simp)⟩
  | cons f L ih =>
    have h' : Certificates.A3E6K.andB (structOK R Z N P (hdH f) t₀) (framesStruct R Z N P L (t₀ + 1) t₁) = true := h
    obtain ⟨h1, h2⟩ := andB_eq_true.mp h'
    obtain ⟨ih1, ih2⟩ := ih h2
    refine ⟨by simp only [List.length_cons]; omega, fun r hr => ?_⟩
    cases r with
    | zero => simpa using h1
    | succ r =>
      have := ih2 r (by simpa using hr)
      simpa [Nat.add_assoc, Nat.add_comm 1 r] using this

theorem framesTags_sound {tw : Bool} {R Z : ℕ} {L : List (List (List (List ℕ)))}
    (h : framesTags tw R Z L = true) :
    ∀ f ∈ L, tagsOK tw R Z (hdH f) (nthLL f (if tw then 1 else 2)) = true := by
  induction L with
  | nil => simp
  | cons f L ih =>
    have h' : Certificates.A3E6K.andB (tagsOK tw R Z (hdH f)
        (nthLL f (Bool.rec (motive := fun _ => Nat) 2 1 tw))) (framesTags tw R Z L) = true := h
    obtain ⟨h1, h2⟩ := andB_eq_true.mp h'
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · cases tw <;> simpa using h1
    · exact ih h2 g hg

theorem structOK_parts {R Z N P t : ℕ} {h : List ℕ} (hs : structOK R Z N P h t = true) :
    (∀ k < 5, nth h k < 72) ∧
    (rel N (nth h 0) (nth h 1) = true ∧ rel N (nth h 1) (nth h 2) = true ∧
      rel Z (nth h 0) (nth h 2) = true ∧ rel Z (nth h 3) (nth h 4) = true) ∧
    popc (row72 Z (nth h 0) &&& (row72 Z (nth h 1) &&& row72 Z (nth h 2))) 72 = 4 ∧
    (rel Z (nth h 0) (nth h 3) = true ∧ rel Z (nth h 1) (nth h 3) = true ∧
      rel Z (nth h 2) (nth h 3) = true) ∧
    (rel Z (nth h 0) (nth h 4) = true ∧ rel Z (nth h 1) (nth h 4) = true ∧
      rel Z (nth h 2) (nth h 4) = true) ∧
    popc (row72 Z (nth h 3) &&& row72 Z (nth h 4)) 72 = 12 ∧
    fld P 72 t = (row72 Z (nth h 3) &&& row72 Z (nth h 4)) ∧
    (∀ k < 5, formZ (nth h 5) (rc R (nth h k)) = true) ∧
    (∀ i < 6, ∀ j < 6, (sumN 6 fun k => cd (fld (bP R h) 24 k) i * aX (nth h 6) k j) + 3072 =
      Bool.rec (motive := fun _ => ℕ) 0 8 (Nat.beq i j) +
        (64 * sumN 6 (fun k => cd (fld (bP R h) 24 k) i) +
          8 * sumN 6 (fun k => aX (nth h 6) k j))) := by
  unfold structOK at hs
  simp only [andB_eq_true, beq_true, letNB_eq] at hs
  obtain ⟨h1, ⟨h2a, h2b, h2c, h2d⟩, ⟨h3, ⟨h4a, h4b, h4c⟩, h5a, h5b, h5c⟩, ⟨h6, h7⟩, h8, h9⟩ := hs
  exact ⟨fun k hk => by simpa [Nat.blt_eq] using allN_sound h1 k hk, ⟨h2a, h2b, h2c, h2d⟩, h3, ⟨h4a, h4b, h4c⟩, ⟨h5a, h5b, h5c⟩, h6, h7,
    allN_sound h8, fun i hi j hj => beq_true.mp (allN_sound (allN_sound h9 i hi) j hj)⟩

theorem codes_lt : ∀ i < 72, e6Certificate.roots.getD i 0 < 16 ^ 6 := by decide +kernel

theorem codes_inj : ∀ i < 72, ∀ j < 72,
    e6Certificate.roots.getD i 0 = e6Certificate.roots.getD j 0 → i = j := by decide +kernel

theorem decodeVec_inj {a b : ℕ} (ha : a < 16 ^ 6) (hb : b < 16 ^ 6)
    (h : decodeVec (τ := Tag.E6) a = decodeVec b) : a = b := by
  have e : ∀ j (hj : j < 6), a / 16 ^ j % 16 = b / 16 ^ j % 16 := fun j hj => by
    have := congrFun h ⟨j, hj⟩
    rw [dv', dv', cd_eq, cd_eq] at this
    simp only [Fin.val_mk, sub_left_inj, Nat.cast_inj] at this
    exact this
  have e0 := e 0 (by norm_num)
  have e1 := e 1 (by norm_num)
  have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num)
  have e4 := e 4 (by norm_num)
  have e5 := e 5 (by norm_num)
  norm_num at e0 e1 e2 e3 e4 e5 ha hb
  omega

theorem rt_inj {i j : ℕ} (hi : i < 72) (hj : j < 72) (h : rt i = rt j) : i = j :=
  codes_inj i hi j hj (decodeVec_inj (codes_lt i hi) (codes_lt j hj) h)

theorem testBit_row_and {T a b k : ℕ} (hk : k < 72) :
    (row72 T a &&& row72 T b).testBit k = true ↔ rel T a k = true ∧ rel T b k = true := by
  rw [Nat.testBit_and, rel_eq _ _ _ hk, rel_eq _ _ _ hk, Bool.and_eq_true]

theorem cd_fld_bP {R : ℕ} {h : List ℕ} {k i : ℕ} (hk : k < 6) (hi : i < 6) :
    cd (fld (bP R h) 24 k) i = cd (colc R h k) i := by
  have hc0 : colc R h 0 < 2 ^ 24 := fld_lt _ _ _
  have hc1 : colc R h 1 < 2 ^ 24 := fld_lt _ _ _
  have hc2 : colc R h 2 < 2 ^ 24 := fld_lt _ _ _
  have hc3 : colc R h 3 < 2 ^ 24 := fld_lt _ _ _
  have hc4 : colc R h 4 < 2 ^ 24 := fld_lt _ _ _
  have hb : bP R h = colc R h 0 * 2 ^ (24 * 0) + colc R h 1 * 2 ^ (24 * 1) +
      colc R h 2 * 2 ^ (24 * 2) + colc R h 3 * 2 ^ (24 * 3) + colc R h 4 * 2 ^ (24 * 4) +
      colc R h 5 * 2 ^ (24 * 5) := by
    change sumN 6 (fun k => colc R h k <<< (24 * k)) = _
    rw [sumN_six]
    simp only [Nat.shiftLeft_eq, Nat.zero_add]
  have hfld : fld (bP R h) 24 k = colc R h k % 2 ^ 24 := by
    rw [fld_eq, hb]
    simp only [Nat.reducePow, Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 ⊢
    interval_cases k <;> omega
  rw [hfld, cd_eq, cd_eq]
  generalize colc R h k = c
  interval_cases i <;> simp only [Nat.reducePow] <;> omega

theorem isRoot_rt {k : ℕ} (hk : k < 72) : IsRoot Tag.E6 (rt k) :=
  CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root ⟨k, hk⟩

theorem exists_rt {γ : E6V} (hγ : IsRoot Tag.E6 γ) : ∃ k < 72, rt k = γ := by
  obtain ⟨k, hk⟩ := CFSG.LieType.Chevalley.C2E6Std.exists_e6Root_eq hγ
  exact ⟨k.val, k.isLt, hk⟩

theorem decode_p (f : List (List (List ℕ))) : (decode f).p = rt (nth (hdH f) 0) := rfl
theorem decode_q (f : List (List (List ℕ))) : (decode f).q = rt (nth (hdH f) 1) := rfl
theorem decode_r (f : List (List (List ℕ))) : (decode f).r = rt (nth (hdH f) 2) := rfl
theorem decode_b₀ (f : List (List (List ℕ))) : (decode f).b₀ = rt (nth (hdH f) 3) := rfl
theorem decode_b₁ (f : List (List (List ℕ))) : (decode f).b₁ = rt (nth (hdH f) 4) := rfl
theorem decode_col {R : ℕ} (hR : rootsOK R e6Certificate.roots = true)
    {f : List (List (List ℕ))} (hlt : ∀ k < 5, nth (hdH f) k < 72) (k : Fin 6) :
    (decode f).col k = decodeVec (colc R (hdH f) k) := by
  fin_cases k
  · exact (roots_sound hR (hlt 0 (by norm_num))).symm
  · exact (roots_sound hR (hlt 1 (by norm_num))).symm
  · exact (roots_sound hR (hlt 2 (by norm_num))).symm
  · exact (roots_sound hR (hlt 3 (by norm_num))).symm
  · exact (roots_sound hR (hlt 4 (by norm_num))).symm
  · rfl

theorem decode_BA {R : ℕ} (hR : rootsOK R e6Certificate.roots = true)
    {f : List (List (List ℕ))} (hlt : ∀ k < 5, nth (hdH f) k < 72)
    (hBA : ∀ i < 6, ∀ j < 6,
      (sumN 6 fun k => cd (fld (bP R (hdH f)) 24 k) i * aX (nth (hdH f) 6) k j) + 3072 =
      Bool.rec (motive := fun _ => ℕ) 0 8 (Nat.beq i j) +
        (64 * sumN 6 (fun k => cd (fld (bP R (hdH f)) 24 k) i) +
          8 * sumN 6 (fun k => aX (nth (hdH f) 6) k j))) :
    (decode f).B * (decode f).A = (8 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) := by
  ext i j
  have hc := hBA i.val i.isLt j.val j.isLt
  simp only [sumN_six] at hc
  rw [cd_fld_bP (by norm_num) i.isLt, cd_fld_bP (by norm_num) i.isLt,
    cd_fld_bP (by norm_num) i.isLt, cd_fld_bP (by norm_num) i.isLt,
    cd_fld_bP (by norm_num) i.isLt, cd_fld_bP (by norm_num) i.isLt] at hc
  change ∑ k : Fin 6, (decode f).col k i * ((aX (nth (hdH f) 6) k j : ℤ) - 64) = _
  simp only [decode_col hR hlt, dv', Fin.sum_univ_six, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  have hij : (i = j) ↔ (i.val = j.val) := Fin.ext_iff
  by_cases h : i = j
  · have h' : Nat.beq i.val j.val = true := beq_true.mpr (hij.mp h)
    rw [h'] at hc
    rw [if_pos h]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hc ⊢
    push_cast [mul_one]
    have h3 : ((3 : Fin 6) : ℕ) = 3 := rfl
    have h4 : ((4 : Fin 6) : ℕ) = 4 := rfl
    have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
    rw [h3, h4, h5]
    have hc' := congrArg (fun n : ℕ => (n : ℤ)) hc
    push_cast at hc'
    linear_combination hc'
  · have h' : Nat.beq i.val j.val = false := by
      cases hb : Nat.beq i.val j.val
      · rfl
      · exact absurd (hij.mpr (beq_true.mp hb)) h
    rw [h'] at hc
    rw [if_neg h]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hc ⊢
    have h3 : ((3 : Fin 6) : ℕ) = 3 := rfl
    have h4 : ((4 : Fin 6) : ℕ) = 4 := rfl
    have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
    rw [h3, h4, h5]
    have hc' := congrArg (fun n : ℕ => (n : ℤ)) hc
    push_cast at hc'
    linear_combination hc'

theorem headsM_testBit {L : List (List ℕ)} {n : ℕ} (h : (headsM L).testBit n = true) :
    ∃ e ∈ L, hd e = n := by
  induction L with
  | nil => simp [headsM] at h
  | cons e L ih =>
    change (headsM L ||| 1 <<< hd e).testBit n = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨e', he', rfl⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', rfl⟩
    · exact ⟨e, List.mem_cons_self, of_decide_eq_true h⟩

theorem resM_testBit {l : List ℕ} {n : ℕ} (h : (resM l).testBit n = true) :
    ∃ x ∈ l, x % 72 = n := by
  induction l with
  | nil => simp [resM] at h
  | cons x l ih =>
    change (resM l ||| 1 <<< (x % 72)).testBit n = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨x', hx', rfl⟩ := ih h
      exact ⟨x', List.mem_cons_of_mem _ hx', rfl⟩
    · exact ⟨x, List.mem_cons_self, of_decide_eq_true h⟩

theorem inFrames_mem {P i j : ℕ} {l : List ℕ} (h : inFrames P i j l = true) :
    ∀ x ∈ l, x / 72 < 270 ∧ bitB (fld P 72 (x / 72)) i = true ∧
      bitB (fld P 72 (x / 72)) j = true ∧ bitB (fld P 72 (x / 72)) (x % 72) = true := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h' : Certificates.A3E6K.andB (Certificates.A3E6K.andB (Nat.blt (x / 72) 270) (Certificates.A3E6K.andB (bitB (fld P 72 (x / 72)) i)
        (Certificates.A3E6K.andB (bitB (fld P 72 (x / 72)) j) (bitB (fld P 72 (x / 72)) (x % 72)))))
        (inFrames P i j l) = true := h
    simp only [andB_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h'
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨h1, h2, h3, h4⟩
    · exact ih h5 y hy

theorem coverAt_parts {Z N P i : ℕ} {row : List (List ℕ)} (h : coverAt Z N P row i = true) :
    headsM row = row72 N i ∧ ∀ e ∈ row, resM (tl e) = (row72 N (hd e) &&& row72 Z i) ∧
      inFrames P i (hd e) (tl e) = true := by
  have h' : Certificates.A3E6K.andB (Nat.beq (headsM row) (row72 N i))
      (List.rec (motive := fun _ => Bool) true
        (fun e _ ih => Certificates.A3E6K.andB (Certificates.A3E6K.andB (Nat.beq (resM (tl e)) (row72 N (hd e) &&& row72 Z i))
          (inFrames P i (hd e) (tl e))) ih) row) = true := h
  obtain ⟨h1, h2⟩ := andB_eq_true.mp h'
  refine ⟨beq_true.mp h1, ?_⟩
  clear h h' h1
  induction row with
  | nil => simp
  | cons e row ih =>
    obtain ⟨ha, hb⟩ := andB_eq_true.mp (andB_eq_true.mp h2).1
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨beq_true.mp ha, hb⟩
    · exact ih (andB_eq_true.mp h2).2 e' he'

theorem frame_facts {R Z N P t : ℕ} (hR : rootsOK R e6Certificate.roots = true)
    (hM : ∀ i < 72, masksAt R Z N i = true) {f : List (List (List ℕ))}
    (hs : structOK R Z N P (hdH f) t = true) : FrameFacts (decode f) := by
  obtain ⟨hlt, ⟨-, -, -, hbb⟩, h4, ⟨hp3, hq3, hr3⟩, ⟨hp4, hq4, hr4⟩, h12, -, hv, hBA⟩ :=
    structOK_parts hs
  have l0 := hlt 0 (by norm_num)
  have l1 := hlt 1 (by norm_num)
  have l2 := hlt 2 (by norm_num)
  have l3 := hlt 3 (by norm_num)
  have l4 := hlt 4 (by norm_num)
  have mZ : ∀ {i k : ℕ}, i < 72 → k < 72 → (rel Z i k = true ↔ iform (rt i) (rt k) = 0) :=
    fun hi hk => (masks_sound hR hM hi hk).1
  have mZ' : ∀ {i k : ℕ}, i < 72 → k < 72 → (rel Z i k = true ↔ iform (rt k) (rt i) = 0) :=
    fun hi hk => by rw [mZ hi hk, iform_comm]
  have hvk : ∀ k < 5, iform (decodeVec (τ := Tag.E6) (nth (hdH f) 5)) (rt (nth (hdH f) k)) = 0 :=
    fun k hk => by
      have := (formZ_iff _ _).mp (hv k hk)
      rwa [roots_sound hR (hlt k hk)] at this
  set p := nth (hdH f) 0 with hpdef
  set q := nth (hdH f) 1 with hqdef
  set r := nth (hdH f) 2 with hrdef
  set b₀ := nth (hdH f) 3 with hb₀def
  set b₁ := nth (hdH f) 4 with hb₁def
  have v00 := iform_root_self (isRoot_rt l3)
  have v11 := iform_root_self (isRoot_rt l4)
  have v01 : iform (rt b₀) (rt b₁) = 0 := (mZ l3 l4).mp hbb
  have v10 : iform (rt b₁) (rt b₀) = 0 := by rw [iform_comm]; exact v01
  have z3 : iform (rt b₀) (rt p) = 0 ∧ iform (rt b₀) (rt q) = 0 ∧ iform (rt b₀) (rt r) = 0 :=
    ⟨(mZ' l0 l3).mp hp3, (mZ' l1 l3).mp hq3, (mZ' l2 l3).mp hr3⟩
  have z4 : iform (rt b₁) (rt p) = 0 ∧ iform (rt b₁) (rt q) = 0 ∧ iform (rt b₁) (rt r) = 0 :=
    ⟨(mZ' l0 l4).mp hp4, (mZ' l1 l4).mp hq4, (mZ' l2 l4).mp hr4⟩
  refine
    { hp := isRoot_rt l0
      hq := isRoot_rt l1
      hr := isRoot_rt l2
      hb₀ := isRoot_rt l3
      hb₁ := isRoot_rt l4
      hbb := v01
      perp_iff := ?_
      perp_card := ?_
      vp := hvk 0 (by norm_num)
      vq := hvk 1 (by norm_num)
      vr := hvk 2 (by norm_num)
      vb₀ := hvk 3 (by norm_num)
      vb₁ := hvk 4 (by norm_num)
      hBA := decode_BA hR hlt hBA }
  · intro γ hγ
    obtain ⟨k, hk, rfl⟩ := exists_rt hγ
    rw [decode_p, decode_q, decode_r, decode_b₀, decode_b₁, ← hpdef, ← hqdef, ← hrdef, ← hb₀def,
      ← hb₁def]
    constructor
    · rintro ⟨h0, h1, h2⟩
      obtain ⟨n₀, hn₀, en₀⟩ := exists_rt (IsRoot.neg (isRoot_rt l3))
      obtain ⟨n₁, hn₁, en₁⟩ := exists_rt (IsRoot.neg (isRoot_rt l4))
      let S := (Finset.range 72).filter fun g =>
        (row72 Z p &&& (row72 Z q &&& row72 Z r)).testBit g = true
      have hS : S.card = 4 := by rw [← popc_eq]; exact h4
      have memS : ∀ g < 72, iform (rt g) (rt p) = 0 → iform (rt g) (rt q) = 0 →
          iform (rt g) (rt r) = 0 → g ∈ S := by
        intro g hg e0 e1 e2
        simp only [S, Finset.mem_filter, Finset.mem_range, Nat.testBit_and, rel_eq _ _ _ hg,
          Bool.and_eq_true]
        refine ⟨hg, ?_, ?_, ?_⟩
        · rw [← rel_eq _ _ _ hg]; exact (mZ' l0 hg).mpr e0
        · rw [← rel_eq _ _ _ hg]; exact (mZ' l1 hg).mpr e1
        · rw [← rel_eq _ _ _ hg]; exact (mZ' l2 hg).mpr e2
      have m3 : b₀ ∈ S := memS _ l3 z3.1 z3.2.1 z3.2.2
      have m4 : b₁ ∈ S := memS _ l4 z4.1 z4.2.1 z4.2.2
      have mn₀ : n₀ ∈ S := memS _ hn₀ (by rw [en₀, iform_neg_left, z3.1, neg_zero])
        (by rw [en₀, iform_neg_left, z3.2.1, neg_zero])
        (by rw [en₀, iform_neg_left, z3.2.2, neg_zero])
      have mn₁ : n₁ ∈ S := memS _ hn₁ (by rw [en₁, iform_neg_left, z4.1, neg_zero])
        (by rw [en₁, iform_neg_left, z4.2.1, neg_zero])
        (by rw [en₁, iform_neg_left, z4.2.2, neg_zero])
      have mk : k ∈ S := memS _ hk h0 h1 h2
      by_contra hne
      simp only [not_or] at hne
      obtain ⟨ne0, nn0, ne1, nn1⟩ := hne
      have d01 : b₀ ≠ b₁ := fun e => by rw [e, v11] at v01; norm_num at v01
      have d0n0 : b₀ ≠ n₀ := fun e => by
        rw [← e] at en₀
        have := congrArg (fun x => iform (rt b₀) x) en₀
        simp only [iform_neg_right, v00] at this
        norm_num at this
      have d0n1 : b₀ ≠ n₁ := fun e => by
        have := congrArg (fun x => iform x (rt b₁)) en₁
        rw [← e] at this
        simp only [iform_neg_left, v01, v11] at this
        norm_num at this
      have d1n0 : b₁ ≠ n₀ := fun e => by
        have := congrArg (fun x => iform x (rt b₀)) en₀
        rw [← e] at this
        simp only [iform_neg_left, v10, v00] at this
        norm_num at this
      have d1n1 : b₁ ≠ n₁ := fun e => by
        have := congrArg (fun x => iform (rt b₁) x) en₁
        rw [← e] at this
        simp only [iform_neg_right, v11] at this
        norm_num at this
      have dn : n₀ ≠ n₁ := fun e => by
        have := congrArg (fun x => iform (rt b₀) x) (en₀.symm.trans (e ▸ en₁))
        simp only [iform_neg_right, v00, v01] at this
        norm_num at this
      have dk0 : k ≠ b₀ := fun e => ne0 (by rw [e])
      have dk1 : k ≠ b₁ := fun e => ne1 (by rw [e])
      have dkn0 : k ≠ n₀ := fun e => nn0 (by rw [e, en₀])
      have dkn1 : k ≠ n₁ := fun e => nn1 (by rw [e, en₁])
      have hsub : ({k, b₀, b₁, n₀, n₁} : Finset ℕ) ⊆ S := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hcard : ({k, b₀, b₁, n₀, n₁} : Finset ℕ).card = 5 := by
        rw [Finset.card_insert_of_notMem (by simp [dk0, dk1, dkn0, dkn1]),
          Finset.card_insert_of_notMem (by simp [d01, d0n0, d0n1]),
          Finset.card_insert_of_notMem (by simp [d1n0, d1n1]), Finset.card_pair dn]
      have := Finset.card_le_card hsub
      omega
    · intro hb
      rcases hb with e | e | e | e <;> rw [e]
      · exact z3
      · simp only [iform_neg_left, z3.1, z3.2.1, z3.2.2, neg_zero, and_self]
      · exact z4
      · simp only [iform_neg_left, z4.1, z4.2.1, z4.2.2, neg_zero, and_self]
  · let T := (Finset.range 72).filter fun g => (row72 Z b₀ &&& row72 Z b₁).testBit g = true
    have hT : T.card = 12 := by rw [← popc_eq]; exact h12
    have hset : (decode f).perp = rt '' (T : Set ℕ) := by
      ext γ
      rw [Frame.perp, decode_b₀, decode_b₁, ← hb₀def, ← hb₁def]
      constructor
      · rintro ⟨hγ, e0, e1⟩
        obtain ⟨k, hk, rfl⟩ := exists_rt hγ
        refine ⟨k, ?_, rfl⟩
        simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
        exact ⟨hk, (testBit_row_and hk).mpr ⟨(mZ' l3 hk).mpr e0, (mZ' l4 hk).mpr e1⟩⟩
      · rintro ⟨k, hkT, rfl⟩
        simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hkT
        obtain ⟨hk, hb⟩ := hkT
        obtain ⟨e0, e1⟩ := (testBit_row_and hk).mp hb
        exact ⟨isRoot_rt hk, (mZ' l3 hk).mp e0, (mZ' l4 hk).mp e1⟩
    have hinj : Set.InjOn rt (T : Set ℕ) := by
      intro x hx y hy hxy
      simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
      exact rt_inj hx.1 hy.1 hxy
    rw [hset, hinj.ncard_image, Set.ncard_coe_finset, hT]

theorem frames_sound {R Z N P : ℕ} {Ls : List (List (List (List (List ℕ))))}
    (hR : rootsOK R e6Certificate.roots = true) (hM : ∀ i < 72, masksAt R Z N i = true)
    (hS : ∀ c < Ls.length, framesStruct R Z N P (Ls.getD c []) (27 * c) (27 * c + 27) = true) :
    ∀ F ∈ framesOf Ls, FrameFacts F := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨L, hL, hfL⟩ := List.mem_flatten.mp hf
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hfL
  have hg : Ls.getD c [] = Ls[c] := by simp [hc]
  have h := (framesStruct_sound (hS c hc)).2 r (by rw [hg]; exact hr)
  simp only [hg] at h
  exact frame_facts hR hM h

theorem cover_sound {R Z N P : ℕ} {c₀ c₁ : List (List (List ℕ))}
    {Ls : List (List (List (List (List ℕ))))}
    (hR : rootsOK R e6Certificate.roots = true) (hM : ∀ i < 72, masksAt R Z N i = true)
    (hC : ∀ i < 72, coverAt Z N P (cvRow c₀ c₁ i) i = true) (hL : Ls.length = 10)
    (hS : ∀ c < Ls.length, framesStruct R Z N P (Ls.getD c []) (27 * c) (27 * c + 27) = true) :
    Cover (framesOf Ls) := by
  intro i j k hi hj hk hch
  obtain ⟨a, ha, rfl⟩ := exists_rt hi
  obtain ⟨b, hb, rfl⟩ := exists_rt hj
  obtain ⟨c, hc, rfl⟩ := exists_rt hk
  obtain ⟨hab, hbc, hac⟩ := hch
  have rab : rel N a b = true := (masks_sound hR hM ha hb).2.mpr hab
  have rbc : rel N b c = true := (masks_sound hR hM hb hc).2.mpr hbc
  have rac : rel Z a c = true := (masks_sound hR hM ha hc).1.mpr hac
  obtain ⟨hH, hE⟩ := coverAt_parts (hC a ha)
  have h1 : (headsM (cvRow c₀ c₁ a)).testBit b = true := by
    rw [hH, ← rel_eq _ _ _ hb]
    exact rab
  obtain ⟨e, he, rfl⟩ := headsM_testBit h1
  obtain ⟨hres, hin⟩ := hE e he
  have h2 : (resM (tl e)).testBit c = true := by
    rw [hres, Nat.testBit_and, ← rel_eq _ _ _ hc, ← rel_eq _ _ _ hc, rbc, rac]
    rfl
  obtain ⟨x, hx, hxc⟩ := resM_testBit h2
  obtain ⟨ht, bi, bj, bk⟩ := inFrames_mem hin x hx
  rw [hxc] at bk
  have hcl : x / 72 / 27 < Ls.length := by rw [hL]; omega
  obtain ⟨hlen, hst⟩ := framesStruct_sound (hS _ hcl)
  have hr : x / 72 % 27 < (Ls.getD (x / 72 / 27) []).length := by omega
  have hs := hst _ hr
  rw [Nat.div_add_mod] at hs
  obtain ⟨hlt, -, -, -, -, -, hP, -, -⟩ := structOK_parts hs
  have l3 := hlt 3 (by norm_num)
  have l4 := hlt 4 (by norm_num)
  have mZ' : ∀ {i k : ℕ}, i < 72 → k < 72 → (rel Z i k = true ↔ iform (rt k) (rt i) = 0) :=
    fun hi hk => by rw [(masks_sound hR hM hi hk).1, iform_comm]
  have hg : Ls.getD (x / 72 / 27) [] = Ls[x / 72 / 27] := by simp [hcl]
  have orth : ∀ g < 72, bitB (fld P 72 (x / 72)) g = true →
      iform (rt g) (rt (nth (hdH (Ls.getD (x / 72 / 27) [])[x / 72 % 27]) 3)) = 0 ∧
      iform (rt g) (rt (nth (hdH (Ls.getD (x / 72 / 27) [])[x / 72 % 27]) 4)) = 0 := by
    intro g hg' hbit
    rw [bitB_eq, hP, testBit_row_and hg'] at hbit
    exact ⟨(mZ' l3 hg').mp hbit.1, (mZ' l4 hg').mp hbit.2⟩
  refine ⟨decode (Ls.getD (x / 72 / 27) [])[x / 72 % 27], ⟨_, ?_, rfl⟩,
    orth a ha bi, orth _ hb bj, orth c hc bk⟩
  refine List.mem_flatten.mpr ⟨_, ?_, List.getElem_mem hr⟩
  rw [hg]
  exact List.getElem_mem hcl

theorem tagsOK_aux {tw : Bool} {R Z Bp : ℕ} {h : List ℕ} : ∀ (tags : List (List ℕ)) (d : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun d => Nat.beq d 16)
      (fun tg _ ih d => Certificates.A3E6K.andB (tagOK tw R Z h Bp d tg) (ih (Nat.succ d))) tags d = true →
    d + tags.length = 16 ∧ ∀ i < tags.length, tagOK tw R Z h Bp (d + i) (tags.getD i []) = true
  | [], d, hd => ⟨by simpa using beq_true.mp hd, fun i hi => absurd hi (by simp)⟩
  | tg :: tags, d, hd => by
    have h' : Certificates.A3E6K.andB (tagOK tw R Z h Bp d tg) (List.rec (motive := fun _ => ℕ → Bool)
        (fun d => Nat.beq d 16) (fun tg _ ih d => Certificates.A3E6K.andB (tagOK tw R Z h Bp d tg) (ih (Nat.succ d)))
        tags (d + 1)) = true := hd
    obtain ⟨h1, h2⟩ := andB_eq_true.mp h'
    obtain ⟨ih1, ih2⟩ := tagsOK_aux tags (d + 1) h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ i =>
      have := ih2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem tagsOK_parts {tw : Bool} {R Z : ℕ} {h : List ℕ} {tags : List (List ℕ)}
    (ht : tagsOK tw R Z h tags = true) :
    ∀ d < 16, tagOK tw R Z h (bP R h) d (tags.getD d []) = true := by
  rw [tagsOK, letNB_eq] at ht
  obtain ⟨h1, h2⟩ := tagsOK_aux tags 0 ht
  intro d hd
  simpa using h2 d (by omega)

@[expose] def eb (e : ℤ) : ℕ := if e = -1 then 1 else 0

@[expose] def dOf (sw : Bool) (e₀ e₁ e₂ : ℤ) : ℕ :=
  8 * (if sw then 1 else 0) + 4 * eb e₀ + 2 * eb e₁ + eb e₂

theorem dOf_lt (sw : Bool) (e₀ e₁ e₂ : ℤ) : dOf sw e₀ e₁ e₂ < 16 := by
  unfold dOf eb
  split_ifs <;> omega

theorem dbit_eq (d n : ℕ) : dbit d n = d / 2 ^ n % 2 := by
  change (d >>> n) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem sg_cast (e x : ℕ) : (sg e x : ZMod 24) = if e = 1 then -(x : ZMod 24) else x := by
  by_cases he : e = 1
  · subst he
    change ((24 - x % 24 : ℕ) : ZMod 24) = _
    rw [Nat.cast_sub (Nat.mod_lt _ (by norm_num)).le, ZMod.natCast_mod, if_pos rfl]
    have : ((24 : ℕ) : ZMod 24) = 0 := ZMod.natCast_self 24
    rw [this, zero_sub]
  · have hb : Nat.beq e 1 = false := by
      cases hb : Nat.beq e 1
      · rfl
      · exact absurd (beq_true.mp hb) he
    unfold sg
    rw [hb, if_neg he]

theorem yAt_def (Bp d : ℕ) (u : ℕ → ℕ) (i : ℕ) : yAt Bp d u i =
    (b24 Bp 0 i * u 0 + b24 Bp 1 i * u 1 +
      (b24 Bp 2 i * u 2 + sg (dbit d 2) (b24 Bp (3 + dbit d 3) i * u 3)) +
      (sg (dbit d 1) (b24 Bp (4 - dbit d 3) i * u 4) + sg (dbit d 0) (b24 Bp 5 i * u 5))) % 24 :=
  rfl

theorem yAt_lt (Bp d : ℕ) (u : ℕ → ℕ) (i : ℕ) : yAt Bp d u i < 24 := by
  rw [yAt_def]
  exact Nat.mod_lt _ (by norm_num)

theorem B_mulVec (F : Frame) (w : E6V) : (F.B *ᵥ w : E6V) =
    ((w : Fin 6 → ℤ) 0 • F.p + (w : Fin 6 → ℤ) 1 • F.q + (w : Fin 6 → ℤ) 2 • F.r +
      (w : Fin 6 → ℤ) 3 • F.b₀ + (w : Fin 6 → ℤ) 4 • F.b₁ + (w : Fin 6 → ℤ) 5 • F.v : E6V) := by
  ext i
  change ∑ j : Fin 6, F.col j i * (w : Fin 6 → ℤ) j = _
  rw [Fin.sum_univ_six]
  simp only [Frame.col, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [mul_comm (F.p i), mul_comm (F.q i), mul_comm (F.r i), mul_comm (F.b₀ i), mul_comm (F.b₁ i),
    mul_comm (F.v i)]
  rfl

theorem b24_cast {R : ℕ} (hR : rootsOK R e6Certificate.roots = true)
    {f : List (List (List ℕ))} (hlt : ∀ k < 5, nth (hdH f) k < 72) (k : Fin 6) (i : Fin 6) :
    (b24 (bP R (hdH f)) k i : ZMod 24) = (((decode f).col k i : ℤ) : ZMod 24) := by
  change (((cd (fld (bP R (hdH f)) 24 k) i + 16) % 24 : ℕ) : ZMod 24) = _
  rw [ZMod.natCast_mod, cd_fld_bP k.isLt i.isLt, decode_col hR hlt, dv]
  push_cast
  have : ((24 : ℤ) : ZMod 24) = 0 := by decide
  linear_combination this

theorem eight_mulVec {f : Frame} (hF : FrameFacts f) {z : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    {sw : Bool} {e₀ e₁ e₂ : ℤ} (hfix : Fixes f z) (him : ColImages f z sw e₀ e₁ e₂) (u : E6V)
    (i : Fin Tag.E6.rank) :
    8 * (z *ᵥ u) i = (f.A *ᵥ u) (0 : Fin 6) * f.p i + (f.A *ᵥ u) (1 : Fin 6) * f.q i +
      (f.A *ᵥ u) (2 : Fin 6) * f.r i +
      (f.A *ᵥ u) (3 : Fin 6) * (e₀ * (if sw then f.b₁ else f.b₀) i) +
      (f.A *ᵥ u) (4 : Fin 6) * (e₁ * (if sw then f.b₀ else f.b₁) i) +
      (f.A *ᵥ u) (5 : Fin 6) * (e₂ * f.v i) := by
  have hB := Frame.B_mulVec_A f hF u
  rw [B_mulVec] at hB
  have h := congrArg (fun x => z *ᵥ x) hB
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hfix.1, hfix.2.1, hfix.2.2, him.2.2.2.1,
    him.2.2.2.2.1, him.2.2.2.2.2] at h
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
  exact hi.symm

theorem yAt_eq {R : ℕ} (hR : rootsOK R e6Certificate.roots = true)
    {f : List (List (List ℕ))} (hlt : ∀ k < 5, nth (hdH f) k < 72) (hF : FrameFacts (decode f))
    {z : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ} {sw : Bool} {e₀ e₁ e₂ : ℤ}
    (hfix : Fixes (decode f) z) (him : ColImages (decode f) z sw e₀ e₁ e₂) (u : E6V)
    (w : ℕ → ℕ) (hw : ∀ k : Fin 6, (w k : ZMod 24) = (((decode f).A *ᵥ u) k : ZMod 24))
    (i : Fin 6) :
    (yAt (bP R (hdH f)) (dOf sw e₀ e₁ e₂) w i : ZMod 24) = ((8 * (z *ᵥ u) i : ℤ) : ZMod 24) := by
  have h8 := eight_mulVec hF hfix him u i
  have hb := b24_cast hR hlt
  have hb0 := hb 0 i
  have hb1 := hb 1 i
  have hb2 := hb 2 i
  have hb3 := hb 3 i
  have hb4 := hb 4 i
  have hb5 := hb 5 i
  have hw0 := hw 0
  have hw1 := hw 1
  have hw2 := hw 2
  have hw3 := hw 3
  have hw4 := hw 4
  have hw5 := hw 5
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hb0 hb1 hb2 hw0 hw1 hw2
  have v3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have v5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  rw [v3] at hb3 hw3
  rw [v4] at hb4 hw4
  rw [v5] at hb5 hw5
  rw [h8, yAt_def, ZMod.natCast_mod]
  obtain ⟨he₀, he₁, he₂, -⟩ := him
  push_cast
  cases sw <;> rcases he₀ with rfl | rfl <;> rcases he₁ with rfl | rfl <;>
    rcases he₂ with rfl | rfl <;>
    simp only [dOf, eb, dbit_eq, sg_cast, Nat.cast_mul, if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false] at hb0 hb1 hb2 hb3 hb4 hb5 ⊢ <;>
    norm_num <;>
    simp only [Frame.col] at hb0 hb1 hb2 hb3 hb4 hb5 <;>
    rw [hb0, hb1, hb2, hb3, hb4, hb5, hw0, hw1, hw2, hw3, hw4, hw5] <;>
    simp [Frame.col] <;>
    first | rfl | ring

theorem aE_cast (A k j : ℕ) : (aE A k j : ZMod 24) = ((((aX A k j : ℤ) - 64 : ℤ)) : ZMod 24) := by
  change (((aX A k j + 8) % 24 : ℕ) : ZMod 24) = _
  rw [ZMod.natCast_mod]
  push_cast
  have : ((72 : ℤ) : ZMod 24) = 0 := by decide
  linear_combination this

theorem uA_cast (f : List (List (List ℕ))) (v : ℕ → ℕ) (k : Fin 6) :
    (uA (nth (hdH f) 6) v k : ZMod 24) =
      ((((decode f).A *ᵥ (fun j : Fin Tag.E6.rank => (v j.val : ℤ))) k : ℤ) : ZMod 24) := by
  change (((sumN 6 fun j => aE (nth (hdH f) 6) k j * v j) % 24 : ℕ) : ZMod 24) =
    ((∑ j : Fin 6, ((aX (nth (hdH f) 6) k j : ℤ) - 64) * (v j.val : ℤ) : ℤ) : ZMod 24)
  rw [ZMod.natCast_mod, sumN_six, Fin.sum_univ_six]
  push_cast
  simp only [aE_cast, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  have h3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have h4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  rw [h3, h4, h5]
  push_cast
  ring

theorem allN_of {n : ℕ} {f : ℕ → Bool} (h : ∀ k < n, f k = true) : allN n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Certificates.A3E6K.andB (f n) (allN n f) = true
    exact andB_eq_true.mpr ⟨h n (by omega), ih fun k hk => h k (by omega)⟩

theorem zmod24_dvd {y : ℕ} {x : ℤ} (h : (y : ZMod 24) = ((x : ℤ) : ZMod 24)) :
    (24 : ℤ) ∣ x - y := by
  rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  exact_mod_cast h

theorem tagOK_cases {tw : Bool} {R Z Bp d : ℕ} {h tg : List ℕ} (ht : tagOK tw R Z h Bp d tg = true) :
    tag0 Bp (nth h 6) d tg = true ∨ tag1 tw Bp (nth h 6) d = true ∨
      (tw = true ∧ tag2 R Z h Bp (nth h 6) d tg = true) ∨
      (tw = false ∧ Nat.land d 9 = 0) := by
  unfold tagOK at ht
  generalize Nat.beq (hd tg) 0 = b0 at ht
  generalize Nat.beq (hd tg) 1 = b1 at ht
  generalize Nat.beq (hd tg) 2 = b2 at ht
  cases b0
  · cases b1
    · cases b2
      · obtain ⟨-, h2⟩ := andB_eq_true.mp ht
        obtain ⟨h3, h4⟩ := andB_eq_true.mp h2
        exact Or.inr (Or.inr (Or.inr ⟨notB_eq_true.mp h3, beq_true.mp h4⟩))
      · obtain ⟨h1, h2⟩ := andB_eq_true.mp ht
        exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    · exact Or.inr (Or.inl ht)
  · exact Or.inl ht

theorem land9 {sw : Bool} {e₀ e₁ e₂ : ℤ} (he₀ : e₀ = 1 ∨ e₀ = -1) (he₁ : e₁ = 1 ∨ e₁ = -1)
    (he₂ : e₂ = 1 ∨ e₂ = -1) (h : Nat.land (dOf sw e₀ e₁ e₂) 9 = 0) : sw = false ∧ e₂ = 1 := by
  revert h
  cases sw <;> rcases he₀ with rfl | rfl <;> rcases he₁ with rfl | rfl <;>
    rcases he₂ with rfl | rfl <;> decide +kernel

section Tags

variable {R Z : ℕ} {f : List (List (List ℕ))} {z : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
  {sw : Bool} {e₀ e₁ e₂ : ℤ}

theorem tag0_false (hR : rootsOK R e6Certificate.roots = true)
    (hlt : ∀ k < 5, nth (hdH f) k < 72) (hF : FrameFacts (decode f))
    (hfix : Fixes (decode f) z) (him : ColImages (decode f) z sw e₀ e₁ e₂) {tg : List ℕ}
    (h : tag0 (bP R (hdH f)) (nth (hdH f) 6) (dOf sw e₀ e₁ e₂) tg = true) : False := by
  unfold tag0 at h
  simp only [andB_eq_true, Nat.blt_eq, notB_eq_true] at h
  obtain ⟨⟨ha, hb⟩, hy⟩ := h
  let j : Fin Tag.E6.rank := ⟨nth tg 2, hb⟩
  have hw : ∀ k : Fin 6, (aE (nth (hdH f) 6) k (nth tg 2) : ZMod 24) =
      ((((decode f).A *ᵥ Pi.single j 1) k : ℤ) : ZMod 24) := by
    intro k
    rw [aE_cast]
    congr 1
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, j]
    rfl
  have e := yAt_eq hR hlt hF hfix him (Pi.single j 1)
    (fun k => aE (nth (hdH f) 6) k (nth tg 2)) hw ⟨nth tg 1, ha⟩
  have d := zmod24_dvd e
  simp only [Fin.val_mk] at d
  have h8 : yAt (bP R (hdH f)) (dOf sw e₀ e₁ e₂) (fun k => aE (nth (hdH f) 6) k (nth tg 2))
      (nth tg 1) % 8 = 0 := by omega
  have hy' : Nat.beq (yAt (bP R (hdH f)) (dOf sw e₀ e₁ e₂)
      (fun k => aE (nth (hdH f) 6) k (nth tg 2)) (nth tg 1) % 8) 0 = false := hy
  rw [h8] at hy'
  exact absurd hy' (by decide)

theorem rr_vals : (fun j : Fin Tag.E6.rank => ((fld rrP 4 j.val : ℕ) : ℤ)) = rr := by
  funext j
  fin_cases j <;> decide +kernel

theorem tag1_false (hR : rootsOK R e6Certificate.roots = true)
    (hlt : ∀ k < 5, nth (hdH f) k < 72) (hF : FrameFacts (decode f))
    (hfix : Fixes (decode f) z) (him : ColImages (decode f) z sw e₀ e₁ e₂) {tw : Bool}
    (hrr : ∀ i : Fin 6, ∀ y : ℕ, y < 24 → (24 : ℤ) ∣ 8 * (z *ᵥ rr) i - y → y = fld (rrT tw) 5 i)
    (h : tag1 tw (bP R (hdH f)) (nth (hdH f) 6) (dOf sw e₀ e₁ e₂) = true) : False := by
  unfold tag1 at h
  rw [notB_eq_true] at h
  have hall : allN 6 (fun i => Nat.beq (yAt (bP R (hdH f)) (dOf sw e₀ e₁ e₂)
      (uA (nth (hdH f) 6) fun j => fld rrP 4 j) i) (fld (rrT tw) 5 i)) = true := by
    refine allN_of fun i hi => beq_true.mpr ?_
    have hw : ∀ k : Fin 6, (uA (nth (hdH f) 6) (fun j => fld rrP 4 j) k : ZMod 24) =
        ((((decode f).A *ᵥ rr) k : ℤ) : ZMod 24) := by
      intro k
      rw [uA_cast, rr_vals]
    have e := yAt_eq hR hlt hF hfix him rr _ hw ⟨i, hi⟩
    exact hrr ⟨i, hi⟩ _ (yAt_lt _ _ _ _) (zmod24_dvd e)
  rw [hall] at h
  exact absurd h (by decide)

theorem notB_andB {a b : Bool} : Certificates.A3E6K.notB (Certificates.A3E6K.andB a b) = true ↔ ¬(a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

theorem pair_congr {x y : E6V} (h : ∀ i, (x i : ZMod 3) = (y i : ZMod 3))
    (c : Fin Tag.E6.rank → ZMod 3) : ggLiePair x c = ggLiePair y c := by
  unfold ggLiePair
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem colc0 (R : ℕ) (h : List ℕ) : colc R h 0 = rc R (nth h 0) := rfl
theorem colc1 (R : ℕ) (h : List ℕ) : colc R h 1 = rc R (nth h 1) := rfl
theorem colc2 (R : ℕ) (h : List ℕ) : colc R h 2 = rc R (nth h 2) := rfl

theorem tag2_sound {N P t : ℕ}
    (hR : rootsOK R e6Certificate.roots = true)
    (hM : ∀ i < 72, masksAt R Z N i = true) (hs : structOK R Z N P (hdH f) t = true)
    (hF : FrameFacts (decode f))
    (hfix : Fixes (decode f) z) (him : ColImages (decode f) z sw e₀ e₁ e₂) {tg : List ℕ}
    (h : tag2 R Z (hdH f) (bP R (hdH f)) (nth (hdH f) 6) (dOf sw e₀ e₁ e₂) tg = true) :
    ∃ g : E6V, IsRoot Tag.E6 g ∧ ¬(iform g (decode f).b₀ = 0 ∧ iform g (decode f).b₁ = 0) ∧
      (iform (decode f).p g ≠ 0 ∨ iform (decode f).q g ≠ 0 ∨ iform (decode f).r g ≠ 0) ∧
      ∀ c : Fin Tag.E6.rank → ZMod 3, (∀ γ, ggLiePair (z *ᵥ γ) c = -ggLiePair γ c) →
        ggLiePair (decode f).p c = 0 → ggLiePair (decode f).q c = 0 →
        ggLiePair (decode f).r c = 0 → ggLiePair g c = 0 := by
  obtain ⟨hlt, -⟩ := structOK_parts hs
  unfold tag2 at h
  simp only [notB_andB, andB_eq_true, Nat.blt_eq] at h
  obtain ⟨hg, hnb, hnp, hall⟩ := h
  have mZ : ∀ {i k : ℕ}, i < 72 → k < 72 → (rel Z i k = true ↔ iform (rt i) (rt k) = 0) :=
    fun hi hk => (masks_sound hR hM hi hk).1
  have mZ' : ∀ {i k : ℕ}, i < 72 → k < 72 → (rel Z i k = true ↔ iform (rt k) (rt i) = 0) :=
    fun hi hk => by rw [mZ hi hk, iform_comm]
  refine ⟨rt (nth tg 10), isRoot_rt hg, ?_, ?_, ?_⟩
  · rw [decode_b₀, decode_b₁, ← mZ' (hlt 3 (by norm_num)) hg, ← mZ' (hlt 4 (by norm_num)) hg]
    exact hnb
  · rw [decode_p, decode_q, decode_r]
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hnp ⟨(mZ (hlt 0 (by norm_num)) hg).mpr hc.1, (mZ (hlt 1 (by norm_num)) hg).mpr hc.2.1,
      (mZ (hlt 2 (by norm_num)) hg).mpr hc.2.2⟩
  · intro c hz hpc hqc hrc
    let L : E6V := fun j => ((nth tg (1 + j.val) : ℕ) : ℤ)
    have hw : ∀ k : Fin 6, (uA (nth (hdH f) 6) (fun j => nth tg (1 + j)) k : ZMod 24) =
        ((((decode f).A *ᵥ L) k : ℤ) : ZMod 24) := fun k => uA_cast f _ k
    have key : ∀ i : Fin Tag.E6.rank, ((rt (nth tg 10) i : ℤ) : ZMod 3) =
        (((z *ᵥ L) + L + ((nth tg 7 : ℕ) : ℤ) • (decode f).p + ((nth tg 8 : ℕ) : ℤ) • (decode f).q +
          ((nth tg 9 : ℕ) : ℤ) • (decode f).r) i : ZMod 3) := by
      intro i
      have e := zmod24_dvd (yAt_eq hR hlt hF hfix him L _ hw i)
      have hY := yAt_lt (bP R (hdH f)) (dOf sw e₀ e₁ e₂)
        (uA (nth (hdH f) 6) fun j => nth tg (1 + j)) i.val
      have ha := beq_true.mp (allN_sound hall i.val i.isLt)
      simp only [nadd, nmul, ndiv, nmod] at ha
      set y := yAt (bP R (hdH f)) (dOf sw e₀ e₁ e₂)
        (uA (nth (hdH f) 6) fun j => nth tg (1 + j)) i.val with hy
      have Ay : ((y / 8 : ℕ) : ZMod 3) = (((z *ᵥ L) i : ℤ) : ZMod 3) := by
        rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
        omega
      have A2 := (ZMod.natCast_eq_natCast_iff' _ _ 3).mpr ha
      rw [cd_fld_bP (by norm_num) i.isLt, cd_fld_bP (by norm_num) i.isLt,
        cd_fld_bP (by norm_num) i.isLt, colc0, colc1, colc2] at A2
      have hp : (decode f).p i = (cd (rc R (nth (hdH f) 0)) i : ℤ) - 8 := by
        rw [decode_p, ← roots_sound hR (hlt 0 (by norm_num)), dv']
      have hq : (decode f).q i = (cd (rc R (nth (hdH f) 1)) i : ℤ) - 8 := by
        rw [decode_q, ← roots_sound hR (hlt 1 (by norm_num)), dv']
      have hr : (decode f).r i = (cd (rc R (nth (hdH f) 2)) i : ℤ) - 8 := by
        rw [decode_r, ← roots_sound hR (hlt 2 (by norm_num)), dv']
      have hgi : rt (nth tg 10) i = (cd (rc R (nth tg 10)) i : ℤ) - 8 := by
        rw [← roots_sound hR hg, dv']
      have h9 : (9 : ZMod 3) = 0 := by decide
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp, hq, hr, hgi, L]
      push_cast at A2 ⊢
      rw [← Ay]
      linear_combination -A2 + ((nth tg 7 : ZMod 3) + (nth tg 8 : ZMod 3) + (nth tg 9 : ZMod 3) - 1) * h9
    rw [pair_congr key c, pair_add, pair_add, pair_add, pair_add, pair_zsmul, pair_zsmul, pair_zsmul,
      hz L, hpc, hqc, hrc, mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero]
    exact neg_add_cancel _

theorem rr_tw (i : Fin 6) (x : ℤ) (y : ℕ) (hy : y < 24) (h3 : (3 : ℤ) ∣ x + rr i)
    (hd : (24 : ℤ) ∣ 8 * x - y) : y = fld (rrT true) 5 i := by
  have hr : rr i = ([4, 3, 5, 6, 4, 2] : List ℤ).getD i.val 0 := by fin_cases i <;> rfl
  have ht : fld (rrT true) 5 i.val = ([16, 0, 8, 0, 16, 8] : List ℕ).getD i.val 0 := by
    fin_cases i <;> decide +kernel
  rw [hr] at h3
  rw [ht]
  obtain ⟨n, hn⟩ := i
  simp only at h3 ⊢
  interval_cases n <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h3 ⊢ <;> omega

theorem rr_un (i : Fin 6) (x : ℤ) (y : ℕ) (hy : y < 24) (h3 : (3 : ℤ) ∣ x - rr i)
    (hd : (24 : ℤ) ∣ 8 * x - y) : y = fld (rrT false) 5 i := by
  have hr : rr i = ([4, 3, 5, 6, 4, 2] : List ℤ).getD i.val 0 := by fin_cases i <;> rfl
  have ht : fld (rrT false) 5 i.val = ([8, 0, 16, 0, 8, 16] : List ℕ).getD i.val 0 := by
    fin_cases i <;> decide +kernel
  rw [hr] at h3
  rw [ht]
  obtain ⟨n, hn⟩ := i
  simp only at h3 ⊢
  interval_cases n <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h3 ⊢ <;> omega

end Tags

theorem mem_framesOf {R Z N P : ℕ} {Ls : List (List (List (List (List ℕ))))}
    (hS : ∀ c < Ls.length, framesStruct R Z N P (Ls.getD c []) (27 * c) (27 * c + 27) = true)
    {F : Frame} (hF : F ∈ framesOf Ls) :
    ∃ c < Ls.length, ∃ f ∈ Ls.getD c [], F = decode f ∧ ∃ t, structOK R Z N P (hdH f) t = true := by
  obtain ⟨f, hf, rfl⟩ := hF
  obtain ⟨L, hL, hfL⟩ := List.mem_flatten.mp hf
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hfL
  have hg : Ls.getD c [] = Ls[c] := by simp [hc]
  have h := (framesStruct_sound (hS c hc)).2 r (by rw [hg]; exact hr)
  simp only [hg] at h
  exact ⟨c, hc, Ls[c][r], by rw [hg]; exact List.getElem_mem hr, rfl, _, h⟩

theorem tw_sound {R Z N P : ℕ} {Ls : List (List (List (List (List ℕ))))}
    (hR : rootsOK R e6Certificate.roots = true) (hM : ∀ i < 72, masksAt R Z N i = true)
    (hS : ∀ c < Ls.length, framesStruct R Z N P (Ls.getD c []) (27 * c) (27 * c + 27) = true)
    (hT : ∀ c < Ls.length, framesTags true R Z (Ls.getD c []) = true) :
    ∀ F ∈ framesOf Ls, TwFacts F := by
  intro F hFm
  obtain ⟨c, hc, f, hf, rfl, t, hs⟩ := mem_framesOf hS hFm
  have hF := frame_facts hR hM hs
  obtain ⟨hlt, -⟩ := structOK_parts hs
  have ht := framesTags_sound (hT c hc) f hf
  simp only [if_true] at ht
  intro z sw e₀ e₁ e₂ hfix him hrr
  have htg := tagsOK_parts ht _ (dOf_lt sw e₀ e₁ e₂)
  rcases tagOK_cases htg with h0 | h1 | ⟨-, h2⟩ | ⟨h3, -⟩
  · exact (tag0_false hR hlt hF hfix him h0).elim
  · exact (tag1_false hR hlt hF hfix him (fun i y hy hd => rr_tw i _ y hy (hrr i) hd) h1).elim
  · exact tag2_sound hR hM hs hF hfix him h2
  · exact absurd h3 (by decide)

theorem un_sound {R Z N P : ℕ} {Ls : List (List (List (List (List ℕ))))}
    (hR : rootsOK R e6Certificate.roots = true) (hM : ∀ i < 72, masksAt R Z N i = true)
    (hS : ∀ c < Ls.length, framesStruct R Z N P (Ls.getD c []) (27 * c) (27 * c + 27) = true)
    (hU : ∀ c < Ls.length, framesTags false R Z (Ls.getD c []) = true) :
    ∀ F ∈ framesOf Ls, UnFacts F := by
  intro F hFm
  obtain ⟨c, hc, f, hf, rfl, t, hs⟩ := mem_framesOf hS hFm
  have hF := frame_facts hR hM hs
  obtain ⟨hlt, -⟩ := structOK_parts hs
  have ht := framesTags_sound (hU c hc) f hf
  simp only [Bool.false_eq_true, if_false] at ht
  intro z sw e₀ e₁ e₂ hfix him hrr
  have htg := tagsOK_parts ht _ (dOf_lt sw e₀ e₁ e₂)
  rcases tagOK_cases htg with h0 | h1 | ⟨h2, -⟩ | ⟨-, h3⟩
  · exact (tag0_false hR hlt hF hfix him h0).elim
  · exact (tag1_false hR hlt hF hfix him (fun i y hy hd => rr_un i _ y hy (hrr i) hd) h1).elim
  · exact absurd h2 (by decide)
  · exact land9 him.1 him.2.1 him.2.2.1 h3

end CFSG.KC.A3E6

end
