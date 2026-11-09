module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.F2NatMat

@[expose] def ent (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem ent_true : ent true = 1 := rfl
@[simp] theorem ent_false : ent false = 0 := rfl

theorem ent_xor (a b : Bool) : ent (a ^^ b) = ent a + ent b := by
  cases a <;> cases b <;> decide

theorem ent_and (a b : Bool) : ent (a && b) = ent a * ent b := by
  cases a <;> cases b <;> decide

theorem ent_inj {a b : Bool} : ent a = ent b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem ent_eq_zero {a : Bool} : ent a = 0 ↔ a = false := by
  cases a <;> decide

theorem ent_eq_one {a : Bool} : ent a = 1 ↔ a = true := by
  cases a <;> decide

theorem ent_decide_eq_one (x : ZMod 2) : ent (decide (x = 1)) = x := by
  revert x; decide

@[expose] def bitK (c k : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight c k) 1) 1

theorem bitK_eq (c k : ℕ) : bitK c k = c.testBit k := by
  have e : Nat.land (Nat.shiftRight c k) 1 = (c >>> k) % 2 := Nat.and_one_is_mod _
  rw [bitK, e, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (c >>> k) with h | h <;> rw [h] <;> rfl

@[expose] def bx (a b : Bool) : Bool := cond a (!b) b

theorem bx_eq (a b : Bool) : bx a b = (a ^^ b) := by cases a <;> cases b <;> rfl

@[expose] def xorSum (g : ℕ → Bool) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => bx acc (g k)) m

theorem ent_xorSum (g : ℕ → Bool) (m : ℕ) :
    ent (xorSum g m) = ∑ k ∈ Finset.range m, ent (g k) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    change ent (bx (xorSum g m) (g m)) = _
    rw [bx_eq]
    exact ent_xor _ _

theorem xorSum_false (g : ℕ → Bool) (h : ∀ k, g k = false) (m : ℕ) : xorSum g m = false := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change bx (xorSum g m) (g m) = false
    rw [ih, h]; rfl

@[expose] def build (f : ℕ → Bool) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun p acc => Nat.lor acc (cond (f p) (Nat.pow 2 p) 0)) m

theorem testBit_build (f : ℕ → Bool) (m p : ℕ) :
    (build f m).testBit p = (decide (p < m) && f p) := by
  induction m with
  | zero => simp [build]
  | succ m ih =>
    change (build f m ||| (bif f m then 2 ^ m else 0)).testBit p = _
    rw [Nat.testBit_or, ih]
    rcases Nat.lt_trichotomy p m with h | rfl | h
    · cases f m <;> simp [h, Nat.ne_of_gt h, Nat.lt_succ_of_lt h]
    · cases f p <;> simp
    · cases f m <;> simp [Nat.ne_of_lt h, Nat.not_lt_of_gt h] <;> omega

theorem build_lt (f : ℕ → Bool) (m : ℕ) : build f m < 2 ^ m :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_build]; simp; omega

@[expose] def allBelow (m : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && f k) m

theorem allBelow_spec {m : ℕ} {f : ℕ → Bool} (h : allBelow m f = true) : ∀ k < m, f k = true := by
  induction m with
  | zero => intro k hk; omega
  | succ m ih =>
    change (allBelow m f && f m) = true at h
    rw [Bool.and_eq_true] at h
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h.1 k hk
    · exact h.2

theorem allBelow_iff {m : ℕ} {f : ℕ → Bool} : allBelow m f = true ↔ ∀ k < m, f k = true := by
  refine ⟨allBelow_spec, fun h => ?_⟩
  induction m with
  | zero => rfl
  | succ m ih =>
    change (allBelow m f && f m) = true
    rw [Bool.and_eq_true]
    exact ⟨ih fun k hk => h k (by omega), h m (by omega)⟩

@[expose] def anyBelow (m : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => acc || f k) m

theorem anyBelow_iff {m : ℕ} {f : ℕ → Bool} : anyBelow m f = true ↔ ∃ k < m, f k = true := by
  induction m with
  | zero => simp [anyBelow]
  | succ m ih =>
    change (anyBelow m f || f m) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inl ⟨k, hk, h⟩
      · exact Or.inr h

@[expose] def orAcc (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc (f k)) m

theorem testBit_orAcc (f : ℕ → ℕ) (m t : ℕ) :
    (orAcc f m).testBit t = anyBelow m (fun k => (f k).testBit t) := by
  induction m with
  | zero => simp [orAcc, anyBelow]
  | succ m ih =>
    change (orAcc f m ||| f m).testBit t = (anyBelow m (fun k => (f k).testBit t) || (f m).testBit t)
    rw [Nat.testBit_or, ih]

@[expose] def dec (n c : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => ent (c.testBit (n * i + j))

theorem dec_apply (n c : ℕ) (i j : Fin n) : dec n c i j = ent (c.testBit (n * i + j)) := rfl

theorem idx_lt {n i j : ℕ} (hi : i < n) (hj : j < n) : n * i + j < n * n := by
  have : n * i + n ≤ n * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left n hi
  omega

theorem idx_div {n i j : ℕ} (hj : j < n) : (n * i + j) / n = i := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

theorem idx_mod {n i j : ℕ} (hj : j < n) : (n * i + j) % n = j := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem idx_eq {n p : ℕ} : n * (p / n) + p % n = p := Nat.div_add_mod p n

theorem idx_div_lt {n p : ℕ} (hp : p < n * n) : p / n < n :=
  Nat.div_lt_of_lt_mul hp

theorem idx_mod_lt {n p : ℕ} (hp : p < n * n) : p % n < n :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by subst h; simp at hp)

theorem exists_dec (n : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    ∃ c, c < 2 ^ (n * n) ∧ dec n c = M := by
  let f : ℕ → Bool := fun p =>
    if h : p / n < n ∧ p % n < n then decide (M ⟨p / n, h.1⟩ ⟨p % n, h.2⟩ = 1) else false
  refine ⟨build f (n * n), build_lt _ _, ?_⟩
  ext i j
  rw [dec_apply, testBit_build, decide_eq_true (idx_lt i.2 j.2), Bool.true_and]
  have h1 := idx_div (i := i.1) j.2
  have h2 := idx_mod (i := i.1) j.2
  have hh : (n * i + j) / n < n ∧ (n * i + j) % n < n := by rw [h1, h2]; exact ⟨i.2, j.2⟩
  simp only [f, hh, and_self, ↓reduceDIte]
  have e : (⟨(n * i + j) / n, hh.1⟩ : Fin n) = i := Fin.ext h1
  have e' : (⟨(n * i + j) % n, hh.2⟩ : Fin n) = j := Fin.ext h2
  rw [e, e', ent_decide_eq_one]

theorem dec_eq_dec_iff {n a b : ℕ} : dec n a = dec n b ↔ a % 2 ^ (n * n) = b % 2 ^ (n * n) := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hp : p < n * n
    · have hi := idx_div_lt hp
      have hj := idx_mod_lt hp
      have := congrFun (congrFun h ⟨p / n, hi⟩) ⟨p % n, hj⟩
      simp only [dec_apply, idx_eq] at this
      rw [ent_inj.1 this]
    · simp [hp]
  · intro h
    ext i j
    rw [dec_apply, dec_apply]
    have hl := idx_lt i.2 j.2
    have ha := Nat.testBit_mod_two_pow a (n * n) (n * i + j)
    have hb := Nat.testBit_mod_two_pow b (n * n) (n * i + j)
    rw [h, decide_eq_true hl, Bool.true_and] at ha
    rw [decide_eq_true hl, Bool.true_and] at hb
    rw [← ha, hb]

@[expose] def eqK (n a b : ℕ) : Bool :=
  Nat.beq (Nat.mod a (Nat.pow 2 (Nat.mul n n))) (Nat.mod b (Nat.pow 2 (Nat.mul n n)))

theorem decide_dec_eq (n a b : ℕ) : decide (dec n a = dec n b) = eqK n a b := by
  change _ = (a % 2 ^ (n * n) == b % 2 ^ (n * n))
  by_cases h : a % 2 ^ (n * n) = b % 2 ^ (n * n)
  · rw [decide_eq_true (dec_eq_dec_iff.2 h), h, beq_self_eq_true]
  · rw [decide_eq_false (fun e => h (dec_eq_dec_iff.1 e))]
    exact (beq_eq_false_iff_ne.2 h).symm

theorem dec_eq_iff_eqK {n a b : ℕ} : dec n a = dec n b ↔ eqK n a b = true := by
  rw [← decide_dec_eq, decide_eq_true_iff]

@[expose] def rowOf (n c i : ℕ) : ℕ := Nat.mod (Nat.shiftRight c (Nat.mul n i)) (Nat.pow 2 n)

theorem testBit_rowOf (n c i j : ℕ) :
    (rowOf n c i).testBit j = (decide (j < n) && c.testBit (n * i + j)) := by
  change ((c >>> (n * i)) % 2 ^ n).testBit j = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

@[expose] def rowMul (n r b m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => Nat.xor acc (cond (bitK r k) (rowOf n b k) 0)) m

theorem testBit_rowMul (n r b m j : ℕ) :
    (rowMul n r b m).testBit j = xorSum (fun k => r.testBit k && (rowOf n b k).testBit j) m := by
  induction m with
  | zero => simp [rowMul, xorSum]
  | succ m ih =>
    change (rowMul n r b m ^^^ (bif bitK r m then rowOf n b m else 0)).testBit j =
      bx (xorSum (fun k => r.testBit k && (rowOf n b k).testBit j) m)
        (r.testBit m && (rowOf n b m).testBit j)
    rw [Nat.testBit_xor, ih, bitK_eq, bx_eq]
    cases r.testBit m <;> simp

theorem testBit_rowMul_ge {n r b m j : ℕ} (hj : n ≤ j) : (rowMul n r b m).testBit j = false := by
  rw [testBit_rowMul]
  apply xorSum_false
  intro k
  rw [testBit_rowOf, decide_eq_false (by omega)]
  simp

@[expose] def mulAux (n a b m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (rowMul n (rowOf n a i) b n) (Nat.mul n i))) m

@[expose] def mulK (n a b : ℕ) : ℕ := mulAux n a b n

theorem testBit_mulAux {n a b i j : ℕ} (hj : j < n) (m : ℕ) :
    (mulAux n a b m).testBit (n * i + j) =
      (decide (i < m) && (rowMul n (rowOf n a i) b n).testBit j) := by
  induction m with
  | zero => simp [mulAux]
  | succ m ih =>
    change (mulAux n a b m ||| (rowMul n (rowOf n a m) b n <<< (n * m))).testBit (n * i + j) = _
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy i m with h | rfl | h
    · have : n * i + n ≤ n * m := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left n h
      simp [h, Nat.lt_succ_of_lt h]
      omega
    · simp
    · have : n * m + n ≤ n * i := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left n h
      have h2 : ¬ i < m := Nat.not_lt_of_gt h
      have h3 : ¬ i < m + 1 := by omega
      simp only [h2, h3, decide_false, Bool.false_and, Bool.false_or]
      rw [testBit_rowMul_ge (by omega), Bool.and_false]

theorem dec_mulK (n a b : ℕ) : dec n (mulK n a b) = dec n a * dec n b := by
  ext i j
  rw [dec_apply, mulK, testBit_mulAux j.2, decide_eq_true i.2, Bool.true_and, testBit_rowMul,
    ent_xorSum, Matrix.mul_apply]
  simp only [dec_apply]
  rw [← Finset.sum_range (fun k => ent (a.testBit (n * i + k)) *
      ent (b.testBit (n * k + j)))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < n := Finset.mem_range.1 hk
  rw [testBit_rowOf, testBit_rowOf, decide_eq_true hk', decide_eq_true j.2, Bool.true_and,
    Bool.true_and, ent_and]

@[expose] def oneK (n : ℕ) : ℕ := build (fun p => Nat.beq (p / n) (p % n)) (n * n)

theorem dec_oneK (n : ℕ) : dec n (oneK n) = 1 := by
  ext i j
  rw [dec_apply, oneK, testBit_build, decide_eq_true (idx_lt i.2 j.2), Bool.true_and,
    idx_div j.2, idx_mod j.2, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    have hb : Nat.beq i j = false := Bool.eq_false_iff.2 fun e => this (Nat.eq_of_beq_eq_true e)
    simp [h, hb]

theorem oneK_five : oneK 5 = 17043521 := by decide +kernel

theorem dec_17043521 : dec 5 17043521 = 1 := by rw [← oneK_five, dec_oneK]

@[expose] def transK (n a : ℕ) : ℕ := build (fun p => bitK a (n * (p % n) + p / n)) (n * n)

theorem dec_transK (n a : ℕ) : dec n (transK n a) = (dec n a).transpose := by
  ext i j
  rw [dec_apply, transK, testBit_build, decide_eq_true (idx_lt i.2 j.2), Bool.true_and,
    idx_div j.2, idx_mod j.2, Matrix.transpose_apply, dec_apply, bitK_eq]

@[expose] def powK (n a k : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (oneK n)
  (fun _ acc => mulK n acc a) k

theorem dec_powK (n a k : ℕ) : dec n (powK n a k) = dec n a ^ k := by
  induction k with
  | zero => exact dec_oneK n
  | succ k ih =>
    change dec n (mulK n (powK n a k) a) = _
    rw [dec_mulK, ih, pow_succ]

@[expose] def vdec (n c : ℕ) : Fin n → ZMod 2 := fun j => ent (c.testBit j)

@[expose] def packK (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: L => r ||| (packK n L <<< n)

theorem testBit_packK {n j : ℕ} (hj : j < n) :
    ∀ (L : List ℕ), (∀ r ∈ L, r < 2 ^ n) → ∀ i,
      (packK n L).testBit (n * i + j) = (L.getD i 0).testBit j
  | [], _, i => by simp [packK]
  | r :: L, hL, i => by
    have hr : r < 2 ^ n := hL r List.mem_cons_self
    rw [packK, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases i with _ | i
    · simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      simp [show ¬ j ≥ n by omega]
    · have h1 : n * (i + 1) + j ≥ n := by rw [Nat.mul_succ]; omega
      have h2 : n * (i + 1) + j - n = n * i + j := by rw [Nat.mul_succ]; omega
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) h1)),
        decide_eq_true h1, h2, testBit_packK hj L (fun r' h' => hL r' (List.mem_cons_of_mem _ h')) i]
      simp

theorem of_vdec_eq_dec {n : ℕ} (L : List ℕ) (hL : ∀ r ∈ L, r < 2 ^ n)
    (v : Fin n → Fin n → ZMod 2) (hv : ∀ i, v i = vdec n (L.getD i 0)) :
    Matrix.of v = dec n (packK n L) := by
  ext i j
  rw [Matrix.of_apply, hv, dec_apply, testBit_packK j.2 L hL]
  rfl

theorem vdec_xor (n a b : ℕ) : vdec n (a ^^^ b) = vdec n a + vdec n b := by
  funext j
  simp only [vdec, Pi.add_apply, Nat.testBit_xor, ent_xor]

@[expose] def mvK (n c v : ℕ) : ℕ := build (fun r => xorSum (fun k => bitK (rowOf n c r) k && bitK v k) n) n

theorem vdec_mvK (n c v : ℕ) : vdec n (mvK n c v) = (dec n c).mulVec (vdec n v) := by
  funext r
  simp only [vdec, mvK, testBit_build, decide_eq_true r.2, Bool.true_and, ent_xorSum,
    Matrix.mulVec, dotProduct, dec_apply]
  rw [← Finset.sum_range (fun k => ent (c.testBit (n * r + k)) * ent (v.testBit k))]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [ent_and, bitK_eq, bitK_eq, testBit_rowOf, decide_eq_true (Finset.mem_range.1 hk),
    Bool.true_and]

theorem mvK_lt (n c v : ℕ) : mvK n c v < 2 ^ n := build_lt _ _

@[expose] def dotK (n a b : ℕ) : Bool := xorSum (fun k => bitK a k && bitK b k) n

theorem dotProduct_vdec (n a b : ℕ) : vdec n a ⬝ᵥ vdec n b = ent (dotK n a b) := by
  rw [dotK, ent_xorSum, dotProduct]
  simp only [vdec]
  rw [← Finset.sum_range (fun k => ent (a.testBit k) * ent (b.testBit k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ent_and, bitK_eq, bitK_eq]

@[expose] def det3K (a : ℕ) : Bool :=
  bx (bx (bitK a 0 && bx (bitK a 4 && bitK a 8) (bitK a 5 && bitK a 7))
    (bitK a 1 && bx (bitK a 3 && bitK a 8) (bitK a 5 && bitK a 6)))
    (bitK a 2 && bx (bitK a 3 && bitK a 7) (bitK a 4 && bitK a 6))

theorem zmod2_neg (x : ZMod 2) : -x = x := by revert x; decide

theorem det_dec3 (a : ℕ) : (dec 3 a).det = ent (det3K a) := by
  rw [Matrix.det_fin_three]
  simp only [dec_apply, det3K, bx_eq, bitK_eq, ent_xor, ent_and, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  simp only [sub_eq_add_neg, zmod2_neg]
  ring

end CFSG.F2NatMat
