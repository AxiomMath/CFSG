module

public import Certificates.Data.Kernel.Misc.O73
public import CFSG.LieType.Multipliers.O73DataInputs
import CFSG.Certificates.Kernel.Spor.PK.Enc
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KS.PK

open CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.LieType.Multipliers.O73 Matrix

@[expose] def idxOf (a : Nat) : Idx :=
  if h : a < 3 then .inl ⟨a, h⟩ else if h' : a < 6 then .inr (.inl ⟨a - 3, by omega⟩) else .inr (.inr ())

@[expose] noncomputable def mEnc (A : Matrix Idx Idx (ZMod 3)) : Nat :=
  ofFnM fun a b => (A (idxOf a) (idxOf b)).val

@[expose] def gram : Matrix Idx Idx (ZMod 3) :=
  Matrix.of fun a b => match a, b with
    | .inl i, .inr (.inl j) => if i = j then 1 else 0
    | .inr (.inl i), .inl j => if i = j then 1 else 0
    | .inr (.inr _), .inr (.inr _) => 2
    | _, _ => 0

theorem idx_idxOf {a : Nat} (ha : a < 7) : idx (idxOf a) = a := by
  unfold idxOf
  by_cases h : a < 3
  · simp [h, idx]
  · by_cases h' : a < 6
    · simp [h, h', idx]
      omega
    · simp [h, h', idx]
      omega

theorem idxOf_idx (i : Idx) : idxOf (idx i) = i := by
  revert i
  decide

private theorem idx_lt (i : Idx) : idx i < 7 := by
  revert i
  decide

private theorem g_lt (f : Nat → Nat → Nat) (i : Nat) : f (i / 7) (i % 7) % 3 < 2 ^ 4 := by
  have := Nat.mod_lt (f (i / 7) (i % 7)) (show 3 > 0 by omega)
  have h16 : (2 : Nat) ^ 4 = 16 := by norm_num
  omega

private theorem ofFnM_inner (f : Nat → Nat → Nat) (a acc : Nat)
    (hacc : acc = enc 4 (fun t => f (t / 7) (t % 7) % 3) (7 * a)) (b : Nat) (hb : b ≤ 7) :
    Nat.rec (motive := fun _ => Nat) acc (fun b acc2 => Nat.lor acc2 (Nat.shiftLeft
      (Nat.mod (f a b) 3) (Nat.mul 4 (Nat.add (Nat.mul 7 a) b)))) b
      = enc 4 (fun t => f (t / 7) (t % 7) % 3) (7 * a + b) := by
  induction b with
  | zero => exact hacc
  | succ b ih =>
    have ih := ih (by omega)
    have h1 : enc 4 (fun t => f (t / 7) (t % 7) % 3) (7 * a + b) < 2 ^ (4 * (7 * a + b)) :=
      enc_lt (fun i _ => g_lt f i)
    have e1 : (7 * a + b) / 7 = a := by omega
    have e2 : (7 * a + b) % 7 = b := by omega
    show Nat.lor (Nat.rec (motive := fun _ => Nat) acc (fun b acc2 => Nat.lor acc2 (Nat.shiftLeft
      (Nat.mod (f a b) 3) (Nat.mul 4 (Nat.add (Nat.mul 7 a) b)))) b)
      (Nat.shiftLeft (Nat.mod (f a b) 3) (Nat.mul 4 (Nat.add (Nat.mul 7 a) b)))
      = enc 4 (fun t => f (t / 7) (t % 7) % 3) (7 * a + (b + 1))
    rw [ih]
    show enc 4 (fun t => f (t / 7) (t % 7) % 3) (7 * a + b) ||| ((f a b % 3) <<< (4 * (7 * a + b)))
      = enc 4 (fun t => f (t / 7) (t % 7) % 3) (7 * a + b + 1)
    rw [lor_shiftLeft_eq_add h1, enc_succ]
    show _ = _ + (f ((7 * a + b) / 7) ((7 * a + b) % 7) % 3) * 2 ^ (4 * (7 * a + b))
    rw [e1, e2]

private theorem ofFnM_outer (f : Nat → Nat → Nat) (a : Nat) (ha : a ≤ 7) :
    Nat.rec (motive := fun _ => Nat) 0 (fun a acc => Nat.rec (motive := fun _ => Nat) acc
      (fun b acc2 => Nat.lor acc2 (Nat.shiftLeft (Nat.mod (f a b) 3)
        (Nat.mul 4 (Nat.add (Nat.mul 7 a) b)))) 7) a
      = enc 4 (fun t => f (t / 7) (t % 7) % 3) (7 * a) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have ih := ih (by omega)
    have h := ofFnM_inner f a _ ih 7 le_rfl
    rw [show 7 * (a + 1) = 7 * a + 7 by omega]
    exact h

private theorem ofFnM_eq (f : Nat → Nat → Nat) :
    ofFnM f = enc 4 (fun t => f (t / 7) (t % 7) % 3) 49 :=
  ofFnM_outer f 7 le_rfl

private theorem ent_eq_fd (M a b : Nat) : ent M a b = fd 4 M (7 * a + b) := by
  unfold ent fd
  show (M >>> (4 * (7 * a + b))) &&& 15 = M / 2 ^ (4 * (7 * a + b)) % 2 ^ 4
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

theorem ent_mEnc (A : Matrix Idx Idx (ZMod 3)) {a b : Nat} (ha : a < 7) (hb : b < 7) :
    ent (mEnc A) a b = (A (idxOf a) (idxOf b)).val := by
  rw [ent_eq_fd]
  unfold mEnc
  rw [ofFnM_eq, fd_enc (w := 4) (f := fun t => (A (idxOf (t / 7)) (idxOf (t % 7))).val % 3)
    (fun i _ => g_lt (fun a b => (A (idxOf a) (idxOf b)).val) i) (by omega)]
  show (A (idxOf ((7 * a + b) / 7)) (idxOf ((7 * a + b) % 7))).val % 3 = _
  rw [show (7 * a + b) / 7 = a by omega, show (7 * a + b) % 7 = b by omega]
  exact Nat.mod_eq_of_lt (ZMod.val_lt _)

theorem mEnc_inj {A B : Matrix Idx Idx (ZMod 3)} (h : mEnc A = mEnc B) : A = B := by
  ext i j
  have e1 := ent_mEnc A (idx_lt i) (idx_lt j)
  have e2 := ent_mEnc B (idx_lt i) (idx_lt j)
  rw [idxOf_idx, idxOf_idx] at e1 e2
  rw [h] at e1
  exact ZMod.val_injective 3 (e1.symm.trans e2)

private theorem ofFnM_congr {f g : Nat → Nat → Nat}
    (h : ∀ a b, a < 7 → b < 7 → f a b % 3 = g a b % 3) : ofFnM f = ofFnM g := by
  rw [ofFnM_eq, ofFnM_eq]
  exact enc_congr (fun i hi => h _ _ (by omega) (by omega))

private theorem mod3_eq_val {n : Nat} {z : ZMod 3} (h : ((n : ℕ) : ZMod 3) = z) :
    n % 3 = z.val := by
  rw [← h, ZMod.val_natCast]

private theorem ofFnM_eq_mEnc {f : Nat → Nat → Nat} {A : Matrix Idx Idx (ZMod 3)}
    (h : ∀ a b, a < 7 → b < 7 → ((f a b : ℕ) : ZMod 3) = A (idxOf a) (idxOf b)) :
    ofFnM f = mEnc A := by
  apply ofFnM_congr
  intro a b ha hb
  show f a b % 3 = (A (idxOf a) (idxOf b)).val % 3
  rw [mod3_eq_val (h a b ha hb), Nat.mod_eq_of_lt (ZMod.val_lt _)]

private theorem idxOf_0 : idxOf 0 = .inl 0 := rfl
private theorem idxOf_1 : idxOf 1 = .inl 1 := rfl
private theorem idxOf_2 : idxOf 2 = .inl 2 := rfl
private theorem idxOf_3 : idxOf 3 = .inr (.inl 0) := rfl
private theorem idxOf_4 : idxOf 4 = .inr (.inl 1) := rfl
private theorem idxOf_5 : idxOf 5 = .inr (.inl 2) := rfl
private theorem idxOf_6 : idxOf 6 = .inr (.inr ()) := rfl

private theorem sum_idx {M : Type*} [AddCommMonoid M] (F : Idx → M) :
    ∑ j, F j = ∑ k ∈ Finset.range 7, F (idxOf k) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_three,
    Fintype.sum_unique]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, idxOf_0, idxOf_1, idxOf_2, idxOf_3,
    idxOf_4, idxOf_5, idxOf_6]
  rw [zero_add]
  abel

private theorem natRec_sum (F : Nat → Nat) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add acc (F k)) n =
      ∑ k ∈ Finset.range n, F k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

theorem mulM7_mEnc (A B : Matrix Idx Idx (ZMod 3)) : mulM7 (mEnc A) (mEnc B) = mEnc (A * B) := by
  unfold mulM7
  rw [letN_eq, letN_eq]
  apply ofFnM_eq_mEnc
  intro a b ha hb
  show ((Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add acc
    (Nat.mul (ent (mEnc A) a k) (ent (mEnc B) k b))) 7 : ℕ) : ZMod 3) = _
  rw [natRec_sum (fun k => Nat.mul (ent (mEnc A) a k) (ent (mEnc B) k b)) 7]
  rw [Matrix.mul_apply, sum_idx, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < 7 := Finset.mem_range.mp hk
  show (((ent (mEnc A) a k * ent (mEnc B) k b : ℕ)) : ZMod 3) = _
  rw [Nat.cast_mul, ent_mEnc A ha hk', ent_mEnc B hk' hb, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

private theorem idxOf_eq_iff {a b : Nat} (ha : a < 7) (hb : b < 7) : idxOf a = idxOf b ↔ a = b :=
  ⟨fun h => by rw [← idx_idxOf ha, ← idx_idxOf hb, h], fun h => by rw [h]⟩

private theorem beq_cast {a b : Nat} (ha : a < 7) (hb : b < 7) :
    ((Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq a b) : ℕ) : ZMod 3) =
      if idxOf a = idxOf b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    have e : Nat.beq a a = true := by simp [Nat.beq_eq]
    rw [e, if_pos rfl]
    exact Nat.cast_one
  · have e : Nat.beq a b = false :=
      Bool.eq_false_iff.mpr (fun h' => h (Nat.eq_of_beq_eq_true h'))
    rw [e, if_neg (fun e => h ((idxOf_eq_iff ha hb).mp e))]
    exact Nat.cast_zero

theorem oneM7_eq : oneM7 = mEnc 1 := by
  unfold oneM7
  apply ofFnM_eq_mEnc
  intro a b ha hb
  rw [Matrix.one_apply]
  exact beq_cast ha hb

theorem trM7_mEnc (A : Matrix Idx Idx (ZMod 3)) : trM7 (mEnc A) = mEnc Aᵀ := by
  unfold trM7
  rw [letN_eq]
  apply ofFnM_eq_mEnc
  intro a b ha hb
  show ((ent (mEnc A) b a : ℕ) : ZMod 3) = _
  rw [ent_mEnc A hb ha, ZMod.natCast_zmod_val]
  rfl

theorem gramM_eq : gramM = mEnc gram := by
  unfold gramM
  apply ofFnM_eq_mEnc
  intro a b ha hb
  interval_cases a <;> interval_cases b <;> decide

private theorem crd_eq (v : List Nat) (k : Nat) : crd v k = v.getD k 0 % 3 := by
  show Nat.mod (wordM7.nthN v k) 3 = _
  rw [nthN_eq]
  rfl

private theorem crdZ (v : List Nat) {a : Nat} (ha : a < 7) :
    ((crd v a : ℕ) : ZMod 3) = vecOf v (idxOf a) := by
  rw [crd_eq, ZMod.natCast_mod]
  simp only [vecOf, idx_idxOf ha]

private theorem idxOf_inl {b : Nat} (h : b < 3) : idxOf b = .inl ⟨b, h⟩ := by
  unfold idxOf; rw [dif_pos h]

private theorem idxOf_inr {b : Nat} (h3 : 3 ≤ b) (h6 : b < 6) :
    idxOf b = .inr (.inl ⟨b - 3, by omega⟩) := by
  unfold idxOf; rw [dif_neg (by omega), dif_pos h6]

private theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]; exact h

private theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.mpr (fun h' => h (by rw [Nat.blt_eq] at h'; exact h'))

private theorem gvK_cast (v : List Nat) {b : Nat} (hb : b < 7) :
    ((gvK v b : ℕ) : ZMod 3) = gv (vecOf v) (idxOf b) := by
  by_cases h3 : b < 3
  · have e : gvK v b = crd v (b + 3) := by
      unfold gvK
      rw [blt_true h3]
    rw [e, crdZ v (by omega), idxOf_inl h3, idxOf_inr (by omega) (by omega)]
    show vecOf v (.inr (.inl ⟨b + 3 - 3, _⟩)) = vecOf v (.inr (.inl ⟨b, h3⟩))
    congr 3
  · by_cases h6 : b < 6
    · have e : gvK v b = crd v (b - 3) := by
        unfold gvK
        rw [blt_false h3, blt_true h6]
        rfl
      rw [e, crdZ v (by omega), idxOf_inr (by omega) h6, idxOf_inl (by omega)]
      rfl
    · have e : gvK v b = 2 * crd v 6 := by
        unfold gvK
        rw [blt_false h3, blt_false h6]
        rfl
      have hb6 : b = 6 := by omega
      subst hb6
      rw [e, Nat.cast_mul, crdZ v (by omega), idxOf_6]
      rfl

theorem rK_eq (v : List Nat) : rK v = mEnc (rMat (vecOf v)) := by
  unfold rK
  apply ofFnM_eq_mEnc
  intro a b ha hb
  show (((Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq a b) : ℕ) + crd v a * gvK v b : ℕ) :
    ZMod 3) = _
  rw [Nat.cast_add, Nat.cast_mul, beq_cast ha hb, crdZ v ha, gvK_cast v hb]
  rfl

theorem tK_eq (v : List Nat) : tK v = mEnc (tMat (vecOf v)) := by
  unfold tK
  rw [letN_eq, rK_eq]
  apply ofFnM_eq_mEnc
  intro a b ha hb
  show ((2 * ent (mEnc (rMat (vecOf v))) a b : ℕ) : ZMod 3) = _
  rw [ent_mEnc _ ha hb, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_ofNat]
  have h2 : ∀ x : ZMod 3, 2 * x = -x := by decide
  rw [h2]
  rfl

theorem q3K_eq (v : List Nat) : q3K v = (q3 (vecOf v)).val := by
  unfold q3K
  show (crd v 0 * crd v 3 + crd v 1 * crd v 4 + (crd v 2 * crd v 5 + crd v 6 * crd v 6)) % 3 = _
  apply mod3_eq_val
  push_cast
  rw [crdZ v (a := 0) (by omega), crdZ v (a := 1) (by omega), crdZ v (a := 2) (by omega),
    crdZ v (a := 3) (by omega), crdZ v (a := 4) (by omega), crdZ v (a := 5) (by omega),
    crdZ v (a := 6) (by omega)]
  simp only [idxOf_0, idxOf_1, idxOf_2, idxOf_3, idxOf_4, idxOf_5, idxOf_6, q3]
  ring

private theorem code_eq_sum (v : Idx → ZMod 3) :
    code v = ∑ a ∈ Finset.range 7, 3 ^ a * (v (idxOf a)).val := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, idxOf_0, idxOf_1, idxOf_2, idxOf_3,
    idxOf_4, idxOf_5, idxOf_6, code]
  ring

private theorem dec_idxOf (x : Nat) {k : Nat} (hk : k < 7) :
    dec x (idxOf k) = ((dig x k : ℕ) : ZMod 3) := by
  simp only [dec, idx_idxOf hk]
  rfl

private theorem mulVec_idxOf (A : Matrix Idx Idx (ZMod 3)) (v : Idx → ZMod 3) (i : Idx) :
    (A *ᵥ v) i = ∑ k ∈ Finset.range 7, A i (idxOf k) * v (idxOf k) := by
  rw [← sum_idx (fun j => A i j * v j)]
  rfl

theorem appM7_mEnc (A : Matrix Idx Idx (ZMod 3)) {x : Nat} (hx : x < 2187) :
    appM7 (mEnc A) x = code (A *ᵥ dec x) := by
  unfold appM7
  rw [natRec_sum, code_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a < 7 := Finset.mem_range.mp ha
  show 3 ^ a * (Nat.rec (motive := fun _ => Nat) 0 (fun k acc2 => Nat.add acc2
    (Nat.mul (ent (mEnc A) a k) (dig x k))) 7 % 3) = _
  rw [natRec_sum (fun k => Nat.mul (ent (mEnc A) a k) (dig x k)) 7]
  congr 1
  apply mod3_eq_val
  rw [mulVec_idxOf, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < 7 := Finset.mem_range.mp hk
  show ((ent (mEnc A) a k * dig x k : ℕ) : ZMod 3) = _
  rw [Nat.cast_mul, ent_mEnc A ha' hk', ZMod.natCast_zmod_val, dec_idxOf x hk']

@[expose] noncomputable def wordMat (Ms : List (Matrix Idx Idx (ZMod 3))) : List Nat →
    Matrix Idx Idx (ZMod 3)
  | [] => 1
  | c :: w => (if c < Ms.length then Ms.getD c 1 else 1) * wordMat Ms w

theorem wordM7_mEnc (Ms : List (Matrix Idx Idx (ZMod 3))) (w : List Nat) :
    wordM7 (Ms.map mEnc) w = mEnc (wordMat Ms w) := by
  induction w with
  | nil => exact oneM7_eq
  | cons c w ih =>
    show mulM7 (Bool.rec (motive := fun _ => Nat) oneM7 (wordM7.nthN (Ms.map mEnc) c)
      (Nat.blt c (lenN (Ms.map mEnc)))) (wordM7 (Ms.map mEnc) w) =
        mEnc ((if c < Ms.length then Ms.getD c 1 else 1) * wordMat Ms w)
    rw [ih, ← mulM7_mEnc]
    congr 1
    by_cases hc : c < Ms.length
    · have h1 : c < (Ms.map mEnc).length := by rw [List.length_map]; exact hc
      rw [if_pos hc, blt_true (by rw [lenN_misc_eq]; exact h1), nthN_eq,
        List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ hc, List.getElem_map]
    · have h1 : ¬ c < (Ms.map mEnc).length := by rw [List.length_map]; exact hc
      rw [if_neg hc, blt_false (by rw [lenN_misc_eq]; exact h1)]
      exact oneM7_eq

private theorem q3_polar (v : Idx → ZMod 3) : 2 * q3 v = v ⬝ᵥ (gram *ᵥ v) := by
  simp [q3, gram, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_three]
  ring

private theorem dot_mulVec_transpose (A : Matrix Idx Idx (ZMod 3)) (v w : Idx → ZMod 3) :
    (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem q3_mulVec {A : Matrix Idx Idx (ZMod 3)} (hA : Aᵀ * gram * A = gram) (v : Idx → ZMod 3) :
    q3 (A *ᵥ v) = q3 v := by
  have key : (A *ᵥ v) ⬝ᵥ (gram *ᵥ (A *ᵥ v)) = v ⬝ᵥ (gram *ᵥ v) := by
    rw [dot_mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
  have h22 : ∀ x : ZMod 3, 2 * (2 * x) = x := by decide
  calc q3 (A *ᵥ v) = 2 * (2 * q3 (A *ᵥ v)) := (h22 _).symm
    _ = 2 * ((A *ᵥ v) ⬝ᵥ (gram *ᵥ (A *ᵥ v))) := by rw [q3_polar]
    _ = 2 * (v ⬝ᵥ (gram *ᵥ v)) := by rw [key]
    _ = 2 * (2 * q3 v) := by rw [q3_polar]
    _ = q3 v := h22 _

theorem code_lt (v : Idx → ZMod 3) : code v < 2187 := by
  have h0 := ZMod.val_lt (v (.inl 0))
  have h1 := ZMod.val_lt (v (.inl 1))
  have h2 := ZMod.val_lt (v (.inl 2))
  have h3 := ZMod.val_lt (v (.inr (.inl 0)))
  have h4 := ZMod.val_lt (v (.inr (.inl 1)))
  have h5 := ZMod.val_lt (v (.inr (.inl 2)))
  have h6 := ZMod.val_lt (v (.inr (.inr ())))
  unfold code
  omega

private theorem code_div_mod (v : Idx → ZMod 3) {a : Nat} (ha : a < 7) :
    code v / 3 ^ a % 3 = (v (idxOf a)).val := by
  have h0 := ZMod.val_lt (v (.inl 0))
  have h1 := ZMod.val_lt (v (.inl 1))
  have h2 := ZMod.val_lt (v (.inl 2))
  have h3 := ZMod.val_lt (v (.inr (.inl 0)))
  have h4 := ZMod.val_lt (v (.inr (.inl 1)))
  have h5 := ZMod.val_lt (v (.inr (.inl 2)))
  have h6 := ZMod.val_lt (v (.inr (.inr ())))
  unfold code
  interval_cases a
  · rw [idxOf_0]; omega
  · rw [idxOf_1]; omega
  · rw [idxOf_2]; omega
  · rw [idxOf_3]; omega
  · rw [idxOf_4]; omega
  · rw [idxOf_5]; omega
  · rw [idxOf_6]; omega

theorem dec_code (v : Idx → ZMod 3) : dec (code v) = v := by
  funext i
  unfold dec
  rw [code_div_mod v (idx_lt i), idxOf_idx, ZMod.natCast_zmod_val]

theorem code_dec {x : Nat} (hx : x < 2187) : code (dec x) = x := by
  rw [code_eq_sum]
  have e : ∀ a < 7, (dec x (idxOf a)).val = x / 3 ^ a % 3 := by
    intro a ha
    unfold dec
    rw [idx_idxOf ha, ZMod.val_natCast, Nat.mod_mod]
  have h : ∑ a ∈ Finset.range 7, 3 ^ a * (dec x (idxOf a)).val =
      ∑ a ∈ Finset.range 7, 3 ^ a * (x / 3 ^ a % 3) :=
    Finset.sum_congr rfl (fun a ha => by rw [e a (Finset.mem_range.mp ha)])
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  omega

end CFSG.KS.PK

end
