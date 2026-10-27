module

public import Certificates.Data.Kernel.Co2Span.Check
public import CFSG.Certificates.Kernel.Co2Syl.Sound
public import CFSG.Certificates.Kernel.Co2Smith.RowsSound
public import CFSG.GF2Type.Widths1112.Co2Module.EnumInputs

public section

namespace CFSG.KC.Co2Span

set_option exponentiation.threshold 600

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.KC.Co2Syl CFSG.KC.TabMatGrp
  CFSG.Sporadic.SmallF2.Native CFSG.GF2Type.Widths1112.Co2Module CFSG.GF2W1112 Matrix
open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_apply toVecD_apply ofBits_testBit ofBits_lt)

theorem allN_iff {f : Nat → Bool} : ∀ {n : Nat}, allN f n = true ↔ ∀ i < n, f i = true
  | 0 => by simp [allN]
  | n + 1 => by
    rw [allN, Bool.and_eq_true, allN_iff]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem MatP_apply22 (U : Nat) (i j : Fin 22) :
    MatP 22 U i j = if U.testBit (22 * i.val + j.val) then 1 else 0 := by
  rw [MatP_apply, Nat.mul_comm]

theorem MatP_mod (A : Nat) : MatP 22 (A % 2 ^ 484) = MatP 22 A := by
  unfold MatP
  rw [unpack_mod]

theorem eqK_iff {A B : Nat} : eqK A B = true ↔ MatP 22 A = MatP 22 B := by
  constructor
  · intro h
    unfold MatP
    rw [eq_unpack_of_eqK h]
  · intro h
    rw [← MatP_mod A, ← MatP_mod B] at h
    have := MatP_inj h (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    rw [eqK, cK_eq, cK_eq, this, Nat.beq_refl]

theorem MatP_powK (A : Nat) : ∀ e : Nat, MatP 22 (powK A e) = MatP 22 A ^ e
  | 0 => by rw [pow_zero, ← MatP_IDP]; rfl
  | e + 1 => by
    have : powK A (e + 1) = mulV (powK A e) A := rfl
    rw [this, MatP_mulV, MatP_powK A e, pow_succ]

theorem MatP_xor (A B : Nat) : MatP 22 (A ^^^ B) = MatP 22 A + MatP 22 B := by
  ext i j
  rw [Matrix.add_apply, MatP_apply22, MatP_apply22, MatP_apply22, Nat.testBit_xor]
  cases A.testBit (22 * i.val + j.val) <;> cases B.testBit (22 * i.val + j.val) <;> decide

theorem MatP_zero : MatP 22 0 = 0 := by
  ext i j
  rw [MatP_apply22]
  simp

theorem rowsAgree_sound {R : Array Nat} {P : Nat} (h : rowsAgree R P = true) :
    rowsMatrix 22 R = MatP 22 P := by
  ext i j
  rw [rowsMatrix_apply, toVecD_apply, MatP_apply22]
  have h1 := (allN_iff.1 ((allN_iff.1 h) i.val i.isLt)) j.val j.isLt
  rw [beq_iff_eq] at h1
  rw [h1]

private theorem fld_ofBits {f : Nat → Bool} {i v : Nat} (hi : i < 10) (hv : v < 16)
    (hf : ∀ k < 4, f (4 * i + k) = v.testBit k) : (ofBits 40 f >>> (4 * i)) % 16 = v := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [show (16 : Nat) = 2 ^ 4 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hk : k < 4
  · rw [ofBits_testBit, hf k hk]
    simp [hk, show 4 * i + k < 40 by omega]
  · have h16 : (16 : Nat) ≤ 2 ^ k :=
      le_trans (by norm_num : (16 : Nat) ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have : v.testBit k = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hv h16)
    simp [hk, this]

theorem sgOf_fld (S : Array Nat) (m : Nat) {i : Nat} (hi : i < 10) :
    (sgOf S m >>> (4 * i)) % 16 = S.getD (10 * m + i) 0 % 10 := by
  unfold sgOf
  refine fld_ofBits hi (by omega) fun k hk => ?_
  have h1 : (4 * i + k) / 4 = i := by omega
  have h2 : (4 * i + k) % 4 = k := by omega
  rw [h1, h2]

theorem sgId_fld {i : Nat} (hi : i < 10) : (sgId >>> (4 * i)) % 16 = i := by
  unfold sgId
  refine fld_ofBits hi (by omega) fun k hk => ?_
  have h1 : (4 * i + k) / 4 = i := by omega
  have h2 : (4 * i + k) % 4 = k := by omega
  rw [h1, h2]

theorem cbOf_testBit (U : Array Nat) (m : Nat) {i j c : Nat} (hi : i < 10) (hj : j < 2)
    (hc : c < 2) : (cbOf U m).testBit (4 * i + 2 * j + c) =
      cfNat (U.getD (20 * m + 2 * i + j) 0 / 3 % 3) c := by
  unfold cbOf
  rw [ofBits_testBit]
  have h1 : (4 * i + 2 * j + c) / 4 = i := by omega
  have h2 : (4 * i + 2 * j + c) % 4 / 2 = j := by omega
  have h3 : (4 * i + 2 * j + c) % 2 = c := by omega
  simp [h1, h2, h3, show 4 * i + 2 * j + c < 40 by omega]

theorem cbId_testBit {i j c : Nat} (hi : i < 10) (hj : j < 2) (hc : c < 2) :
    cbId.testBit (4 * i + 2 * j + c) = (j == c) := by
  unfold cbId
  rw [ofBits_testBit]
  have h2 : (4 * i + 2 * j + c) % 4 / 2 = j := by omega
  have h3 : (4 * i + 2 * j + c) % 2 = c := by omega
  simp [h2, h3, show 4 * i + 2 * j + c < 40 by omega]

theorem Xfin_eq_xPack (θ : Matrix (Fin 2) (Fin 2) (ZMod 2)) (σ : Fin 10 → Fin 10)
    (cf : Fin 10 → Fin 2 → Fin 2 → ZMod 2) (t sg cb : Nat)
    (hθ : ∀ a b : Fin 2, θ a b = if t.testBit (2 * a.val + b.val) then 1 else 0)
    (hσ : ∀ i : Fin 10, (sg >>> (4 * i.val)) % 16 = (σ i).val)
    (hcf : ∀ i j c, cf i j c = if cb.testBit (4 * i.val + 2 * j.val + c.val) then 1 else 0) :
    Xfin θ σ cf = MatP 22 (xPack t sg cb) := by
  ext r k
  rw [MatP_apply22, xPack, ofBits_testBit]
  have hlt : 22 * r.val + k.val < 484 := by omega
  have hd : (22 * r.val + k.val) / 22 = r.val := by omega
  have hm : (22 * r.val + k.val) % 22 = k.val := by omega
  simp only [hlt, decide_true, Bool.true_and, xbits, hd, hm]
  unfold Xfin
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  change Xmat θ σ cf (idxDecode r) (idxDecode k) = _
  unfold idxDecode
  by_cases hr : r.val < 2
  · by_cases hk : k.val < 2
    · simp only [hr, hk, ↓reduceDIte, ↓reduceIte, decide_true, Bool.true_and, Xmat, Matrix.of_apply]
      rw [hθ]
    · simp only [hr, hk, ↓reduceDIte, ↓reduceIte, decide_false, Bool.false_and, Xmat,
        Matrix.of_apply]
      rfl
  · by_cases hk : k.val < 2
    · simp only [hr, hk, ↓reduceDIte, ↓reduceIte, Xmat, Matrix.of_apply]
      have : ¬ 2 ≤ k.val := by omega
      simp [this]
    · have hk2 : 2 ≤ k.val := by omega
      simp only [hr, hk, ↓reduceDIte, ↓reduceIte, Xmat, Matrix.of_apply, hk2, decide_true,
        Bool.true_and]
      have hi : (k.val - 2) / 2 < 10 := by omega
      rw [hσ ⟨(k.val - 2) / 2, hi⟩, hcf]
      simp only []
      by_cases he : ((r.val - 2) / 2 : Nat) = (σ ⟨(k.val - 2) / 2, hi⟩).val
      · have he' : (⟨(r.val - 2) / 2, by omega⟩ : Fin 10) = σ ⟨(k.val - 2) / 2, hi⟩ := Fin.ext he
        rw [if_pos he', he]
        simp
      · have he' : (⟨(r.val - 2) / 2, by omega⟩ : Fin 10) ≠ σ ⟨(k.val - 2) / 2, hi⟩ :=
          fun h => he (congrArg Fin.val h)
        rw [if_neg he']
        have : ((σ ⟨(k.val - 2) / 2, hi⟩).val == (r.val - 2) / 2) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun h => he h.symm
        simp [this]

theorem thetaCode_apply (t : Nat) (a b : Fin 2) :
    thetaCode t a b = if t.testBit (2 * a.val + b.val) then 1 else 0 := by
  unfold thetaCode
  rw [Matrix.of_apply, Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (t >>> (2 * a.val + b.val)) with h | h <;> simp [h]

private theorem uW1_dot (n : Nat) : uW1 ⬝ᵥ uVec n = ((n / 3 % 3 : Nat) : ZMod 3) := by
  have h : uW1 = ![0, 1, 0, 0] := by decide
  rw [h]
  simp [dotProduct, Fin.sum_univ_four, uVec]

private theorem coef_nat : ∀ v : Fin 3, ∀ c : Fin 2,
    coef ((v.val : Nat) : ZMod 3) c = if cfNat v.val c.val then 1 else 0 := by
  decide

theorem cfTab_eq (k : Fin 8) (i : Fin 10) (j c : Fin 2) :
    cfTab uW1 uV0 (uU k) i j c =
      if (cbOf w12UDecU k.val).testBit (4 * i.val + 2 * j.val + c.val) then 1 else 0 := by
  have h0 : uW1 ⬝ᵥ uV0 = 1 := by
    unfold uV0
    rw [uW1_dot]
    decide
  unfold cfTab uU
  rw [uW1_dot, h0, inv_one, mul_one, cbOf_testBit _ _ i.isLt j.isLt c.isLt]
  have hv : w12UDecU.getD (k.val * 20 + i.val * 2 + j.val) 0 / 3 % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have e : 20 * k.val + 2 * i.val + j.val = k.val * 20 + i.val * 2 + j.val := by ring
  rw [e]
  exact coef_nat ⟨_, hv⟩ c

theorem uSigma_fld (k : Fin 8) (i : Fin 10) :
    (sgOf w12UDecSigma k.val >>> (4 * i.val)) % 16 = (uSigma k i).val := by
  rw [sgOf_fld _ _ i.isLt]
  unfold uSigma
  simp only []
  rw [show 10 * k.val + i.val = k.val * 10 + i.val by ring]

theorem uXOf_eq (t : Nat) (k : Fin 8) :
    uXOf (thetaCode t) k = MatP 22 (xPack t (sgOf w12UDecSigma k.val) (cbOf w12UDecU k.val)) :=
  Xfin_eq_xPack _ _ _ _ _ _ (thetaCode_apply t) (uSigma_fld k) (cfTab_eq k)

theorem one_eq_thetaCode : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) = thetaCode 9 := by
  decide

theorem uXOf_one_eq (k : Fin 8) :
    uXOf 1 k = MatP 22 (xPack 9 (sgOf w12UDecSigma k.val) (cbOf w12UDecU k.val)) := by
  rw [one_eq_thetaCode, uXOf_eq]

private theorem Qmat_eq (S : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    Qmat S = Xmat S id (fun _ j c => if j = c then 1 else 0) := by
  ext r k
  rcases r with a' | ⟨i', c⟩ <;> rcases k with a | ⟨i, j⟩
  · rfl
  · rfl
  · rfl
  · simp only [Qmat, Xmat, Matrix.of_apply, id, Prod.mk.injEq]
    by_cases h1 : i' = i <;> by_cases h2 : c = j <;> simp [h1, h2, eq_comm]

theorem Qfin_eq (s : Nat) : Qfin (thetaCode s) = MatP 22 (xPack s sgId cbId) := by
  have : Qfin (thetaCode s) = Xfin (thetaCode s) id (fun _ j c => if j = c then 1 else 0) := by
    unfold Qfin Xfin
    rw [Qmat_eq]
  rw [this]
  refine Xfin_eq_xPack _ _ _ _ _ _ (thetaCode_apply s) (fun i => sgId_fld i.isLt) fun i j c => ?_
  rw [cbId_testBit i.isLt j.isLt c.isLt]
  by_cases h : j = c
  · simp [h]
  · have : (j.val == c.val) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun e => h (Fin.ext e)
    simp [h, this]

end CFSG.KC.Co2Span
