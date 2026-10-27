module

public import Certificates.Data.Kernel.Q9SL.Enc
import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBase
import CFSG.GH74.GLS.Stage4.Q9.TablesInputs

public section

namespace CFSG.KC.Q9SL

open CFSG.GH74.GLS.Stage4.Q9 CFSG.GH74.GLS.Stage4.Q9.Tables

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9

theorem eF_lt (a : F9) : eF a < 9 := by
  have h1 := ZMod.val_lt a.re
  have h2 := ZMod.val_lt a.im
  change 3 * a.re.val + a.im.val < 9
  omega

theorem eF_inj : ∀ a b : F9, eF a = eF b → a = b := by decide +kernel

theorem eF_add : ∀ a b : F9, eF (a + b) = addF (eF a) (eF b) := by decide +kernel

theorem eF_sub : ∀ a b : F9, eF (a - b) = subF (eF a) (eF b) := by decide +kernel

theorem eF_neg : ∀ a : F9, eF (-a) = negF (eF a) := by decide +kernel

theorem eF_mul : ∀ a b : F9, eF (a * b) = mulF (eF a) (eF b) := by decide +kernel

theorem eF_nu : eF nu = 4 := by decide +kernel

theorem eF_nu_inv : eF nu⁻¹ = 7 := by decide +kernel

theorem fl_eq (x i : Nat) : fl x i = x / 2 ^ i % 16 := by
  change (x >>> i) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem pk_eq (a b c d : Nat) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    pk a b c d = a * 4096 + (b * 256 + (c * 16 + d)) := by
  have h1 : c <<< 4 ||| d = c * 16 + d := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.lt_of_lt_of_le hd (by norm_num) : d < 2 ^ 4),
      Nat.shiftLeft_eq]
  have h2 : b <<< 8 ||| (c * 16 + d) = b * 256 + (c * 16 + d) := by
    have hl : c * 16 + d < 2 ^ 8 := by
      norm_num
      omega
    rw [← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq]
  have h3 : a <<< 12 ||| (b * 256 + (c * 16 + d)) = a * 4096 + (b * 256 + (c * 16 + d)) := by
    have hl : b * 256 + (c * 16 + d) < 2 ^ 12 := by
      norm_num
      omega
    rw [← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq]
  change a <<< 12 ||| (b <<< 8 ||| (c <<< 4 ||| d)) = _
  rw [h1, h2, h3]

theorem lanes_pk (a b c d : Nat) (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    m00 (pk a b c d) = a ∧ m01 (pk a b c d) = b ∧ m10 (pk a b c d) = c ∧ m11 (pk a b c d) = d := by
  simp only [m00, m01, m10, m11, fl_eq, pk_eq a b c d hb hc hd, Nat.reducePow]
  omega

theorem lanes_enc (M : SL2) :
    m00 (enc M) = eF ((M : 𝕄) 0 0) ∧ m01 (enc M) = eF ((M : 𝕄) 0 1) ∧
      m10 (enc M) = eF ((M : 𝕄) 1 0) ∧ m11 (enc M) = eF ((M : 𝕄) 1 1) :=
  lanes_pk _ _ _ _ (by have := eF_lt ((M : 𝕄) 0 0); omega) (by have := eF_lt ((M : 𝕄) 0 1); omega)
    (by have := eF_lt ((M : 𝕄) 1 0); omega) (by have := eF_lt ((M : 𝕄) 1 1); omega)

theorem m00_enc (M : SL2) : m00 (enc M) = eF ((M : 𝕄) 0 0) := (lanes_enc M).1

theorem m01_enc (M : SL2) : m01 (enc M) = eF ((M : 𝕄) 0 1) := (lanes_enc M).2.1

theorem m10_enc (M : SL2) : m10 (enc M) = eF ((M : 𝕄) 1 0) := (lanes_enc M).2.2.1

theorem m11_enc (M : SL2) : m11 (enc M) = eF ((M : 𝕄) 1 1) := (lanes_enc M).2.2.2

theorem enc_inj {M N : SL2} (h : enc M = enc N) : M = N := by
  have e00 := eF_inj _ _ (by rw [← m00_enc, ← m00_enc, h] : eF ((M : 𝕄) 0 0) = eF ((N : 𝕄) 0 0))
  have e01 := eF_inj _ _ (by rw [← m01_enc, ← m01_enc, h] : eF ((M : 𝕄) 0 1) = eF ((N : 𝕄) 0 1))
  have e10 := eF_inj _ _ (by rw [← m10_enc, ← m10_enc, h] : eF ((M : 𝕄) 1 0) = eF ((N : 𝕄) 1 0))
  have e11 := eF_inj _ _ (by rw [← m11_enc, ← m11_enc, h] : eF ((M : 𝕄) 1 1) = eF ((N : 𝕄) 1 1))
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

theorem enc_of (a b c d : F9) (h : Matrix.det !![a, b; c, d] = 1) :
    enc ⟨!![a, b; c, d], h⟩ = pk (eF a) (eF b) (eF c) (eF d) := rfl

theorem enc_mul (M N : SL2) : enc (M * N) = mulS (enc M) (enc N) := by
  rw [mulS, m00_enc, m01_enc, m10_enc, m11_enc, m00_enc, m01_enc, m10_enc, m11_enc]
  simp only [enc, mulE, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    eF_add, eF_mul]

theorem enc_conjSL (c M : SL2) : enc (conjSL c M) = conjS (enc c) (enc M) := by
  rw [conjS, m00_enc, m01_enc, m10_enc, m11_enc, m00_enc, m01_enc, m10_enc, m11_enc]
  simp only [conjSL, enc_of, conjE, eF_add, eF_sub, eF_mul]

theorem enc_mul_minusOne (M : SL2) : enc (M * minusOne) = negS (enc M) := by
  rw [negS, m00_enc, m01_enc, m10_enc, m11_enc]
  simp only [enc, Matrix.SpecialLinearGroup.coe_mul, minusOne_val, mul_neg, mul_one,
    Matrix.neg_apply, eF_neg]

theorem enc_sigma (M : SL2) : enc (sigmaAut M) = sigS (enc M) := by
  have h : sigmaAut M = sigmaFun M := rfl
  rw [h, sigS, m00_enc, m01_enc, m10_enc, m11_enc]
  simp only [sigmaFun, enc_of, eF_mul, eF_nu, eF_nu_inv]

theorem enc_invSL (M : SL2) : enc (invSL M) = invS (enc M) := by
  rw [invS, m00_enc, m01_enc, m10_enc, m11_enc]
  simp only [invSL, enc_of, eF_neg]

theorem enc_one : enc 1 = oneS := by decide +kernel

theorem enc_minusOne : enc minusOne = moneS := by decide +kernel

theorem enc_eq_oneS {M : SL2} : enc M = oneS ↔ M = 1 :=
  ⟨fun h => enc_inj (h.trans enc_one.symm), fun h => h ▸ enc_one⟩

theorem enc_eq_moneS {M : SL2} : enc M = moneS ↔ M = minusOne :=
  ⟨fun h => enc_inj (h.trans enc_minusOne.symm), fun h => h ▸ enc_minusOne⟩

theorem trS_enc (M : SL2) : trS (enc M) = eF (trSL2 M) := by
  rw [trS, m00_enc, m11_enc, trSL2, eF_add]

theorem repIdx_val (M : SL2) : (repIdx M).val = repS (enc M) := by
  rw [repS, trS_enc, m01_enc, m10_enc]
  unfold repIdx
  generalize trSL2 M = t
  generalize (M : 𝕄) 0 1 = b
  generalize (M : 𝕄) 1 0 = c
  revert t b c
  decide +kernel

theorem classSwap_val : ∀ j : Fin 7, (classSwap j).val = swapC j.val := by decide +kernel

theorem orderFn_eq : ∀ (j : Fin 7) (t : F9), orderFn j t = ordFE j.val (eF t) := by decide +kernel

theorem ordAux_succ (x k p n : Nat) :
    ordAux x (k + 1) p n =
      Bool.rec (motive := fun _ => Nat) (ordAux x k (mulS p x) (n + 1)) n (Nat.beq p oneS) := rfl

theorem ordLAux_innerL (M : SL2) : ∀ (k : Nat) (P : SL2) (n : Nat),
    ordLAux (innerL M) k (innerL P) n = ordAux (enc M) k (enc P) n := by
  intro k
  induction k with
  | zero => intro P n; rfl
  | succ k ih =>
    intro P n
    have hP : innerL P = 1 ↔ enc P = oneS := by
      rw [enc_eq_oneS, map_eq_one_iff innerL innerL_injective]
    rw [ordAux_succ]
    simp only [ordLAux]
    cases hb : Nat.beq (enc P) oneS
    · have hne : ¬ innerL P = 1 := fun h => by
        rw [hP.mp h, Nat.beq_refl] at hb
        exact Bool.noConfusion hb
      rw [if_neg hne, ← map_mul, normL_eq, ih, enc_mul]
    · rw [if_pos (hP.mpr (Nat.eq_of_beq_eq_true hb))]

theorem ordL_innerL (M : SL2) : ordL (innerL M) = ordS (enc M) := by
  rw [ordL, normL_eq, ordLAux_innerL]
  rfl

theorem brec_and (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem brec_or (a b : Bool) : Bool.rec (motive := fun _ => Bool) b true a = (a || b) := by
  cases a <;> rfl

theorem allL_nil (f : Nat → Bool) : allL [] f = true := rfl

theorem allL_cons (x : Nat) (L : List Nat) (f : Nat → Bool) :
    allL (x :: L) f = (f x && allL L f) := brec_and _ _

theorem allL_spec (L : List Nat) (f : Nat → Bool) : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allL_nil]
  | cons x L ih => simp [allL_cons, ih]

theorem cntL_eq (L : List Nat) (f : Nat → Bool) : cntL L f = (L.filter f).length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Bool.rec (motive := fun _ => Nat) (cntL L f) (Nat.succ (cntL L f)) (f x) = _
    rw [List.filter_cons]
    cases f x <;> simp [ih]

theorem allI_cons (x : Nat) (L : List Nat) (f : Nat → Nat → Bool) (i : Nat) :
    allI (x :: L) f i = (f i x && allI L f (i + 1)) := brec_and _ _

theorem allI_spec (L : List Nat) (f : Nat → Nat → Bool) : ∀ s : Nat,
    allI L f s = true ↔ ∀ (i : Nat) (h : i < L.length), f (s + i) L[i] = true := by
  induction L with
  | nil => intro s; simp only [List.length_nil, Nat.not_lt_zero]; exact ⟨fun _ _ h => h.elim, fun _ => rfl⟩
  | cons x L ih =>
    intro s
    rw [allI_cons, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have h := h1 i (by simp only [List.length_cons] at hi; omega)
        have e : s + 1 + i = s + (i + 1) := by omega
        rw [e] at h
        simpa using h
    · intro h
      have h0 := h 0 (by simp)
      rw [List.getElem_cons_zero, Nat.add_zero] at h0
      refine ⟨h0, fun i hi => ?_⟩
      have h' := h (i + 1) (by simp only [List.length_cons]; omega)
      have e : s + (i + 1) = s + 1 + i := by omega
      rw [e] at h'
      simpa using h'

theorem incL_cons (x : Nat) (L : List Nat) (p : Nat) :
    incL (x :: L) p = (Nat.blt p x && incL L x) := brec_and _ _

theorem incL_spec (L : List Nat) : ∀ p : Nat, incL L p = true →
    L.Pairwise (· < ·) ∧ ∀ y ∈ L, p < y := by
  induction L with
  | nil => intro p _; simp
  | cons x L ih =>
    intro p h
    rw [incL_cons, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hpx, h⟩ := h
    obtain ⟨hs, hb⟩ := ih x h
    refine ⟨List.pairwise_cons.2 ⟨hb, hs⟩, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hpx
    · exact Nat.lt_trans hpx (hb y hy)

theorem all2_exists (f : Nat → Nat → Bool) (L : List Nat) : ∀ W : List Nat, all2 L f W = true →
    ∀ x ∈ L, ∃ w, f x w = true := by
  induction L with
  | nil => intro W _ x hx; simp at hx
  | cons x L ih =>
    intro W h y hy
    cases W with
    | nil => exact absurd (h : false = true) Bool.false_ne_true
    | cons w W =>
      have h' : Bool.rec (motive := fun _ => Bool) false (all2 L f W) (f x w) = true := h
      rw [brec_and, Bool.and_eq_true] at h'
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨w, h'.1⟩
      · exact ih W h'.2 y hy

theorem ckSort_spec {L : List Nat} (h : ckSort L = true) :
    L.length = 720 ∧ L.Pairwise (· < ·) := by
  have h' : (incL L 0 && Nat.beq (cntL L fun _ => true) 720) = true := (brec_and _ _).symm.trans h
  rw [Bool.and_eq_true, Nat.beq_eq, cntL_eq, List.filter_true] at h'
  exact ⟨h'.2, (incL_spec L 0 h'.1).1⟩

theorem ln_of_ckLP {L : List Nat} {LP : Nat} (h : ckLP L LP = true) :
    ∀ (i : Nat) (hi : i < L.length), ln LP i = L[i] := by
  intro i hi
  have h' := (allI_spec L _ 0).1 h i hi
  rw [Nat.zero_add, Nat.beq_eq] at h'
  exact h'

theorem ckRep_spec {R : List Nat} {RP : Nat} (h : ckRep R RP = true) :
    ∀ j < 7, repS (ln RP j) = j := by
  intro j hj
  have h' := (brec_and _ _).symm.trans h
  rw [Bool.and_eq_true, Nat.beq_eq, cntL_eq, List.filter_true] at h'
  have h2 := (allI_spec R _ 0).1 h'.1 j (by omega)
  simp only [Nat.zero_add, brec_and, Bool.and_eq_true, Nat.beq_eq] at h2
  rw [h2.2]
  exact h2.1

end CFSG.KC.Q9SL
