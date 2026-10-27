
module

public import Certificates.Data.Kernel.Q9SL2
public import CFSG.GH74.GLS.Stage4.Q9.ModelBaseBase

public section

namespace CFSG.KC.Q9SL2

open CFSG.GH74.GLS.Stage4.Q9 CFSG.GH74.GLS.Stage4.Q9.DFacts

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9

@[expose] def f9c (x : F9) : ℕ := x.re.val * 3 + x.im.val

@[expose] def enc (M : SL2) : ℕ :=
  729 * f9c ((M : 𝕄) 0 0) + 81 * f9c ((M : 𝕄) 0 1) + 9 * f9c ((M : 𝕄) 1 0) + f9c ((M : 𝕄) 1 1)

theorem f9c_lt (x : F9) : f9c x < 9 := by
  have h1 := ZMod.val_lt x.re
  have h2 := ZMod.val_lt x.im
  unfold f9c
  omega

theorem f9c_inj : ∀ x y : F9, f9c x = f9c y → x = y := by decide +kernel

theorem f9c_mul : ∀ x y : F9, f9c (x * y) = mul9 (f9c x) (f9c y) := by decide +kernel

theorem f9c_neg : ∀ x : F9, f9c (-x) = neg9 (f9c x) := by decide +kernel

theorem f9c_beq_zero : ∀ x : F9, (x == 0) = (f9c x == 0) := by decide +kernel

theorem f9c_nu : f9c nu = 4 := by decide +kernel

theorem f9c_nu_inv : f9c nu⁻¹ = 7 := by decide +kernel

theorem enc_d0 (M : SL2) : enc M / 729 = f9c ((M : 𝕄) 0 0) := by
  have := f9c_lt ((M : 𝕄) 0 0); have := f9c_lt ((M : 𝕄) 0 1)
  have := f9c_lt ((M : 𝕄) 1 0); have := f9c_lt ((M : 𝕄) 1 1)
  unfold enc; omega

theorem enc_d1 (M : SL2) : enc M / 81 % 9 = f9c ((M : 𝕄) 0 1) := by
  have := f9c_lt ((M : 𝕄) 0 0); have := f9c_lt ((M : 𝕄) 0 1)
  have := f9c_lt ((M : 𝕄) 1 0); have := f9c_lt ((M : 𝕄) 1 1)
  unfold enc; omega

theorem enc_d2 (M : SL2) : enc M / 9 % 9 = f9c ((M : 𝕄) 1 0) := by
  have := f9c_lt ((M : 𝕄) 0 0); have := f9c_lt ((M : 𝕄) 0 1)
  have := f9c_lt ((M : 𝕄) 1 0); have := f9c_lt ((M : 𝕄) 1 1)
  unfold enc; omega

theorem enc_d3 (M : SL2) : enc M % 9 = f9c ((M : 𝕄) 1 1) := by
  have := f9c_lt ((M : 𝕄) 0 0); have := f9c_lt ((M : 𝕄) 0 1)
  have := f9c_lt ((M : 𝕄) 1 0); have := f9c_lt ((M : 𝕄) 1 1)
  unfold enc; omega

theorem enc_inj {M N : SL2} (h : enc M = enc N) : M = N := by
  have e00 := f9c_inj _ _ (by rw [← enc_d0, ← enc_d0, h] : f9c ((M : 𝕄) 0 0) = f9c ((N : 𝕄) 0 0))
  have e01 := f9c_inj _ _ (by rw [← enc_d1, ← enc_d1, h] : f9c ((M : 𝕄) 0 1) = f9c ((N : 𝕄) 0 1))
  have e10 := f9c_inj _ _ (by rw [← enc_d2, ← enc_d2, h] : f9c ((M : 𝕄) 1 0) = f9c ((N : 𝕄) 1 0))
  have e11 := f9c_inj _ _ (by rw [← enc_d3, ← enc_d3, h] : f9c ((M : 𝕄) 1 1) = f9c ((N : 𝕄) 1 1))
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

theorem beq_enc (A B : SL2) : (A == B) = (enc A == enc B) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨congrArg enc, enc_inj⟩

theorem enc_r0 (M : SL2) : enc M / 81 = 9 * f9c ((M : 𝕄) 0 0) + f9c ((M : 𝕄) 0 1) := by
  have := f9c_lt ((M : 𝕄) 0 0); have := f9c_lt ((M : 𝕄) 0 1)
  have := f9c_lt ((M : 𝕄) 1 0); have := f9c_lt ((M : 𝕄) 1 1)
  unfold enc; omega

theorem enc_r1 (M : SL2) : enc M % 81 = 9 * f9c ((M : 𝕄) 1 0) + f9c ((M : 𝕄) 1 1) := by
  have := f9c_lt ((M : 𝕄) 0 0); have := f9c_lt ((M : 𝕄) 0 1)
  have := f9c_lt ((M : 𝕄) 1 0); have := f9c_lt ((M : 𝕄) 1 1)
  unfold enc; omega

theorem lkD_f9 : ∀ a b e g : F9,
    lkD (81 * (9 * f9c a + f9c b) + (9 * f9c e + f9c g)) = f9c (a * e + b * g) := by
  decide +kernel

theorem enc_mul (M N : SL2) : enc (M * N) = mulK (enc M) (enc N) := by
  have hc : ((M * N : SL2) : 𝕄) = (M : 𝕄) * (N : 𝕄) := Matrix.SpecialLinearGroup.coe_mul M N
  simp only [mulK]
  rw [enc_r0 M, enc_r1 M, enc_d0 N, enc_d1 N, enc_d2 N, enc_d3 N]
  simp only [lkD_f9, enc, hc, Matrix.mul_apply, Fin.sum_univ_two]

theorem enc_one : enc 1 = 2190 := by decide +kernel

theorem enc_minusOne : enc minusOne = 4380 := by decide +kernel

theorem enc_sigma (M : SL2) : enc (sigmaAut M) = sigK (enc M) := by
  have h : ((sigmaAut M : SL2) : 𝕄) =
      !![(M : 𝕄) 1 1, nu * (M : 𝕄) 1 0; nu⁻¹ * (M : 𝕄) 0 1, (M : 𝕄) 0 0] := rfl
  simp only [sigK]
  rw [enc_d0 M, enc_d1 M, enc_d2 M, enc_d3 M]
  simp [enc, h, f9c_mul, f9c_nu, f9c_nu_inv]

theorem enc_inv (M : SL2) : enc (invSL M) = invK (enc M) := by
  have h : ((invSL M : SL2) : 𝕄) = !![(M : 𝕄) 1 1, -(M : 𝕄) 0 1; -(M : 𝕄) 1 0, (M : 𝕄) 0 0] := rfl
  simp only [invK]
  rw [enc_d0 M, enc_d1 M, enc_d2 M, enc_d3 M]
  simp [enc, h, f9c_neg]

theorem inQ16b_eq : inQ16b = fun M => q16K (enc M) := by
  funext M
  simp only [inQ16b, q16K, f9c_beq_zero, enc_d0, enc_d1, enc_d2, enc_d3]

theorem ordLAux_innerL (M : SL2) : ∀ (k : ℕ) (P : SL2) (n : ℕ),
    ordLAux (innerL M) k (innerL P) n = ordAuxK (enc M) k (enc P) n := by
  intro k
  induction k with
  | zero => intro P n; rfl
  | succ k ih =>
    intro P n
    have hP : innerL P = 1 ↔ enc P = 2190 := by
      rw [← enc_one]
      constructor
      · intro h
        rw [← map_one innerL] at h
        exact congrArg enc (innerL_injective h)
      · intro h
        rw [enc_inj h, map_one]
    simp only [ordLAux, ordAuxK]
    rw [← map_mul, normL_eq, ih, enc_mul]
    by_cases h : enc P = 2190
    · rw [if_pos (hP.mpr h), if_pos h]
    · rw [if_neg (mt hP.mp h), if_neg h]

theorem ordL_innerL (M : SL2) : ordL (innerL M) = ordK (enc M) := by
  simp only [ordL, ordK, normL_eq, ordLAux_innerL]

theorem sl2_map : sl2List.map enc = codes := by
  have h : (sl2List.map enc == codes) = true := by decide +kernel
  exact eq_of_beq h

theorem sl2_nodup : sl2List.Nodup := by
  have hc : List.IsChain (· < ·) codes := by decide +kernel
  have h : codes.Nodup := (List.isChain_iff_pairwise.mp hc).imp fun h => Nat.ne_of_lt h
  rw [← sl2_map] at h
  exact h.of_map enc

theorem card_filter (p : SL2 → Bool) :
    (sl2List.filter p).toFinset.card = (sl2List.filter p).length :=
  List.toFinset_card_of_nodup (sl2_nodup.filter p)

theorem chkSqOne_eq : chkSqOne = chkSqOneK := by
  simp only [chkSqOne, chkSqOneK, ← sl2_map, List.all_map, Function.comp_def, beq_enc, enc_mul,
    enc_one, enc_minusOne]

theorem chkCenter_eq : chkCenter = chkCenterK := by
  simp only [chkCenter, chkCenterK, ← sl2_map, List.all_map, Function.comp_def, beq_enc, enc_mul,
    enc_one, enc_minusOne]

theorem chkQ8_eq : chkQ8 = chkQ8K := by
  simp only [chkQ8, chkQ8K, ← sl2_map, List.all_map, List.any_map, Function.comp_def, beq_enc,
    enc_mul, enc_one, enc_minusOne]

theorem chkConjFixed5_eq : chkConjFixed5 = chkConjFixed5K := by
  simp only [chkConjFixed5, chkConjFixed5K, ← sl2_map, List.all_map, List.any_map,
    Function.comp_def, beq_enc, enc_mul, enc_sigma, enc_inv, ordL_innerL]

theorem chkCent5_eq : chkCent5 = chkCent5K := by
  simp only [chkCent5, chkCent5K, cent, centK, card_filter, ← sl2_map, List.all_map,
    List.filter_map, List.length_map, Function.comp_def, beq_enc, enc_mul, ordL_innerL]

theorem chkCent3_eq : chkCent3 = chkCent3K := by
  simp only [chkCent3, chkCent3K, cent, centK, card_filter, ← sl2_map, List.all_map,
    List.filter_map, List.length_map, Function.comp_def, beq_enc, enc_mul, ordL_innerL]

theorem chkCentOdd5_eq : chkCentOdd5 = chkCentOdd5K := by
  simp only [chkCentOdd5, chkCentOdd5K, cent, centK, ← sl2_map, List.all_map, List.filter_map,
    Function.comp_def, beq_enc, enc_mul, enc_one, ordL_innerL]

theorem chkCentOdd3_eq : chkCentOdd3 = chkCentOdd3K := by
  simp only [chkCentOdd3, chkCentOdd3K, cent, centK, ← sl2_map, List.all_map, List.filter_map,
    Function.comp_def, beq_enc, enc_mul, ordL_innerL]

theorem chkSigmaNotConj_eq : chkSigmaNotConj = chkSigmaNotConjK := by
  simp only [chkSigmaNotConj, chkSigmaNotConjK, ← sl2_map, List.all_map, Function.comp_def, bne,
    beq_enc, enc_mul, enc_sigma, ordL_innerL]

theorem chkInvert3_eq : chkInvert3 = chkInvert3K := by
  simp only [chkInvert3, chkInvert3K, ← sl2_map, List.all_map, List.any_map, Function.comp_def,
    beq_enc, enc_mul, enc_inv, enc_minusOne, ordL_innerL]

theorem chkNo16_eq : chkNo16 = chkNo16K := by
  simp only [chkNo16, chkNo16K, ← sl2_map, List.all_map, Function.comp_def, bne, ordL_innerL]

theorem chkQ16_eq : chkQ16 = chkQ16K := by
  simp only [chkQ16, chkQ16K, ← sl2_map, List.all_map, Function.comp_def, inQ16b_eq, beq_enc,
    enc_mul, enc_one, enc_minusOne]

theorem chkQ16card_eq : chkQ16card = chkQ16cardK := by
  simp only [chkQ16card, chkQ16cardK, card_filter, ← sl2_map, List.filter_map, List.length_map,
    Function.comp_def, inQ16b_eq]

end CFSG.KC.Q9SL2
