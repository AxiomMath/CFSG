module

public import CFSG.CGT.Stroth77.Types120
public import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem int_modEq_of_mul_three_pow (d e : ℕ) {a b : ℤ}
    (h : 3 ^ d * a ≡ 3 ^ d * b [ZMOD 2 ^ e]) : a ≡ b [ZMOD 2 ^ e] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  have hcop : IsCoprime ((2 : ℤ) ^ e) ((3 : ℤ) ^ d) := by
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow_left.pow_right
  rw [← Int.mul_sub] at h
  exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using h)

theorem MatEq.of_three_pow_witness {k : Fin 3 → ℕ} {A B W : IntMat} (d : ℕ)
    (h : ∀ i j, 3 ^ d * (A i j - B i j) = 2 ^ k i * W i j) : MatEq k A B := by
  intro i j
  apply int_modEq_of_mul_three_pow d (k i)
  rw [Int.modEq_iff_dvd]
  refine ⟨-W i j, ?_⟩
  linear_combination (-1 : ℤ) * h i j


namespace Type121

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 1, m + 1]

@[expose] def ρM : IntMat := ofCols ![1, 0, 0] ![0, 0, 1] ![-2, -1, -1]

@[expose] def uvA (i F N : ℤ) : Fin 3 → ℤ := ![2 * F * i, -5 * i, 2 * i + N]

@[expose] def tM (i F G N : ℤ) : IntMat :=
  ofCols ![4 - i, 2, 4] ![4 * G * i, -7 * i + N, -8 * i] (ρM *ᵥ uvA i F N)

@[expose] def uvM (i F G N : ℤ) : IntMat :=
  ofCols ![-i, 2, -2] (uvA i F N) (ρM *ᵥ (tM i F G N *ᵥ uvA i F N))

@[expose] def uM (F : ℤ) : IntMat := uMat ![-1, 0, 0] (-4 * F)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

structure Data (m : ℕ) (i F G N K : ℤ) : Prop where
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hN : N = 2 ^ m
  hK : N = 2 * K
  hG : 3 * G + 7 = N * N


theorem compat_uv {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    Compat (k m) (uvM i F G N) := by
  obtain ⟨hi, hF, -, hK, -⟩ := h
  subst hi
  subst hF
  subst hK
  exact Compat.of_witness (C := !![-8 * G - 19, 128 * G ^ 2 + 592 * G + 684,
      -1536 * G ^ 3 + 256 * G ^ 2 * K - 13184 * G ^ 2 + 1504 * G * K - 36568 * G + 2128 * K - 33060;
    1, -40 * G - 95, -1920 * G ^ 2 + 144 * G * K + 4 * K ^ 2 - 9088 * G + 342 * K - 10754;
    -1, 16 * G + 2 * K + 38, 192 * G ^ 2 + 928 * G + 1121]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, uvM, tM, uvA, ρM, uMat, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)

theorem compat_t {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    Compat (k m) (tM i F G N) := by
  obtain ⟨hi, hF, -, hK, -⟩ := h
  subst hi
  subst hF
  subst hK
  exact Compat.of_witness (C := !![-8 * G - 15, 64 * G ^ 2 + 152 * G, 128 * G ^ 2 + 528 * G - 8 * K + 532;
    1, -56 * G + 2 * K - 133, -16 * G - 2 * K - 38;
    2, -64 * G - 152, -56 * G - 2 * K - 133]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, tM, uvA, ρM, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)

theorem compat_u {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    Compat (k m) (uM F) := by
  obtain ⟨hi, hF, -, hK, -⟩ := h
  subst hi
  subst hF
  exact Compat.of_witness (C := !![-1, -32 * G - 72, -32 * G - 72;
    0, 0, 1;
    0, 1, 0]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, uM, uMat, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)

theorem compat_rho {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    Compat (k m) (ρM) := by
  exact Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, ρM, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)

theorem uv_sq {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) ((uvM i F G N) * (uvM i F G N)) 1 := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![49152 * K ^ 5 - 6144 * K ^ 4 + 62976 * K ^ 3 - 5568 * K ^ 2 + 2352 * K - 168, -524288 * K ^ 7 + 16384 * K ^ 6 - 731136 * K ^ 5 + 3072 * K ^ 4 - 38976 * K ^ 3 + 1296 * K ^ 2 - 520 * K + 38, -8388608 * K ^ 9 + 1048576 * K ^ 8 - 15990784 * K ^ 7 + 1343488 * K ^ 6 - 1443840 * K ^ 5 + 119808 * K ^ 4 - 44992 * K ^ 3 + 3680 * K ^ 2 - 476 * K + 38; 46080 * K ^ 3 - 2592 * K ^ 2 + 1386 * K - 81, -491520 * K ^ 5 - 18432 * K ^ 4 - 16032 * K ^ 3 - 522 * K ^ 2 + 195 * K, -7864320 * K ^ 7 + 442368 * K ^ 6 - 162816 * K ^ 5 + 3072 * K ^ 4 - 6432 * K ^ 3 + 1488 * K ^ 2 - 282 * K + 57; -4608 * K ^ 3 - 144 * K + 27, 49152 * K ^ 5 + 4608 * K ^ 4 - 1536 * K ^ 3 - 144 * K ^ 2 - 96 * K - 9, 786432 * K ^ 7 - 270336 * K ^ 5 - 21504 * K ^ 4 + 9312 * K ^ 3 - 3306 * K ^ 2 + 795 * K - 84]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (24576 * K ^ 4 + 18432 * G * K ^ 2 - 3072 * K ^ 3 + 13824 * G ^ 2 - 2304 * G * K + 74496 * K ^ 2 + 88128 * G - 8160 * K + 131544) * hG'
    | linear_combination (-262144 * K ^ 6 - 196608 * G * K ^ 4 + 8192 * K ^ 5 - 147456 * G ^ 2 * K ^ 2 + 6144 * G * K ^ 3 - 824320 * K ^ 4 - 110592 * G ^ 3 + 4608 * G ^ 2 * K - 962304 * G * K ^ 2 + 15872 * K ^ 3 - 981504 * G ^ 2 + 22656 * G * K - 1462048 * K ^ 2 - 2790720 * G + 28424 * K - 2573208) * hG'
    | linear_combination (-4194304 * K ^ 8 - 3145728 * G * K ^ 6 + 524288 * K ^ 7 - 2359296 * G ^ 2 * K ^ 4 + 393216 * G * K ^ 5 - 15335424 * K ^ 6 - 1769472 * G ^ 3 * K ^ 2 + 294912 * G ^ 2 * K ^ 3 - 17006592 * G * K ^ 4 + 1589248 * K ^ 5 - 1327104 * G ^ 4 + 221184 * G ^ 3 * K - 16883712 * G ^ 2 * K ^ 2 + 1880064 * G * K ^ 3 - 27558912 * K ^ 4 - 15759360 * G ^ 3 + 1926144 * G ^ 2 * K - 50430720 * G * K ^ 2 + 2841088 * K ^ 3 - 67371264 * G ^ 2 + 5420928 * G * K - 48250592 * K ^ 2 - 124449696 * G + 4973744 * K - 84448008) * hG'
    | linear_combination (46080 * K ^ 2 + 34560 * G - 2592 * K + 82080) * hG'
    | linear_combination (-491520 * K ^ 4 - 368640 * G * K ^ 2 - 18432 * K ^ 3 - 276480 * G ^ 2 - 13824 * G * K - 876192 * K ^ 2 - 1304640 * G - 32832 * K - 1538784) * hG'
    | linear_combination (-7864320 * K ^ 6 - 5898240 * G * K ^ 4 + 442368 * K ^ 5 - 4423680 * G ^ 2 * K ^ 2 + 331776 * G * K ^ 3 - 13925376 * K ^ 4 - 3317760 * G ^ 3 + 248832 * G ^ 2 * K - 20765952 * G * K ^ 2 + 777216 * K ^ 3 - 23321088 * G ^ 2 + 1163520 * G * K - 24375840 * K ^ 2 - 54646272 * G + 1361616 * K - 42685704) * hG'
    | linear_combination (-4608 * K ^ 2 - 3456 * G - 8208) * hG'
    | linear_combination (49152 * K ^ 4 + 36864 * G * K ^ 2 + 4608 * K ^ 3 + 27648 * G ^ 2 + 3456 * G * K + 84480 * K ^ 2 + 127872 * G + 7920 * K + 147744) * hG'
    | linear_combination (786432 * K ^ 6 + 589824 * G * K ^ 4 + 442368 * G ^ 2 * K ^ 2 + 1105920 * K ^ 4 + 331776 * G ^ 3 + 1861632 * G * K ^ 2 - 21504 * K ^ 3 + 2170368 * G ^ 2 - 16128 * G * K + 1944672 * K ^ 2 + 4713984 * G - 40992 * K + 3398328) * hG'

theorem t_sq {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) ((tM i F G N) * (tM i F G N)) 1 := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 2 (W := !![3072 * K ^ 3 - 2064 * K - 72, -65536 * K ^ 5 + 512 * K ^ 4 + 54272 * K ^ 3 + 656 * K ^ 2 + 1760 * K + 20, -49152 * K ^ 5 - 1536 * K ^ 4 + 27648 * K ^ 3 + 2832 * K ^ 2 + 948 * K + 18; -576 * K - 9, 16896 * K ^ 3 - 288 * K ^ 2 + 609 * K - 9, 7680 * K ^ 3 + 672 * K ^ 2 + 240 * K + 3; -1152 * K - 18, 29184 * K ^ 3 + 912 * K, 17664 * K ^ 3 + 1056 * K ^ 2 + 633 * K - 3]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (1536 * K ^ 2 + 1152 * G + 1656) * hG'
    | linear_combination (-32768 * K ^ 4 - 24576 * G * K ^ 2 + 256 * K ^ 3 - 18432 * G ^ 2 + 192 * G * K - 30208 * K ^ 2 - 65664 * G + 776 * K - 51984) * hG'
    | linear_combination (-24576 * K ^ 4 - 18432 * G * K ^ 2 - 768 * K ^ 3 - 13824 * G ^ 2 - 576 * G * K - 29184 * K ^ 2 - 54144 * G + 72 * K - 50616) * hG'
    | linear_combination (-576) * hG'
    | linear_combination (16896 * K ^ 2 + 12672 * G - 288 * K + 30168) * hG'
    | linear_combination (7680 * K ^ 2 + 5760 * G + 672 * K + 13680) * hG'
    | linear_combination (-1152) * hG'
    | linear_combination (29184 * K ^ 2 + 21888 * G + 51984) * hG'
    | linear_combination (17664 * K ^ 2 + 13248 * G + 1056 * K + 31536) * hG'

theorem uv_comm_t {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) ((tM i F G N) * (uvM i F G N)) ((uvM i F G N) * (tM i F G N)) := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![98304 * K ^ 5 - 12288 * K ^ 4 + 112128 * K ^ 3 - 11136 * K ^ 2 + 3408 * K - 228, -2097152 * K ^ 7 + 262144 * K ^ 6 - 2457600 * K ^ 5 + 245760 * K ^ 4 - 129024 * K ^ 3 + 12288 * K ^ 2 - 1804 * K + 152, -3670016 * K ^ 7 + 294912 * K ^ 6 + 2270208 * K ^ 5 - 125952 * K ^ 4 + 78624 * K ^ 3 + 768 * K ^ 2 + 128 * K + 156; 92160 * K ^ 3 - 5184 * K ^ 2 + 4500 * K - 108, -1966080 * K ^ 5 + 110592 * K ^ 4 - 159744 * K ^ 3 + 6336 * K ^ 2 - 3099 * K + 90, -73728 * K ^ 5 - 93696 * K ^ 4 - 40896 * K ^ 3 - 3012 * K ^ 2 - 1206 * K + 48; -9216 * K ^ 3 - 2016 * K, 196608 * K ^ 5 + 65280 * K ^ 3 - 576 * K ^ 2 + 1794 * K - 18, 1916928 * K ^ 5 - 104448 * K ^ 4 + 103680 * K ^ 3 - 768 * K ^ 2 + 1395 * K + 24]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (49152 * K ^ 4 + 36864 * G * K ^ 2 - 6144 * K ^ 3 + 27648 * G ^ 2 - 4608 * G * K + 142080 * K ^ 2 + 171072 * G - 16320 * K + 250344) * hG'
    | linear_combination (-1048576 * K ^ 6 - 786432 * G * K ^ 4 + 131072 * K ^ 5 - 589824 * G ^ 2 * K ^ 2 + 98304 * G * K ^ 3 - 3063808 * K ^ 4 - 442368 * G ^ 3 + 73728 * G ^ 2 * K - 3674112 * G * K ^ 2 + 352256 * K ^ 3 - 3787776 * G ^ 2 + 436224 * G * K - 5426176 * K ^ 2 - 10499328 * G + 622592 * K - 9496656) * hG'
    | linear_combination (-1835008 * K ^ 6 - 1376256 * G * K ^ 4 + 147456 * K ^ 5 - 1032192 * G ^ 2 * K ^ 2 + 110592 * G * K ^ 3 - 2076160 * K ^ 4 - 774144 * G ^ 3 + 82944 * G ^ 2 * K - 3965568 * G * K ^ 2 + 195072 * K ^ 3 - 4783104 * G ^ 2 + 339840 * G * K - 3593968 * K ^ 2 - 9647424 * G + 341760 * K - 6303744) * hG'
    | linear_combination (92160 * K ^ 2 + 69120 * G - 5184 * K + 165888) * hG'
    | linear_combination (-1966080 * K ^ 4 - 1474560 * G * K ^ 2 + 110592 * K ^ 3 - 1105920 * G ^ 2 + 82944 * G * K - 3600384 * K ^ 2 - 5282496 * G + 199872 * K - 6307848) * hG'
    | linear_combination (-73728 * K ^ 4 - 55296 * G * K ^ 2 - 93696 * K ^ 3 - 41472 * G ^ 2 - 70272 * G * K - 169920 * K ^ 2 - 228096 * G - 167088 * K - 307800) * hG'
    | linear_combination (-9216 * K ^ 2 - 6912 * G - 18144) * hG'
    | linear_combination (196608 * K ^ 4 + 147456 * G * K ^ 2 + 110592 * G ^ 2 + 409344 * K ^ 2 + 565056 * G - 576 * K + 718200) * hG'
    | linear_combination (1916928 * K ^ 4 + 1437696 * G * K ^ 2 - 104448 * K ^ 3 + 1078272 * G ^ 2 - 78336 * G * K + 3458304 * K ^ 2 + 5111424 * G - 183552 * K + 6057504) * hG'

theorem rho_cube {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) (ρM * (ρM * ρM)) 1 := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 0 (W := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem u_sq {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) ((uM F) * (uM F)) 1 := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 0 (W := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem u_rho {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) (ρM * ((uM F) * (ρM * (uM F)))) 1 := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 0 (W := !![0, 32 * K, 0; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (16) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem uv_rho {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) (ρM * (uvM i F G N)) ((tM i F G N) * ρM) := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 2 (W := !![0, 0, -8192 * K ^ 5 + 1024 * K ^ 4 - 12032 * K ^ 3 + 928 * K ^ 2 - 1520 * K + 10; 0, 0, -768 * K ^ 3 - 312 * K; 0, 0, -8448 * K ^ 3 + 432 * K ^ 2 - 831 * K + 9]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (-4096 * K ^ 4 - 3072 * G * K ^ 2 + 512 * K ^ 3 - 2304 * G ^ 2 + 384 * G * K - 13184 * K ^ 2 - 15264 * G + 1360 * K - 23832) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (-768 * K ^ 2 - 576 * G - 1656) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (-8448 * K ^ 2 - 6336 * G + 432 * K - 15624) * hG'

theorem t_rho {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) (ρM * (tM i F G N)) ((tM i F G N) * ((uvM i F G N) * ρM)) := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![1728 * K - 108, 1835008 * K ^ 7 - 114688 * K ^ 6 - 4451328 * K ^ 5 + 285696 * K ^ 4 - 234336 * K ^ 3 + 8976 * K ^ 2 - 2920 * K - 2, -1835008 * K ^ 7 + 114688 * K ^ 6 + 4426752 * K ^ 5 - 282624 * K ^ 4 + 299616 * K ^ 3 - 11376 * K ^ 2 + 4876 * K + 140; 864 * K - 54, -1646592 * K ^ 5 + 144384 * K ^ 4 - 103488 * K ^ 3 + 6090 * K ^ 2 - 1626 * K + 51, 1646592 * K ^ 5 - 144384 * K ^ 4 + 128832 * K ^ 3 - 7386 * K ^ 2 + 2391 * K + 30; 432 * K - 27, -1744896 * K ^ 5 + 109056 * K ^ 4 - 72192 * K ^ 3 + 1920 * K ^ 2 - 552 * K - 33, 1744896 * K ^ 5 - 109056 * K ^ 4 + 95232 * K ^ 3 - 3216 * K ^ 2 + 1245 * K + 60]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (864) * hG'
    | linear_combination (917504 * K ^ 6 + 688128 * G * K ^ 4 - 57344 * K ^ 5 + 516096 * G ^ 2 * K ^ 2 - 43008 * G * K ^ 3 - 620032 * K ^ 4 + 387072 * G ^ 3 - 32256 * G ^ 2 * K + 739200 * G * K ^ 2 + 42496 * K ^ 3 + 1458432 * G ^ 2 - 43392 * G * K - 1202224 * K ^ 2 + 393984 * G + 78856 * K - 2105352) * hG'
    | linear_combination (-917504 * K ^ 6 - 688128 * G * K ^ 4 + 57344 * K ^ 5 - 516096 * G ^ 2 * K ^ 2 + 43008 * G * K ^ 3 + 607744 * K ^ 4 - 387072 * G ^ 3 + 32256 * G ^ 2 * K - 748416 * G * K ^ 2 - 40960 * K ^ 3 - 1465344 * G ^ 2 + 44544 * G * K + 1213360 * K ^ 2 - 401760 * G - 77368 * K + 2125872) * hG'
    | linear_combination (864) * hG'
    | linear_combination (-1646592 * K ^ 4 - 1234944 * G * K ^ 2 + 144384 * K ^ 3 - 926208 * G ^ 2 + 108288 * G * K - 2985024 * K ^ 2 - 4399488 * G + 258816 * K - 5224392) * hG'
    | linear_combination (1646592 * K ^ 4 + 1234944 * G * K ^ 2 - 144384 * K ^ 3 + 926208 * G ^ 2 - 108288 * G * K + 3010368 * K ^ 2 + 4418496 * G - 260112 * K + 5269536) * hG'
    | linear_combination (432) * hG'
    | linear_combination (-1744896 * K ^ 4 - 1308672 * G * K ^ 2 + 109056 * K ^ 3 - 981504 * G ^ 2 + 81792 * G * K - 3125760 * K ^ 2 - 4636224 * G + 192768 * K - 5474736) * hG'
    | linear_combination (1744896 * K ^ 4 + 1308672 * G * K ^ 2 - 109056 * K ^ 3 + 981504 * G ^ 2 - 81792 * G * K + 3148800 * K ^ 2 + 4653504 * G - 194064 * K + 5515776) * hG'

theorem uv_comm_u {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) ((uM F) * (uvM i F G N)) ((uvM i F G N) * (uM F)) := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 2 (W := !![0, 8192 * K ^ 5 - 1024 * K ^ 4 + 11264 * K ^ 3 - 1120 * K ^ 2 + 344 * K - 16, 303104 * K ^ 5 - 19456 * K ^ 4 + 1664 * K ^ 3 - 352 * K ^ 2 - 208 * K + 8; 0, 7680 * K ^ 3 - 432 * K ^ 2 + 519 * K - 9, 768 * K ^ 3 + 312 * K; 0, -768 * K ^ 3 - 312 * K, -7680 * K ^ 3 + 432 * K ^ 2 - 519 * K + 9]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (4096 * K ^ 4 + 3072 * G * K ^ 2 - 512 * K ^ 3 + 2304 * G ^ 2 - 384 * G * K + 12800 * K ^ 2 + 14976 * G - 1456 * K + 22572) * hG'
    | linear_combination (151552 * K ^ 4 + 113664 * G * K ^ 2 - 9728 * K ^ 3 + 85248 * G ^ 2 - 7296 * G * K + 266048 * K ^ 2 + 398592 * G - 17200 * K + 465804) * hG'
    | linear_combination (0) * hG'
    | linear_combination (7680 * K ^ 2 + 5760 * G - 432 * K + 13968) * hG'
    | linear_combination (768 * K ^ 2 + 576 * G + 1656) * hG'
    | linear_combination (0) * hG'
    | linear_combination (-768 * K ^ 2 - 576 * G - 1656) * hG'
    | linear_combination (-7680 * K ^ 2 - 5760 * G + 432 * K - 13968) * hG'

theorem t_u {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    MatEq (k m) ((uM F) * (tM i F G N)) ((tM i F G N) * ((uvM i F G N) * (uM F))) := by
  obtain ⟨hi, hF, hN, hK, hG⟩ := h
  subst hi
  subst hF
  subst hK
  have hG' : 3 * G + 7 = 4 * K * K := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 2 * K := hN.symm
  have h1 : (2 : ℤ) ^ (m + 1) = 4 * K := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![-3456 * K + 108, 1835008 * K ^ 7 - 114688 * K ^ 6 - 4451328 * K ^ 5 + 285696 * K ^ 4 - 229728 * K ^ 3 + 10704 * K ^ 2 - 2776 * K - 110, 24576 * K ^ 5 - 3072 * K ^ 4 - 76800 * K ^ 3 + 5856 * K ^ 2 - 2316 * K - 84; -864 * K + 54, -1646592 * K ^ 5 + 144384 * K ^ 4 - 121920 * K ^ 3 + 7242 * K ^ 2 - 2202 * K - 21, -43776 * K ^ 3 + 2448 * K ^ 2 - 1341 * K - 45; -432 * K + 27, -1744896 * K ^ 5 + 109056 * K ^ 4 - 81408 * K ^ 3 + 2496 * K ^ 2 - 840 * K - 69, -32256 * K ^ 3 + 1872 * K ^ 2 - 981 * K - 9]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (-1728) * hG'
    | linear_combination (917504 * K ^ 6 + 688128 * G * K ^ 4 - 57344 * K ^ 5 + 516096 * G ^ 2 * K ^ 2 - 43008 * G * K ^ 3 - 620032 * K ^ 4 + 387072 * G ^ 3 - 32256 * G ^ 2 * K + 739200 * G * K ^ 2 + 42496 * K ^ 3 + 1458432 * G ^ 2 - 43392 * G * K - 1199920 * K ^ 2 + 395712 * G + 79720 * K - 2101248) * hG'
    | linear_combination (12288 * K ^ 4 + 9216 * G * K ^ 2 - 1536 * K ^ 3 + 6912 * G ^ 2 - 1152 * G * K - 16896 * K ^ 2 + 3456 * G + 240 * K - 30780) * hG'
    | linear_combination (-864) * hG'
    | linear_combination (-1646592 * K ^ 4 - 1234944 * G * K ^ 2 + 144384 * K ^ 3 - 926208 * G ^ 2 + 108288 * G * K - 3003456 * K ^ 2 - 4413312 * G + 259968 * K - 5257224) * hG'
    | linear_combination (-43776 * K ^ 2 - 32832 * G + 2448 * K - 77976) * hG'
    | linear_combination (-432) * hG'
    | linear_combination (-1744896 * K ^ 4 - 1308672 * G * K ^ 2 + 109056 * K ^ 3 - 981504 * G ^ 2 + 81792 * G * K - 3134976 * K ^ 2 - 4643136 * G + 193344 * K - 5491152) * hG'
    | linear_combination (-32256 * K ^ 2 - 24192 * G + 1872 * K - 57456) * hG'

@[expose] def action {m : ℕ} {i F G N K : ℤ} (h : Data m i F G N K) :
    SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM i F G N) (tM i F G N) (uM F) ρM
    (compat_uv h) (compat_t h) (compat_u h) (compat_rho h)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

theorem data (m : ℕ) (hm : 1 ≤ m) :
    Data m (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) (2 ^ (m - 1)) := by
  obtain ⟨hi, hF, -⟩ := Type120.data m hm
  have hdvd : ∀ e : ℕ, (3 : ℤ) ∣ 4 ^ e - 1 := fun e => by
    simpa using sub_one_dvd_pow_sub_one (4 : ℤ) e
  obtain ⟨c, hc⟩ := hdvd m
  have hG : 3 * Type120.GV (m + 1) + 7 = 4 ^ m := by
    have := Int.mul_ediv_cancel' (a := 3) (b := (4 : ℤ) ^ m - 7) ⟨c - 2, by linarith⟩
    simp only [Type120.GV, Nat.add_sub_cancel]
    linarith
  refine ⟨hi, hF, rfl, ?_, ?_⟩
  · have h' : (2 : ℤ) ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [← h']
    ring
  · rw [hG, ← mul_pow]
    norm_num

@[expose] def actionPaper (m : ℕ) (hm : 1 ≤ m) : SigmaFourAction (k m) :=
  action (data m hm)


end Type121

namespace Type130

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 1, m + 1]

@[expose] def ρM : IntMat := ofCols ![1, 0, 0] ![0, 0, 1] ![-2, -1, -1]

@[expose] def uvA (i F : ℤ) : Fin 3 → ℤ := ![2 * F * i, -5 * i, 2 * i]

@[expose] def tM (i F G N : ℤ) : IntMat :=
  ofCols ![4 - i, 2, 4 + N] ![4 * G * i, -7 * i, -8 * i] (ρM *ᵥ uvA i F)

@[expose] def uvM (i F G N : ℤ) : IntMat :=
  ofCols ![-i, 2 + N, -2] (uvA i F) (ρM *ᵥ (tM i F G N *ᵥ uvA i F))

@[expose] def uM (F K : ℤ) : IntMat := uMat ![-1 + K, 0, 0] (-4 * F)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

structure Data (m : ℕ) (i F G N K J : ℤ) : Prop where
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hN : N = 2 ^ m
  hK : N = 2 * K
  hJ : K = 2 * J
  hG : 3 * G + 7 = N * N

theorem uv_sq {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((uvM i F G N) * (uvM i F G N)) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 4 (W := !![4718592 * J ^ 5 + 737280 * J ^ 4 + 1511424 * J ^ 3 - 5760 * J ^ 2 + 14112 * J - 90, -201326592 * J ^ 7 - 25165824 * J ^ 6 - 70778880 * J ^ 5 - 1069056 * J ^ 3 + 4608 * J ^ 2 - 4128 * J + 24, 17179869184 * J ^ 10 - 10737418240 * J ^ 9 + 3087007744 * J ^ 8 - 6174015488 * J ^ 7 - 11534336 * J ^ 6 - 139591680 * J ^ 5 - 581632 * J ^ 4 - 1071104 * J ^ 3 - 1408 * J ^ 2 - 2752 * J + 8; 147456 * J ^ 4 + 1105920 * J ^ 3 - 11520 * J ^ 2 + 8640 * J - 99, -6291456 * J ^ 6 - 47185920 * J ^ 5 + 73728 * J ^ 4 - 460800 * J ^ 3 + 576 * J ^ 2 + 576 * J - 3, 536870912 * J ^ 9 + 3623878656 * J ^ 8 - 3028287488 * J ^ 7 + 20447232 * J ^ 6 - 17203200 * J ^ 5 - 2359296 * J ^ 4 - 141824 * J ^ 3 - 19872 * J ^ 2 - 1504 * J - 15; 147456 * J ^ 4 - 110592 * J ^ 3 + 2304 * J ^ 2 - 864 * J + 9, -6291456 * J ^ 6 + 4718592 * J ^ 5 - 36864 * J ^ 3 + 1152 * J ^ 2 - 576 * J + 6, 536870912 * J ^ 9 - 805306368 * J ^ 8 + 293601280 * J ^ 7 - 25165824 * J ^ 6 - 26050560 * J ^ 5 + 442368 * J ^ 4 + 148480 * J ^ 3 + 3072 * J ^ 2 + 4184 * J - 12]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (1179648 * J ^ 4 + 221184 * G * J ^ 2 + 184320 * J ^ 3 + 41472 * G ^ 2 + 34560 * G * J + 893952 * J ^ 2 + 264384 * G + 79200 * J + 394632) * hG'
    | linear_combination (-50331648 * J ^ 6 - 9437184 * G * J ^ 4 - 6291456 * J ^ 5 - 1769472 * G ^ 2 * J ^ 2 - 1179648 * G * J ^ 3 - 39714816 * J ^ 4 - 331776 * G ^ 3 - 221184 * G ^ 2 * J - 11575296 * G * J ^ 2 - 2752512 * J ^ 3 - 2944512 * G ^ 2 - 1032192 * G * J - 17642496 * J ^ 2 - 8372160 * G - 1203072 * J - 7719624) * hG'
    | linear_combination (4294967296 * J ^ 9 + 805306368 * G * J ^ 7 - 2684354560 * J ^ 8 + 150994944 * G ^ 2 * J ^ 5 - 503316480 * G * J ^ 6 + 2650800128 * J ^ 7 + 28311552 * G ^ 3 * J ^ 3 - 94371840 * G ^ 2 * J ^ 4 + 849346560 * G * J ^ 5 - 2717908992 * J ^ 6 + 5308416 * G ^ 4 * J - 17694720 * G ^ 3 * J ^ 2 + 225312768 * G ^ 2 * J ^ 3 - 729808896 * G * J ^ 4 + 1156841472 * J ^ 5 - 3981312 * G ^ 4 + 54632448 * G ^ 3 * J - 178126848 * G ^ 2 * J ^ 2 + 588496896 * G * J ^ 3 - 1223983104 * J ^ 4 - 47278080 * G ^ 3 + 208917504 * G ^ 2 * J - 548788224 * G * J ^ 2 + 505972736 * J ^ 3 - 202113792 * G ^ 2 + 352337280 * G * J - 535760384 * J ^ 2 - 373349088 * G + 221362720 * J - 253344024) * hG'
    | linear_combination (73728 * J ^ 3 + 13824 * G * J + 552960 * J ^ 2 + 103680 * G + 26496 * J + 246240) * hG'
    | linear_combination (-3145728 * J ^ 5 - 589824 * G * J ^ 3 - 23592960 * J ^ 4 - 110592 * G ^ 2 * J - 4423680 * G * J ^ 2 - 1339392 * J ^ 3 - 829440 * G ^ 2 - 509184 * G * J - 10552320 * J ^ 2 - 3913920 * G - 585696 * J - 4616352) * hG'
    | linear_combination (268435456 * J ^ 8 + 50331648 * G * J ^ 6 + 1811939328 * J ^ 7 + 9437184 * G ^ 2 * J ^ 4 + 339738624 * G * J ^ 5 - 1396703232 * J ^ 6 + 1769472 * G ^ 3 * J ^ 2 + 63700992 * G ^ 2 * J ^ 3 - 239861760 * G * J ^ 4 + 802947072 * J ^ 5 + 11943936 * G ^ 3 * J - 40845312 * G ^ 2 * J ^ 2 + 299188224 * G * J ^ 3 - 619659264 * J ^ 4 - 9953280 * G ^ 3 + 83966976 * G ^ 2 * J - 221125632 * G * J ^ 2 + 350109696 * J ^ 3 - 69963264 * G ^ 2 + 196540416 * G * J - 271171840 * J ^ 2 - 163938816 * G + 153163056 * J - 128057112) * hG'
    | linear_combination (73728 * J ^ 3 + 13824 * G * J - 55296 * J ^ 2 - 10368 * G + 33408 * J - 24624) * hG'
    | linear_combination (-3145728 * J ^ 5 - 589824 * G * J ^ 3 + 2359296 * J ^ 4 - 110592 * G ^ 2 * J + 442368 * G * J ^ 2 - 1376256 * J ^ 3 + 82944 * G ^ 2 - 516096 * G * J + 1013760 * J ^ 2 + 383616 * G - 601536 * J + 443232) * hG'
    | linear_combination (268435456 * J ^ 8 + 50331648 * G * J ^ 6 - 402653184 * J ^ 7 + 9437184 * G ^ 2 * J ^ 4 - 75497472 * G * J ^ 5 + 264241152 * J ^ 6 + 1769472 * G ^ 3 * J ^ 2 - 14155776 * G ^ 2 * J ^ 3 + 71565312 * G * J ^ 4 - 188743680 * J ^ 5 - 2654208 * G ^ 3 * J + 17547264 * G ^ 2 * J ^ 2 - 68419584 * G * J ^ 3 + 102580224 * J ^ 4 + 995328 * G ^ 3 - 19021824 * G ^ 2 * J + 50543616 * G * J ^ 2 - 82354176 * J ^ 3 + 6511104 * G ^ 2 - 45374976 * G * J + 44953088 * J ^ 2 + 14141952 * G - 36028416 * J + 10194984) * hG'

theorem t_sq {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((tM i F G N) * (tM i F G N)) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 2 (W := !![16384 * J ^ 4 + 24576 * J ^ 3 - 1664 * J ^ 2 - 4128 * J - 14, -2097152 * J ^ 5 + 434176 * J ^ 3 + 3520 * J, -1572864 * J ^ 5 + 221184 * J ^ 3 + 1824 * J; -384 * J ^ 2 - 1152 * J - 3, 135168 * J ^ 3 + 1200 * J, 61440 * J ^ 3 + 480 * J; -1536 * J ^ 2 - 2304 * J + 6, 4096 * J ^ 4 + 233472 * J ^ 3 - 1760 * J ^ 2 + 1824 * J - 14, 8192 * J ^ 4 + 141312 * J ^ 3 - 832 * J ^ 2 + 1248 * J - 7]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (4096 * J ^ 3 + 768 * G * J + 6144 * J ^ 2 + 1152 * G + 1376 * J + 1656) * hG'
    | linear_combination (-524288 * J ^ 4 - 98304 * G * J ^ 2 - 18432 * G ^ 2 - 120832 * J ^ 2 - 65664 * G - 51984) * hG'
    | linear_combination (-393216 * J ^ 4 - 73728 * G * J ^ 2 - 13824 * G ^ 2 - 116736 * J ^ 2 - 54144 * G - 50616) * hG'
    | linear_combination (-192 * J - 576) * hG'
    | linear_combination (67584 * J ^ 2 + 12672 * G + 30168) * hG'
    | linear_combination (30720 * J ^ 2 + 5760 * G + 13680) * hG'
    | linear_combination (-768 * J - 1152) * hG'
    | linear_combination (2048 * J ^ 3 + 384 * G * J + 116736 * J ^ 2 + 21888 * G + 16 * J + 51984) * hG'
    | linear_combination (4096 * J ^ 3 + 768 * G * J + 70656 * J ^ 2 + 13248 * G + 1376 * J + 31536) * hG'

theorem uv_comm_t {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((tM i F G N) * (uvM i F G N)) ((uvM i F G N) * (tM i F G N)) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![3145728 * J ^ 6 + 3538944 * J ^ 5 + 1351680 * J ^ 4 + 893952 * J ^ 3 - 4224 * J ^ 2 + 6768 * J - 114, -268435456 * J ^ 7 - 33554432 * J ^ 6 - 78643200 * J ^ 5 - 1032192 * J ^ 3 + 6144 * J ^ 2 - 3392 * J + 32, -134217728 * J ^ 8 - 469762048 * J ^ 7 + 4194304 * J ^ 6 + 72351744 * J ^ 5 - 368640 * J ^ 4 + 626688 * J ^ 3 + 2432 * J ^ 2 + 256 * J + 44; 98304 * J ^ 5 + 835584 * J ^ 4 + 736512 * J ^ 3 + 4992 * J ^ 2 + 9204 * J - 66, -8388608 * J ^ 6 - 62914560 * J ^ 5 - 12288 * J ^ 4 - 1296384 * J ^ 3 + 6816 * J ^ 2 - 6288 * J + 50, 2097152 * J ^ 6 - 2359296 * J ^ 5 - 122880 * J ^ 4 - 368640 * J ^ 3 + 2880 * J ^ 2 - 2736 * J + 31; 98304 * J ^ 5 + 24576 * J ^ 4 - 74496 * J ^ 3 - 8256 * J ^ 2 - 4044 * J - 66, -8388608 * J ^ 6 + 6291456 * J ^ 5 + 24576 * J ^ 4 + 522240 * J ^ 3 + 1344 * J ^ 2 + 3696 * J + 5, 6815744 * J ^ 6 + 61145088 * J ^ 5 - 663552 * J ^ 4 + 849408 * J ^ 3 - 4704 * J ^ 2 + 2904 * J + 7]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (786432 * J ^ 5 + 147456 * G * J ^ 3 + 884736 * J ^ 4 + 27648 * G ^ 2 * J + 165888 * G * J ^ 2 + 681984 * J ^ 3 + 27648 * G ^ 2 + 192384 * G * J + 610560 * J ^ 2 + 171072 * G + 297312 * J + 250344) * hG'
    | linear_combination (-67108864 * J ^ 6 - 12582912 * G * J ^ 4 - 8388608 * J ^ 5 - 2359296 * G ^ 2 * J ^ 2 - 1572864 * G * J ^ 3 - 49020928 * J ^ 4 - 442368 * G ^ 3 - 294912 * G ^ 2 * J - 14696448 * G * J ^ 2 - 3670016 * J ^ 3 - 3787776 * G ^ 2 - 1376256 * G * J - 21704704 * J ^ 2 - 10499328 * G - 1604096 * J - 9496656) * hG'
    | linear_combination (-33554432 * J ^ 7 - 6291456 * G * J ^ 5 - 117440512 * J ^ 6 - 1179648 * G ^ 2 * J ^ 3 - 22020096 * G * J ^ 4 - 13631488 * J ^ 5 - 221184 * G ^ 3 * J - 4128768 * G ^ 2 * J ^ 2 - 5308416 * G * J ^ 3 - 33292288 * J ^ 4 - 774144 * G ^ 3 - 1511424 * G ^ 2 * J - 15876096 * G * J ^ 2 - 6055936 * J ^ 3 - 4783104 * G ^ 2 - 3457920 * G * J - 14408704 * J ^ 2 - 9647424 * G - 2648864 * J - 6303744) * hG'
    | linear_combination (49152 * J ^ 4 + 9216 * G * J ^ 2 + 417792 * J ^ 3 + 78336 * G * J + 389760 * J ^ 2 + 69120 * G + 185280 * J + 165888) * hG'
    | linear_combination (-4194304 * J ^ 5 - 786432 * G * J ^ 3 - 31457280 * J ^ 4 - 147456 * G ^ 2 * J - 5898240 * G * J ^ 2 - 1841152 * J ^ 3 - 1105920 * G ^ 2 - 689280 * G * J - 14410752 * J ^ 2 - 5282496 * G - 802096 * J - 6307848) * hG'
    | linear_combination (1048576 * J ^ 5 + 196608 * G * J ^ 3 - 1179648 * J ^ 4 + 36864 * G ^ 2 * J - 221184 * G * J ^ 2 + 397312 * J ^ 3 - 41472 * G ^ 2 + 160512 * G * J - 700416 * J ^ 2 - 228096 * G + 175264 * J - 307800) * hG'
    | linear_combination (49152 * J ^ 4 + 9216 * G * J ^ 2 + 12288 * J ^ 3 + 2304 * G * J - 15744 * J ^ 2 - 6912 * G + 1248 * J - 18144) * hG'
    | linear_combination (-4194304 * J ^ 5 - 786432 * G * J ^ 3 + 3145728 * J ^ 4 - 147456 * G ^ 2 * J + 589824 * G * J ^ 2 - 1822720 * J ^ 3 + 110592 * G ^ 2 - 685824 * G * J + 1637376 * J ^ 2 + 565056 * G - 796768 * J + 718200) * hG'
    | linear_combination (3407872 * J ^ 5 + 638976 * G * J ^ 3 + 30572544 * J ^ 4 + 119808 * G ^ 2 * J + 5732352 * G * J ^ 2 + 1159168 * J ^ 3 + 1078272 * G ^ 2 + 496896 * G * J + 13800192 * J ^ 2 + 5111424 * G + 504784 * J + 6057504) * hG'

theorem rho_cube {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) (ρM * (ρM * ρM)) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 0 (W := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem u_sq {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((uM F K) * (uM F K)) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 1 (W := !![3 * J - 3, 0, 256 * J ^ 3 - 256 * J ^ 2 - 4 * J + 4; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (64 * J ^ 2 - 64 * J) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem u_rho {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) (ρM * ((uM F K) * (ρM * (uM F K)))) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 1 (W := !![3 * J - 3, -256 * J ^ 2 + 192 * J + 1, 256 * J ^ 3 - 128 * J ^ 2 - 4 * J + 2; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (-64 * J + 48) * hG'
    | linear_combination (64 * J ^ 2 - 32 * J) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem uv_rho {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) (ρM * (uvM i F G N)) ((tM i F G N) * ρM) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 2 (W := !![0, 0, -262144 * J ^ 5 - 96256 * J ^ 3 - 3040 * J; 0, 0, 8192 * J ^ 4 - 6144 * J ^ 3 - 64 * J ^ 2 - 624 * J - 1; 0, 0, -67584 * J ^ 3 - 1680 * J + 9]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (-65536 * J ^ 4 - 12288 * G * J ^ 2 - 2304 * G ^ 2 - 52736 * J ^ 2 - 15264 * G - 23832) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (4096 * J ^ 3 + 768 * G * J - 3072 * J ^ 2 - 576 * G + 1760 * J - 1656) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (-33792 * J ^ 2 - 6336 * G - 15624) * hG'

theorem t_rho {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) (ρM * (tM i F G N)) ((tM i F G N) * ((uvM i F G N) * ρM)) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![-24576 * J ^ 4 + 10560 * J ^ 2 + 3456 * J + 30, 134217728 * J ^ 8 + 234881024 * J ^ 7 - 33554432 * J ^ 6 - 142344192 * J ^ 5 + 368640 * J ^ 4 - 1916928 * J ^ 3 + 2944 * J ^ 2 - 6176 * J - 16, -134217728 * J ^ 8 - 234881024 * J ^ 7 + 33554432 * J ^ 6 + 141557760 * J ^ 5 - 319488 * J ^ 4 + 2439168 * J ^ 3 - 24064 * J ^ 2 + 10304 * J - 152; 4032 * J ^ 2 + 1728 * J + 18, -9437184 * J ^ 6 - 52690944 * J ^ 5 + 98304 * J ^ 4 - 823296 * J ^ 3 + 960 * J ^ 2 - 3216 * J - 3, 9437184 * J ^ 6 + 52690944 * J ^ 5 - 98304 * J ^ 4 + 1026048 * J ^ 3 - 9024 * J ^ 2 + 4800 * J - 60; 5184 * J ^ 2 + 864 * J + 27, -14155776 * J ^ 6 - 55640064 * J ^ 5 + 663552 * J ^ 4 - 597504 * J ^ 3 + 6048 * J ^ 2 - 1272 * J, 14155776 * J ^ 6 + 55640064 * J ^ 5 - 638976 * J ^ 4 + 781824 * J ^ 3 - 16608 * J ^ 2 + 2712 * J - 84]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (-6144 * J ^ 3 - 1152 * G * J - 48 * J + 864) * hG'
    | linear_combination (33554432 * J ^ 7 + 6291456 * G * J ^ 5 + 58720256 * J ^ 6 + 1179648 * G ^ 2 * J ^ 3 + 11010048 * G * J ^ 4 + 6291456 * J ^ 5 + 221184 * G ^ 3 * J + 2064384 * G ^ 2 * J ^ 2 + 3932160 * G * J ^ 3 - 9895936 * J ^ 4 + 387072 * G ^ 3 + 1253376 * G ^ 2 * J + 2961408 * G * J ^ 2 + 2844672 * J ^ 3 + 1458432 * G ^ 2 + 2253696 * G * J - 4808704 * J ^ 2 + 393984 * G + 1245280 * J - 2105352) * hG'
    | linear_combination (-33554432 * J ^ 7 - 6291456 * G * J ^ 5 - 58720256 * J ^ 6 - 1179648 * G ^ 2 * J ^ 3 - 11010048 * G * J ^ 4 - 6291456 * J ^ 5 - 221184 * G ^ 3 * J - 2064384 * G ^ 2 * J ^ 2 - 3932160 * G * J ^ 3 + 9699328 * J ^ 4 - 387072 * G ^ 3 - 1253376 * G ^ 2 * J - 2998272 * G * J ^ 2 - 2832384 * J ^ 3 - 1465344 * G ^ 2 - 2251392 * G * J + 4853248 * J ^ 2 - 401760 * G - 1245184 * J + 2125872) * hG'
    | linear_combination (2016 * J + 864) * hG'
    | linear_combination (-4718592 * J ^ 5 - 884736 * G * J ^ 3 - 26345472 * J ^ 4 - 165888 * G ^ 2 * J - 4939776 * G * J ^ 2 - 2015232 * J ^ 3 - 926208 * G ^ 2 - 764928 * G * J - 11937792 * J ^ 2 - 4399488 * G - 881184 * J - 5224392) * hG'
    | linear_combination (4718592 * J ^ 5 + 884736 * G * J ^ 3 + 26345472 * J ^ 4 + 165888 * G ^ 2 * J + 4939776 * G * J ^ 2 + 2015232 * J ^ 3 + 926208 * G ^ 2 + 764928 * G * J + 12039168 * J ^ 2 + 4418496 * G + 877152 * J + 5269536) * hG'
    | linear_combination (2592 * J + 432) * hG'
    | linear_combination (-7077888 * J ^ 5 - 1327104 * G * J ^ 3 - 27820032 * J ^ 4 - 248832 * G ^ 2 * J - 5216256 * G * J ^ 2 - 2764800 * J ^ 3 - 981504 * G ^ 2 - 1099008 * G * J - 12470016 * J ^ 2 - 4636224 * G - 1206576 * J - 5474736) * hG'
    | linear_combination (7077888 * J ^ 5 + 1327104 * G * J ^ 3 + 27820032 * J ^ 4 + 248832 * G ^ 2 * J + 5216256 * G * J ^ 2 + 2777088 * J ^ 3 + 981504 * G ^ 2 + 1101312 * G * J + 12562176 * J ^ 2 + 4653504 * G + 1206672 * J + 5515776) * hG'

theorem uv_comm_u {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((uM F K) * (uvM i F G N)) ((uvM i F G N) * (uM F K)) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![-4608 * J ^ 2 + 72, 786432 * J ^ 5 + 221184 * J ^ 4 + 270336 * J ^ 3 - 1728 * J ^ 2 + 2064 * J - 27, -8388608 * J ^ 7 + 13107200 * J ^ 6 + 29097984 * J ^ 5 - 417792 * J ^ 4 + 50688 * J ^ 3 - 7776 * J ^ 2 - 1384 * J - 29; -27 * J, 24576 * J ^ 4 + 184320 * J ^ 3 + 960 * J ^ 2 + 3168 * J - 21, -24576 * J ^ 4 + 16128 * J ^ 3 + 192 * J ^ 2 + 1908 * J + 3; 27, 24576 * J ^ 4 - 18432 * J ^ 3 - 192 * J ^ 2 - 1872 * J - 3, -24576 * J ^ 4 - 184320 * J ^ 3 + 1344 * J ^ 2 - 3168 * J - 15]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (-1152 * J) * hG'
    | linear_combination (196608 * J ^ 4 + 36864 * G * J ^ 2 + 55296 * J ^ 3 + 6912 * G ^ 2 + 10368 * G * J + 153600 * J ^ 2 + 44928 * G + 23760 * J + 67716) * hG'
    | linear_combination (-2097152 * J ^ 6 - 393216 * G * J ^ 4 + 3276800 * J ^ 5 - 73728 * G ^ 2 * J ^ 2 + 614400 * G * J ^ 3 + 6356992 * J ^ 4 + 115200 * G ^ 2 * J + 1019904 * G * J ^ 2 + 1329152 * J ^ 3 + 255744 * G ^ 2 + 518016 * G * J + 2793856 * J ^ 2 + 1195776 * G + 579560 * J + 1397412) * hG'
    | linear_combination (0) * hG'
    | linear_combination (12288 * J ^ 3 + 2304 * G * J + 92160 * J ^ 2 + 17280 * G + 5856 * J + 41904) * hG'
    | linear_combination (-12288 * J ^ 3 - 2304 * G * J + 8064 * J ^ 2 + 1728 * G - 5280 * J + 4968) * hG'
    | linear_combination (0) * hG'
    | linear_combination (12288 * J ^ 3 + 2304 * G * J - 9216 * J ^ 2 - 1728 * G + 5280 * J - 4968) * hG'
    | linear_combination (-12288 * J ^ 3 - 2304 * G * J - 92160 * J ^ 2 - 17280 * G - 4704 * J - 41904) * hG'

theorem t_u {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((uM F K) * (tM i F G N)) ((tM i F G N) * ((uvM i F G N) * (uM F K))) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![-49152 * J ^ 5 + 24576 * J ^ 4 + 25728 * J ^ 3 - 1344 * J ^ 2 - 6816 * J - 12, 134217728 * J ^ 8 + 234881024 * J ^ 7 - 31457280 * J ^ 6 - 142344192 * J ^ 5 - 946176 * J ^ 4 - 1880064 * J ^ 3 + 7648 * J ^ 2 - 5888 * J + 102, -4194304 * J ^ 7 + 2097152 * J ^ 6 + 2654208 * J ^ 5 - 614400 * J ^ 4 - 628224 * J ^ 3 + 2112 * J ^ 2 - 5072 * J + 55; 8064 * J ^ 3 - 576 * J ^ 2 - 1665 * J + 9, -9437184 * J ^ 6 - 52690944 * J ^ 5 - 245760 * J ^ 4 - 970752 * J ^ 3 + 3648 * J ^ 2 - 4368 * J + 39, 688128 * J ^ 5 - 49152 * J ^ 4 - 355584 * J ^ 3 + 384 * J ^ 2 - 2820 * J + 6; 10368 * J ^ 3 - 3456 * J ^ 2 - 783 * J - 27, -14155776 * J ^ 6 - 55640064 * J ^ 5 + 221184 * J ^ 4 - 671232 * J ^ 3 + 9504 * J ^ 2 - 1848 * J + 54, 884736 * J ^ 5 - 319488 * J ^ 4 - 264960 * J ^ 3 + 2496 * J ^ 2 - 2124 * J + 39]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (-12288 * J ^ 4 - 2304 * G * J ^ 2 + 6144 * J ^ 3 + 1152 * G * J + 1056 * J ^ 2 + 2352 * J - 1728) * hG'
    | linear_combination (33554432 * J ^ 7 + 6291456 * G * J ^ 5 + 58720256 * J ^ 6 + 1179648 * G ^ 2 * J ^ 3 + 11010048 * G * J ^ 4 + 6815744 * J ^ 5 + 221184 * G ^ 3 * J + 2064384 * G ^ 2 * J ^ 2 + 4030464 * G * J ^ 3 - 9895936 * J ^ 4 + 387072 * G ^ 3 + 1271808 * G ^ 2 * J + 2961408 * G * J ^ 2 + 2745344 * J ^ 3 + 1458432 * G ^ 2 + 2278080 * G * J - 4799488 * J ^ 2 + 395712 * G + 1203000 * J - 2101248) * hG'
    | linear_combination (-1048576 * J ^ 6 - 196608 * G * J ^ 4 + 524288 * J ^ 5 - 36864 * G ^ 2 * J ^ 2 + 98304 * G * J ^ 3 + 204800 * J ^ 4 + 18432 * G ^ 2 * J - 47616 * G * J ^ 2 + 75776 * J ^ 3 + 6912 * G ^ 2 + 57216 * G * J - 67456 * J ^ 2 + 3456 * G + 33680 * J - 30780) * hG'
    | linear_combination (4032 * J ^ 2 - 288 * J - 864) * hG'
    | linear_combination (-4718592 * J ^ 5 - 884736 * G * J ^ 3 - 26345472 * J ^ 4 - 165888 * G ^ 2 * J - 4939776 * G * J ^ 2 - 2187264 * J ^ 3 - 926208 * G ^ 2 - 797184 * G * J - 12011520 * J ^ 2 - 4413312 * G - 955104 * J - 5257224) * hG'
    | linear_combination (344064 * J ^ 4 + 64512 * G * J ^ 2 - 24576 * J ^ 3 - 4608 * G * J - 27264 * J ^ 2 - 32832 * G - 10560 * J - 77976) * hG'
    | linear_combination (5184 * J ^ 2 - 1728 * J - 432) * hG'
    | linear_combination (-7077888 * J ^ 5 - 1327104 * G * J ^ 3 - 27820032 * J ^ 4 - 248832 * G ^ 2 * J - 5216256 * G * J ^ 2 - 2985984 * J ^ 3 - 981504 * G ^ 2 - 1140480 * G * J - 12506880 * J ^ 2 - 4643136 * G - 1301616 * J - 5491152) * hG'
    | linear_combination (442368 * J ^ 4 + 82944 * G * J ^ 2 - 159744 * J ^ 3 - 29952 * G * J + 61056 * J ^ 2 - 24192 * G - 68640 * J - 57456) * hG'



theorem compat_uv {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    Compat (k m) (uvM i F G N) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  exact Compat.of_witness (C := !![-8 * G - 19, 128 * G ^ 2 + 592 * G + 684, -1536 * G ^ 3 - 1024 * G ^ 2 * J - 13184 * G ^ 2 - 4736 * G * J - 36568 * G - 5472 * J - 33060; 2 * J + 1, -40 * G - 95, -256 * G ^ 2 * J - 1920 * G ^ 2 - 1184 * G * J - 9088 * G - 1368 * J - 10754; -1, 16 * G + 38, -256 * G ^ 2 * J + 192 * G ^ 2 - 1184 * G * J + 928 * G - 1368 * J + 1121]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, uvM, tM, uvA, ρM, uMat, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)


theorem compat_t {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    Compat (k m) (tM i F G N) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  exact Compat.of_witness (C := !![-8 * G - 15, 64 * G ^ 2 + 152 * G, 128 * G ^ 2 + 528 * G + 532; 1, -56 * G - 133, -16 * G - 38; 2 * J + 2, -64 * G - 152, -56 * G - 133]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, tM, uvA, ρM, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)


theorem compat_u {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    Compat (k m) (uM F K) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  exact Compat.of_witness (C := !![2 * J - 1, -32 * G - 72, 64 * G * J - 32 * G + 144 * J - 72; 0, 0, 1; 0, 1, 0]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, uM, uMat, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)


theorem compat_rho {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    Compat (k m) (ρM) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  exact Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, ρM, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)

@[expose] def action {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM i F G N) (tM i F G N) (uM F K) ρM
    (compat_uv h) (compat_t h) (compat_u h) (compat_rho h)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

theorem data (m : ℕ) (hm : 2 ≤ m) :
    Data m (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1))
      (2 ^ m) (2 ^ (m - 1)) (2 ^ (m - 2)) := by
  obtain ⟨hi, hF, -⟩ := Type120.data m (by omega)
  have hdvd : ∀ e : ℕ, (3 : ℤ) ∣ 4 ^ e - 1 := fun e => by
    simpa using sub_one_dvd_pow_sub_one (4 : ℤ) e
  obtain ⟨c, hc⟩ := hdvd m
  have hG : 3 * Type120.GV (m + 1) + 7 = 4 ^ m := by
    have := Int.mul_ediv_cancel' (a := 3) (b := (4 : ℤ) ^ m - 7) ⟨c - 2, by linarith⟩
    simp only [Type120.GV, Nat.add_sub_cancel]
    linarith
  refine ⟨hi, hF, rfl, ?_, ?_, ?_⟩
  · have h' : (2 : ℤ) ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rw [← h']
    ring
  · have h' : (2 : ℤ) ^ (m - 2) * 2 = 2 ^ (m - 1) := by
      rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
    rw [← h']
    ring
  · rw [hG, ← mul_pow]
    norm_num

@[expose] def actionPaper (m : ℕ) (hm : 2 ≤ m) : SigmaFourAction (k m) :=
  action (data m hm)

end Type130


namespace Type131

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 1, m + 1]

@[expose] def ρM : IntMat := ofCols ![1, 0, 0] ![0, 0, 1] ![-2, -1, -1]

@[expose] def uvA (i F N : ℤ) : Fin 3 → ℤ := ![2 * F * i, -5 * i, 2 * i + N]

@[expose] def tM (i F G N : ℤ) : IntMat :=
  ofCols ![4 - i, 2, 4 + N] ![4 * G * i, -7 * i + N, -8 * i] (ρM *ᵥ uvA i F N)

@[expose] def uvM (i F G N : ℤ) : IntMat :=
  ofCols ![-i, 2 + N, -2] (uvA i F N) (ρM *ᵥ (tM i F G N *ᵥ uvA i F N))

@[expose] def uM (F K : ℤ) : IntMat := uMat ![-1 + K, 0, 0] (-4 * F)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

structure Data (m : ℕ) (i F G N K J : ℤ) : Prop where
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hN : N = 2 ^ m
  hK : N = 2 * K
  hJ : K = 2 * J
  hG : 3 * G + 7 = N * N

theorem uv_sq {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((uvM i F G N) * (uvM i F G N)) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 4 (W := !![4718592 * J ^ 5 + 442368 * J ^ 4 + 1511424 * J ^ 3 - 72576 * J ^ 2 + 14112 * J - 594, -201326592 * J ^ 7 - 22020096 * J ^ 6 - 71368704 * J ^ 5 + 147456 * J ^ 4 - 926208 * J ^ 3 + 20160 * J ^ 2 - 2976 * J + 138, 17179869184 * J ^ 10 - 11811160064 * J ^ 9 + 3892314112 * J ^ 8 - 6408896512 * J ^ 7 + 246415360 * J ^ 6 - 138805248 * J ^ 5 + 5169152 * J ^ 4 - 1031680 * J ^ 3 + 42752 * J ^ 2 - 2600 * J + 122; 147456 * J ^ 4 + 1105920 * J ^ 3 - 42624 * J ^ 2 + 8316 * J - 342, -6291456 * J ^ 6 - 47480832 * J ^ 5 - 811008 * J ^ 4 - 382464 * J ^ 3 - 5688 * J ^ 2 + 1206 * J - 3, 536870912 * J ^ 9 + 3623878656 * J ^ 8 - 3141533696 * J ^ 7 + 104202240 * J ^ 6 - 16023552 * J ^ 5 - 2202624 * J ^ 4 - 61184 * J ^ 3 - 1872 * J ^ 2 - 1000 * J + 156; 147456 * J ^ 4 - 110592 * J ^ 3 + 2304 * J ^ 2 - 702 * J + 90, -6291456 * J ^ 6 + 4423680 * J ^ 5 + 221184 * J ^ 4 - 34560 * J ^ 3 - 576 * J ^ 2 - 540 * J - 21, 536870912 * J ^ 9 - 805306368 * J ^ 8 + 293601280 * J ^ 7 - 25165824 * J ^ 6 - 26345472 * J ^ 5 - 589824 * J ^ 4 + 226816 * J ^ 3 - 36600 * J ^ 2 + 4814 * J - 264]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (1179648 * J ^ 4 + 221184 * G * J ^ 2 + 110592 * J ^ 3 + 41472 * G ^ 2 + 20736 * G * J + 893952 * J ^ 2 + 264384 * G + 30240 * J + 394632) * hG'
    | linear_combination (-50331648 * J ^ 6 - 9437184 * G * J ^ 4 - 5505024 * J ^ 5 - 1769472 * G ^ 2 * J ^ 2 - 1032192 * G * J ^ 3 - 39862272 * J ^ 4 - 331776 * G ^ 3 - 193536 * G ^ 2 * J - 11602944 * G * J ^ 2 - 2371584 * J ^ 3 - 2944512 * G ^ 2 - 896256 * G * J - 17671296 * J ^ 2 - 8372160 * G - 1032528 * J - 7719624) * hG'
    | linear_combination (4294967296 * J ^ 9 + 805306368 * G * J ^ 7 - 2952790016 * J ^ 8 + 150994944 * G ^ 2 * J ^ 5 - 553648128 * G * J ^ 6 + 2852126720 * J ^ 7 + 28311552 * G ^ 3 * J ^ 3 - 103809024 * G ^ 2 * J ^ 4 + 887095296 * G * J ^ 5 - 2894069760 * J ^ 6 + 5308416 * G ^ 4 * J - 19464192 * G ^ 3 * J ^ 2 + 232390656 * G ^ 2 * J ^ 3 - 784859136 * G * J ^ 4 + 1309409280 * J ^ 5 - 3981312 * G ^ 4 + 55959552 * G ^ 3 * J - 192577536 * G ^ 2 * J ^ 2 + 633618432 * G * J ^ 3 - 1300856832 * J ^ 4 - 47278080 * G ^ 3 + 220474368 * G ^ 2 * J - 587286528 * G * J ^ 2 + 574158848 * J ^ 3 - 202113792 * G ^ 2 + 384862848 * G * J - 569382784 * J ^ 2 - 373349088 * G + 251205184 * J - 253344024) * hG'
    | linear_combination (73728 * J ^ 3 + 13824 * G * J + 552960 * J ^ 2 + 103680 * G + 10944 * J + 246240) * hG'
    | linear_combination (-3145728 * J ^ 5 - 589824 * G * J ^ 3 - 23740416 * J ^ 4 - 110592 * G ^ 2 * J - 4451328 * G * J ^ 2 - 1781760 * J ^ 3 - 829440 * G ^ 2 - 592128 * G * J - 10577664 * J ^ 2 - 3913920 * G - 782688 * J - 4616352) * hG'
    | linear_combination (268435456 * J ^ 8 + 50331648 * G * J ^ 6 + 1811939328 * J ^ 7 + 9437184 * G ^ 2 * J ^ 4 + 339738624 * G * J ^ 5 - 1453326336 * J ^ 6 + 1769472 * G ^ 3 * J ^ 2 + 63700992 * G ^ 2 * J ^ 3 - 250478592 * G * J ^ 4 + 844824576 * J ^ 5 + 11943936 * G ^ 3 * J - 42835968 * G ^ 2 * J ^ 2 + 307040256 * G * J ^ 3 - 643842048 * J ^ 4 - 9953280 * G ^ 3 + 85459968 * G ^ 2 * J - 230304768 * G * J ^ 2 + 368509440 * J ^ 3 - 69963264 * G ^ 2 + 203521536 * G * J - 281711488 * J ^ 2 - 163938816 * G + 161332752 * J - 128057112) * hG'
    | linear_combination (73728 * J ^ 3 + 13824 * G * J - 55296 * J ^ 2 - 10368 * G + 33408 * J - 24624) * hG'
    | linear_combination (-3145728 * J ^ 5 - 589824 * G * J ^ 3 + 2211840 * J ^ 4 - 110592 * G ^ 2 * J + 414720 * G * J ^ 2 - 1265664 * J ^ 3 + 82944 * G ^ 2 - 495360 * G * J + 950400 * J ^ 2 + 383616 * G - 554016 * J + 443232) * hG'
    | linear_combination (268435456 * J ^ 8 + 50331648 * G * J ^ 6 - 402653184 * J ^ 7 + 9437184 * G ^ 2 * J ^ 4 - 75497472 * G * J ^ 5 + 264241152 * J ^ 6 + 1769472 * G ^ 3 * J ^ 2 - 14155776 * G ^ 2 * J ^ 3 + 71565312 * G * J ^ 4 - 188743680 * J ^ 5 - 2654208 * G ^ 3 * J + 17547264 * G ^ 2 * J ^ 2 - 68419584 * G * J ^ 3 + 102432768 * J ^ 4 + 995328 * G ^ 3 - 19021824 * G ^ 2 * J + 50515968 * G * J ^ 2 - 82870272 * J ^ 3 + 6511104 * G ^ 2 - 45471744 * G * J + 44927744 * J ^ 2 + 14141952 * G - 36274368 * J + 10194984) * hG'

theorem t_sq {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((tM i F G N) * (tM i F G N)) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 2 (W := !![16384 * J ^ 4 + 24576 * J ^ 3 - 1664 * J ^ 2 - 4200 * J - 86, -2097152 * J ^ 5 + 8192 * J ^ 4 + 434176 * J ^ 3 + 2624 * J ^ 2 + 3520 * J + 20, -1572864 * J ^ 5 - 24576 * J ^ 4 + 221184 * J ^ 3 + 11328 * J ^ 2 + 1896 * J + 18; -384 * J ^ 2 - 1170 * J - 12, 135168 * J ^ 3 - 1152 * J ^ 2 + 1218 * J - 9, 61440 * J ^ 3 + 2688 * J ^ 2 + 480 * J + 3; -1536 * J ^ 2 - 2322 * J - 12, 4096 * J ^ 4 + 233472 * J ^ 3 - 1760 * J ^ 2 + 1824 * J - 14, 8192 * J ^ 4 + 141312 * J ^ 3 + 3392 * J ^ 2 + 1230 * J - 10]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (4096 * J ^ 3 + 768 * G * J + 6144 * J ^ 2 + 1152 * G + 1376 * J + 1656) * hG'
    | linear_combination (-524288 * J ^ 4 - 98304 * G * J ^ 2 + 2048 * J ^ 3 - 18432 * G ^ 2 + 384 * G * J - 120832 * J ^ 2 - 65664 * G + 1552 * J - 51984) * hG'
    | linear_combination (-393216 * J ^ 4 - 73728 * G * J ^ 2 - 6144 * J ^ 3 - 13824 * G ^ 2 - 1152 * G * J - 116736 * J ^ 2 - 54144 * G + 144 * J - 50616) * hG'
    | linear_combination (-192 * J - 576) * hG'
    | linear_combination (67584 * J ^ 2 + 12672 * G - 576 * J + 30168) * hG'
    | linear_combination (30720 * J ^ 2 + 5760 * G + 1344 * J + 13680) * hG'
    | linear_combination (-768 * J - 1152) * hG'
    | linear_combination (2048 * J ^ 3 + 384 * G * J + 116736 * J ^ 2 + 21888 * G + 16 * J + 51984) * hG'
    | linear_combination (4096 * J ^ 3 + 768 * G * J + 70656 * J ^ 2 + 13248 * G + 3488 * J + 31536) * hG'

theorem uv_comm_t {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((tM i F G N) * (uvM i F G N)) ((uvM i F G N) * (tM i F G N)) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![3145728 * J ^ 6 + 3342336 * J ^ 5 + 1155072 * J ^ 4 + 849408 * J ^ 3 - 48768 * J ^ 2 + 6432 * J - 342, -268435456 * J ^ 7 - 16777216 * J ^ 6 - 78643200 * J ^ 5 + 3932160 * J ^ 4 - 1032192 * J ^ 3 + 55296 * J ^ 2 - 3608 * J + 184, -134217728 * J ^ 8 - 469762048 * J ^ 7 + 23068672 * J ^ 6 + 72646656 * J ^ 5 - 2383872 * J ^ 4 + 628992 * J ^ 3 + 5504 * J ^ 2 + 256 * J + 200; 98304 * J ^ 5 + 835584 * J ^ 4 + 715776 * J ^ 3 - 15960 * J ^ 2 + 8880 * J - 174, -8388608 * J ^ 6 - 62914560 * J ^ 5 + 1757184 * J ^ 4 - 1277952 * J ^ 3 + 32160 * J ^ 2 - 6198 * J + 140, 2097152 * J ^ 6 - 2457600 * J ^ 5 - 1622016 * J ^ 4 - 326400 * J ^ 3 - 9168 * J ^ 2 - 2292 * J + 79; 98304 * J ^ 5 + 24576 * J ^ 4 - 74496 * J ^ 3 - 8256 * J ^ 2 - 4044 * J - 66, -8388608 * J ^ 6 + 6291456 * J ^ 5 + 24576 * J ^ 4 + 522240 * J ^ 3 - 960 * J ^ 2 + 3588 * J - 13, 6815744 * J ^ 6 + 61243392 * J ^ 5 - 2334720 * J ^ 4 + 853248 * J ^ 3 - 7776 * J ^ 2 + 2982 * J + 31]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (786432 * J ^ 5 + 147456 * G * J ^ 3 + 835584 * J ^ 4 + 27648 * G ^ 2 * J + 156672 * G * J ^ 2 + 632832 * J ^ 3 + 27648 * G ^ 2 + 183168 * G * J + 577920 * J ^ 2 + 171072 * G + 264672 * J + 250344) * hG'
    | linear_combination (-67108864 * J ^ 6 - 12582912 * G * J ^ 4 - 4194304 * J ^ 5 - 2359296 * G ^ 2 * J ^ 2 - 786432 * G * J ^ 3 - 49020928 * J ^ 4 - 442368 * G ^ 3 - 147456 * G ^ 2 * J - 14696448 * G * J ^ 2 - 851968 * J ^ 3 - 3787776 * G ^ 2 - 503808 * G * J - 21704704 * J ^ 2 - 10499328 * G - 358912 * J - 9496656) * hG'
    | linear_combination (-33554432 * J ^ 7 - 6291456 * G * J ^ 5 - 117440512 * J ^ 6 - 1179648 * G ^ 2 * J ^ 3 - 22020096 * G * J ^ 4 - 8912896 * J ^ 5 - 221184 * G ^ 3 * J - 4128768 * G ^ 2 * J ^ 2 - 4423680 * G * J ^ 3 - 33218560 * J ^ 4 - 774144 * G ^ 3 - 1345536 * G ^ 2 * J - 15862272 * G * J ^ 2 - 4495360 * J ^ 3 - 4783104 * G ^ 2 - 2778240 * G * J - 14375872 * J ^ 2 - 9647424 * G - 1965344 * J - 6303744) * hG'
    | linear_combination (49152 * J ^ 4 + 9216 * G * J ^ 2 + 417792 * J ^ 3 + 78336 * G * J + 379392 * J ^ 2 + 69120 * G + 174912 * J + 165888) * hG'
    | linear_combination (-4194304 * J ^ 5 - 786432 * G * J ^ 3 - 31457280 * J ^ 4 - 147456 * G ^ 2 * J - 5898240 * G * J ^ 2 - 956416 * J ^ 3 - 1105920 * G ^ 2 - 523392 * G * J - 14401536 * J ^ 2 - 5282496 * G - 402352 * J - 6307848) * hG'
    | linear_combination (1048576 * J ^ 5 + 196608 * G * J ^ 3 - 1228800 * J ^ 4 + 36864 * G ^ 2 * J - 230400 * G * J ^ 2 - 352256 * J ^ 3 - 41472 * G ^ 2 + 19968 * G * J - 700800 * J ^ 2 - 228096 * G - 158912 * J - 307800) * hG'
    | linear_combination (49152 * J ^ 4 + 9216 * G * J ^ 2 + 12288 * J ^ 3 + 2304 * G * J - 15744 * J ^ 2 - 6912 * G + 1248 * J - 18144) * hG'
    | linear_combination (-4194304 * J ^ 5 - 786432 * G * J ^ 3 + 3145728 * J ^ 4 - 147456 * G ^ 2 * J + 589824 * G * J ^ 2 - 1822720 * J ^ 3 + 110592 * G ^ 2 - 685824 * G * J + 1637376 * J ^ 2 + 565056 * G - 797920 * J + 718200) * hG'
    | linear_combination (3407872 * J ^ 5 + 638976 * G * J ^ 3 + 30621696 * J ^ 4 + 119808 * G ^ 2 * J + 5741568 * G * J ^ 2 + 323584 * J ^ 3 + 1078272 * G ^ 2 + 340224 * G * J + 13823616 * J ^ 2 + 5111424 * G + 137680 * J + 6057504) * hG'

theorem rho_cube {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) (ρM * (ρM * ρM)) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 0 (W := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem u_sq {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((uM F K) * (uM F K)) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 1 (W := !![3 * J - 3, 0, 256 * J ^ 3 - 256 * J ^ 2 - 4 * J + 4; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (64 * J ^ 2 - 64 * J) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem u_rho {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) (ρM * ((uM F K) * (ρM * (uM F K)))) 1 := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 1 (W := !![3 * J - 3, -256 * J ^ 2 + 192 * J + 1, 256 * J ^ 3 - 128 * J ^ 2 - 4 * J + 2; 0, 0, 0; 0, 0, 0]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (-64 * J + 48) * hG'
    | linear_combination (64 * J ^ 2 - 32 * J) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'

theorem uv_rho {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) (ρM * (uvM i F G N)) ((tM i F G N) * ρM) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 2 (W := !![0, 0, -262144 * J ^ 5 + 16384 * J ^ 4 - 96256 * J ^ 3 + 3712 * J ^ 2 - 3040 * J + 10; 0, 0, 8192 * J ^ 4 - 6144 * J ^ 3 - 64 * J ^ 2 - 624 * J - 1; 0, 0, -67584 * J ^ 3 + 1728 * J ^ 2 - 1662 * J + 18]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (-65536 * J ^ 4 - 12288 * G * J ^ 2 + 4096 * J ^ 3 - 2304 * G ^ 2 + 768 * G * J - 52736 * J ^ 2 - 15264 * G + 2720 * J - 23832) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (4096 * J ^ 3 + 768 * G * J - 3072 * J ^ 2 - 576 * G + 1760 * J - 1656) * hG'
    | linear_combination (0) * hG'
    | linear_combination (0) * hG'
    | linear_combination (-33792 * J ^ 2 - 6336 * G + 864 * J - 15624) * hG'

theorem t_rho {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) (ρM * (tM i F G N)) ((tM i F G N) * ((uvM i F G N) * ρM)) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![-24576 * J ^ 4 + 10560 * J ^ 2 + 3456 * J - 78, 134217728 * J ^ 8 + 234881024 * J ^ 7 - 40894464 * J ^ 6 - 142835712 * J ^ 5 + 4939776 * J ^ 4 - 1871616 * J ^ 3 + 38848 * J ^ 2 - 5792 * J - 18, -134217728 * J ^ 8 - 234881024 * J ^ 7 + 40894464 * J ^ 6 + 142049280 * J ^ 5 - 4841472 * J ^ 4 + 2393856 * J ^ 3 - 69568 * J ^ 2 + 9704 * J - 12; 4032 * J ^ 2 + 1674 * J - 36, -9437184 * J ^ 6 - 52690944 * J ^ 5 + 2408448 * J ^ 4 - 827904 * J ^ 3 + 25320 * J ^ 2 - 3252 * J + 48, 9437184 * J ^ 6 + 52690944 * J ^ 5 - 2408448 * J ^ 4 + 1030656 * J ^ 3 - 38568 * J ^ 2 + 4890 * J - 30; 5184 * J ^ 2 + 864 * J, -14155776 * J ^ 6 - 55836672 * J ^ 5 + 2408448 * J ^ 4 - 600576 * J ^ 3 + 13728 * J ^ 2 - 1284 * J - 33, 14155776 * J ^ 6 + 55836672 * J ^ 5 - 2383872 * J ^ 4 + 784896 * J ^ 3 - 29472 * J ^ 2 + 2670 * J - 24]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (-6144 * J ^ 3 - 1152 * G * J - 48 * J + 864) * hG'
    | linear_combination (33554432 * J ^ 7 + 6291456 * G * J ^ 5 + 58720256 * J ^ 6 + 1179648 * G ^ 2 * J ^ 3 + 11010048 * G * J ^ 4 + 4456448 * J ^ 5 + 221184 * G ^ 3 * J + 2064384 * G ^ 2 * J ^ 2 + 3588096 * G * J ^ 3 - 10018816 * J ^ 4 + 387072 * G ^ 3 + 1188864 * G ^ 2 * J + 2938368 * G * J ^ 2 + 3184640 * J ^ 3 + 1458432 * G ^ 2 + 2166912 * G * J - 4851136 * J ^ 2 + 393984 * G + 1402992 * J - 2105352) * hG'
    | linear_combination (-33554432 * J ^ 7 - 6291456 * G * J ^ 5 - 58720256 * J ^ 6 - 1179648 * G ^ 2 * J ^ 3 - 11010048 * G * J ^ 4 - 4456448 * J ^ 5 - 221184 * G ^ 3 * J - 2064384 * G ^ 2 * J ^ 2 - 3588096 * G * J ^ 3 + 9822208 * J ^ 4 - 387072 * G ^ 3 - 1188864 * G ^ 2 * J - 2975232 * G * J ^ 2 - 3160064 * J ^ 3 - 1465344 * G ^ 2 - 2162304 * G * J + 4895680 * J ^ 2 - 401760 * G - 1399920 * J + 2125872) * hG'
    | linear_combination (2016 * J + 864) * hG'
    | linear_combination (-4718592 * J ^ 5 - 884736 * G * J ^ 3 - 26345472 * J ^ 4 - 165888 * G ^ 2 * J - 4939776 * G * J ^ 2 - 860160 * J ^ 3 - 926208 * G ^ 2 - 548352 * G * J - 11940096 * J ^ 2 - 4399488 * G - 363552 * J - 5224392) * hG'
    | linear_combination (4718592 * J ^ 5 + 884736 * G * J ^ 3 + 26345472 * J ^ 4 + 165888 * G ^ 2 * J + 4939776 * G * J ^ 2 + 860160 * J ^ 3 + 926208 * G ^ 2 + 548352 * G * J + 12041472 * J ^ 2 + 4418496 * G + 356928 * J + 5269536) * hG'
    | linear_combination (2592 * J + 432) * hG'
    | linear_combination (-7077888 * J ^ 5 - 1327104 * G * J ^ 3 - 27918336 * J ^ 4 - 248832 * G ^ 2 * J - 5234688 * G * J ^ 2 - 1892352 * J ^ 3 - 981504 * G ^ 2 - 935424 * G * J - 12514560 * J ^ 2 - 4636224 * G - 821040 * J - 5474736) * hG'
    | linear_combination (7077888 * J ^ 5 + 1327104 * G * J ^ 3 + 27918336 * J ^ 4 + 248832 * G ^ 2 * J + 5234688 * G * J ^ 2 + 1904640 * J ^ 3 + 981504 * G ^ 2 + 937728 * G * J + 12606720 * J ^ 2 + 4653504 * G + 818544 * J + 5515776) * hG'

theorem uv_comm_u {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((uM F K) * (uvM i F G N)) ((uvM i F G N) * (uM F K)) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![-4608 * J ^ 2 + 72, 786432 * J ^ 5 + 172032 * J ^ 4 + 274944 * J ^ 3 - 15168 * J ^ 2 + 1992 * J - 75, -8388608 * J ^ 7 + 13107200 * J ^ 6 + 29196288 * J ^ 5 - 1351680 * J ^ 4 + 63744 * J ^ 3 - 12000 * J ^ 2 - 1072 * J - 5; -27 * J, 24576 * J ^ 4 + 184320 * J ^ 3 - 4224 * J ^ 2 + 3114 * J - 48, -24576 * J ^ 4 + 16128 * J ^ 3 + 192 * J ^ 2 + 1908 * J + 3; 27, 24576 * J ^ 4 - 18432 * J ^ 3 - 192 * J ^ 2 - 1872 * J - 3, -24576 * J ^ 4 - 184320 * J ^ 3 + 6528 * J ^ 2 - 3114 * J + 12]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (-1152 * J) * hG'
    | linear_combination (196608 * J ^ 4 + 36864 * G * J ^ 2 + 43008 * J ^ 3 + 6912 * G ^ 2 + 8064 * G * J + 154752 * J ^ 2 + 44928 * G + 15024 * J + 67716) * hG'
    | linear_combination (-2097152 * J ^ 6 - 393216 * G * J ^ 4 + 3276800 * J ^ 5 - 73728 * G ^ 2 * J ^ 2 + 614400 * G * J ^ 3 + 6381568 * J ^ 4 + 115200 * G ^ 2 * J + 1024512 * G * J ^ 2 + 1095680 * J ^ 3 + 255744 * G ^ 2 + 474240 * G * J + 2807872 * J ^ 2 + 1195776 * G + 476360 * J + 1397412) * hG'
    | linear_combination (0) * hG'
    | linear_combination (12288 * J ^ 3 + 2304 * G * J + 92160 * J ^ 2 + 17280 * G + 3264 * J + 41904) * hG'
    | linear_combination (-12288 * J ^ 3 - 2304 * G * J + 8064 * J ^ 2 + 1728 * G - 5280 * J + 4968) * hG'
    | linear_combination (0) * hG'
    | linear_combination (12288 * J ^ 3 + 2304 * G * J - 9216 * J ^ 2 - 1728 * G + 5280 * J - 4968) * hG'
    | linear_combination (-12288 * J ^ 3 - 2304 * G * J - 92160 * J ^ 2 - 17280 * G - 2112 * J - 41904) * hG'

theorem t_u {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    MatEq (k m) ((uM F K) * (tM i F G N)) ((tM i F G N) * ((uvM i F G N) * (uM F K))) := by
  obtain ⟨hi, hF, hN, hK, hJ, hG⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  have hG' : 3 * G + 7 = 16 * J * J := by rw [hG]; ring
  have h0 : (2 : ℤ) ^ m = 4 * J := by rw [← hN]; ring
  have h1 : (2 : ℤ) ^ (m + 1) = 8 * J := by rw [pow_succ, h0]; ring
  refine MatEq.of_three_pow_witness (k := k m) 3 (W := !![-49152 * J ^ 5 + 24576 * J ^ 4 + 25728 * J ^ 3 - 1344 * J ^ 2 - 7032 * J + 96, 134217728 * J ^ 8 + 234881024 * J ^ 7 - 38797312 * J ^ 6 - 142835712 * J ^ 5 + 3624960 * J ^ 4 - 1834752 * J ^ 3 + 50464 * J ^ 2 - 5504 * J - 8, -4194304 * J ^ 7 + 2097152 * J ^ 6 + 2654208 * J ^ 5 - 663552 * J ^ 4 - 651264 * J ^ 3 + 25536 * J ^ 2 - 4604 * J - 29; 8064 * J ^ 3 - 684 * J ^ 2 - 1719 * J + 63, -9437184 * J ^ 6 - 52690944 * J ^ 5 + 2064384 * J ^ 4 - 970752 * J ^ 3 + 32616 * J ^ 2 - 4476 * J + 18, 688128 * J ^ 5 - 58368 * J ^ 4 - 360192 * J ^ 3 + 10320 * J ^ 2 - 2694 * J - 39; 10368 * J ^ 3 - 3456 * J ^ 2 - 837 * J, -14155776 * J ^ 6 - 55836672 * J ^ 5 + 1966080 * J ^ 4 - 674304 * J ^ 3 + 19488 * J ^ 2 - 1860 * J - 15, 884736 * J ^ 5 - 319488 * J ^ 4 - 269568 * J ^ 3 + 9984 * J ^ 2 - 1998 * J + 30]) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k, h0, h1, uvM, tM, uvA, ρM, uM, uMat, ofCols_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.mul_one,
      Matrix.one_mul] <;>
    first

    | linear_combination (-12288 * J ^ 4 - 2304 * G * J ^ 2 + 6144 * J ^ 3 + 1152 * G * J + 1056 * J ^ 2 + 2352 * J - 1728) * hG'
    | linear_combination (33554432 * J ^ 7 + 6291456 * G * J ^ 5 + 58720256 * J ^ 6 + 1179648 * G ^ 2 * J ^ 3 + 11010048 * G * J ^ 4 + 4980736 * J ^ 5 + 221184 * G ^ 3 * J + 2064384 * G ^ 2 * J ^ 2 + 3686400 * G * J ^ 3 - 10018816 * J ^ 4 + 387072 * G ^ 3 + 1207296 * G ^ 2 * J + 2938368 * G * J ^ 2 + 3085312 * J ^ 3 + 1458432 * G ^ 2 + 2191296 * G * J - 4841920 * J ^ 2 + 395712 * G + 1362440 * J - 2101248) * hG'
    | linear_combination (-1048576 * J ^ 6 - 196608 * G * J ^ 4 + 524288 * J ^ 5 - 36864 * G ^ 2 * J ^ 2 + 98304 * G * J ^ 3 + 204800 * J ^ 4 + 18432 * G ^ 2 * J - 47616 * G * J ^ 2 + 63488 * J ^ 3 + 6912 * G ^ 2 + 54912 * G * J - 73216 * J ^ 2 + 3456 * G + 34160 * J - 30780) * hG'
    | linear_combination (4032 * J ^ 2 - 288 * J - 864) * hG'
    | linear_combination (-4718592 * J ^ 5 - 884736 * G * J ^ 3 - 26345472 * J ^ 4 - 165888 * G ^ 2 * J - 4939776 * G * J ^ 2 - 1032192 * J ^ 3 - 926208 * G ^ 2 - 580608 * G * J - 12011520 * J ^ 2 - 4413312 * G - 435168 * J - 5257224) * hG'
    | linear_combination (344064 * J ^ 4 + 64512 * G * J ^ 2 - 29184 * J ^ 3 - 4608 * G * J - 29568 * J ^ 2 - 32832 * G - 5664 * J - 77976) * hG'
    | linear_combination (5184 * J ^ 2 - 1728 * J - 432) * hG'
    | linear_combination (-7077888 * J ^ 5 - 1327104 * G * J ^ 3 - 27918336 * J ^ 4 - 248832 * G ^ 2 * J - 5234688 * G * J ^ 2 - 2113536 * J ^ 3 - 981504 * G ^ 2 - 976896 * G * J - 12551424 * J ^ 2 - 4643136 * G - 914928 * J - 5491152) * hG'
    | linear_combination (442368 * J ^ 4 + 82944 * G * J ^ 2 - 159744 * J ^ 3 - 29952 * G * J + 58752 * J ^ 2 - 24192 * G - 64896 * J - 57456) * hG'



theorem compat_uv {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    Compat (k m) (uvM i F G N) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  exact Compat.of_witness (C := !![-8 * G - 19, 128 * G ^ 2 + 592 * G + 684, -1536 * G ^ 3 - 512 * G ^ 2 * J - 13184 * G ^ 2 - 1728 * G * J - 36568 * G - 1216 * J - 33060; 2 * J + 1, -40 * G - 95, -256 * G ^ 2 * J - 1920 * G ^ 2 - 896 * G * J + 16 * J ^ 2 - 9088 * G - 684 * J - 10754; -1, 16 * G + 4 * J + 38, -256 * G ^ 2 * J + 192 * G ^ 2 - 1184 * G * J + 928 * G - 1368 * J + 1121]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, uvM, tM, uvA, ρM, uMat, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)


theorem compat_t {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    Compat (k m) (tM i F G N) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  exact Compat.of_witness (C := !![-8 * G - 15, 64 * G ^ 2 + 152 * G, 128 * G ^ 2 + 528 * G - 16 * J + 532; 1, -56 * G + 4 * J - 133, -16 * G - 4 * J - 38; 2 * J + 2, -64 * G - 152, -56 * G - 4 * J - 133]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, tM, uvA, ρM, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)


theorem compat_u {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    Compat (k m) (uM F K) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  exact Compat.of_witness (C := !![2 * J - 1, -32 * G - 72, 64 * G * J - 32 * G + 144 * J - 72; 0, 0, 1; 0, 1, 0]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, uM, uMat, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)


theorem compat_rho {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    Compat (k m) (ρM) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := h
  subst hi
  subst hF
  subst hK
  subst hJ
  exact Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, ρM, ofCols_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.mulVec, dotProduct] <;> ring1)

@[expose] def action {m : ℕ} {i F G N K J : ℤ} (h : Data m i F G N K J) :
    SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM i F G N) (tM i F G N) (uM F K) ρM
    (compat_uv h) (compat_t h) (compat_u h) (compat_rho h)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

theorem data (m : ℕ) (hm : 2 ≤ m) :
    Data m (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1))
      (2 ^ m) (2 ^ (m - 1)) (2 ^ (m - 2)) := by
  obtain ⟨hi, hF, -⟩ := Type120.data m (by omega)
  have hdvd : ∀ e : ℕ, (3 : ℤ) ∣ 4 ^ e - 1 := fun e => by
    simpa using sub_one_dvd_pow_sub_one (4 : ℤ) e
  obtain ⟨c, hc⟩ := hdvd m
  have hG : 3 * Type120.GV (m + 1) + 7 = 4 ^ m := by
    have := Int.mul_ediv_cancel' (a := 3) (b := (4 : ℤ) ^ m - 7) ⟨c - 2, by linarith⟩
    simp only [Type120.GV, Nat.add_sub_cancel]
    linarith
  refine ⟨hi, hF, rfl, ?_, ?_, ?_⟩
  · have h' : (2 : ℤ) ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rw [← h']
    ring
  · have h' : (2 : ℤ) ^ (m - 2) * 2 = 2 ^ (m - 1) := by
      rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
    rw [← h']
    ring
  · rw [hG, ← mul_pow]
    norm_num

@[expose] def actionPaper (m : ℕ) (hm : 2 ≤ m) : SigmaFourAction (k m) :=
  action (data m hm)

end Type131


end CFSG.CGT.Stroth77
