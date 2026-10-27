module

public import CFSG.CGT.Stroth77.Types120
public import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem MatEq.of_three_pow_mul_witness {k : Fin 3 → ℕ} {A B W : IntMat} (d : ℕ)
    (h : ∀ i j, 3 ^ d * (A i j - B i j) = 2 ^ k i * W i j) : MatEq k A B := by
  intro i j
  have h3 : IsCoprime ((2 : ℤ) ^ k i) ((3 : ℤ) ^ d) := by
    have hodd : Odd ((3 : ℤ) ^ d) := (show Odd (3 : ℤ) by exact ⟨1, by norm_num⟩).pow
    exact hodd.isCoprime_two.symm.pow_left
  have hdvd : (2 : ℤ) ^ k i ∣ A i j - B i j := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one ⟨W i j, h i j⟩ ?_
    exact Int.isCoprime_iff_gcd_eq_one.mp h3
  rw [Int.modEq_iff_dvd]
  simpa only [neg_sub] using dvd_neg.mpr hdvd

namespace Type32x

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m, m]

structure Data (m : ℕ) (i F G N : ℤ) : Prop where
  hm : 2 ≤ m
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hG : 3 * G + 7 = N * N
  hN : N = 2 ^ (m - 1)

theorem dvd_three_mul_add_seven {m : ℕ} {i F G N : ℤ} (h : Data m i F G N) :
    ∀ r : Fin 3, (2 : ℤ) ^ Type32x.k m r ∣ 3 * G + 7 := by
  obtain ⟨hm, -, -, hG, hN⟩ := h
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  subst hN
  intro r
  fin_cases r <;> simp [Type32x.k]
  all_goals
    rw [hG, ← pow_add]
    refine pow_dvd_pow 2 ?_
    change s + 2 ≤ (s + 1) + (s + 1)
    exact Nat.succ_le_succ (Nat.le_add_right (s + 1) s)

theorem data (m : ℕ) (hm : 2 ≤ m) :
    Data m (Type120.iV m) (Type120.FV m) (Type120.GV m) (2 ^ (m - 1)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  have hdvd : ∀ e : ℕ, (3 : ℤ) ∣ 4 ^ e - 1 := fun e => by
    simpa using sub_one_dvd_pow_sub_one (4 : ℤ) e
  obtain ⟨c, hc⟩ := hdvd (s + 1)
  have hG : 3 * Type120.GV (s + 2) + 7 = 4 ^ (s + 1) := by
    have h := Int.mul_ediv_cancel' (a := 3) (b := (4 : ℤ) ^ (s + 1) - 7)
      ⟨c - 2, by linarith⟩
    change 3 * Type120.GV (s + 2) = 4 ^ (s + 1) - 7 at h
    linarith
  have hF : Type120.FV (s + 2) = 4 * Type120.GV (s + 2) + 9 := by
    have h := Int.mul_ediv_cancel' (hdvd (s + 2))
    change 3 * Type120.FV (s + 2) = 4 ^ (s + 2) - 1 at h
    rw [show (4 : ℤ) ^ (s + 2) = 4 * 4 ^ (s + 1) by rw [pow_succ]; ring] at h
    linarith
  have hi : Type120.iV (s + 2) = 8 * Type120.GV (s + 2) + 19 := by
    have hpow : (2 : ℤ) ^ (2 * (s + 2) + 1) = 8 * 4 ^ (s + 1) := by
      rw [show 2 * (s + 2) + 1 = 2 * (s + 1) + 3 by ring, pow_add]
      rw [show (2 : ℤ) ^ (2 * (s + 1)) = 4 ^ (s + 1) by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]]
      norm_num
      ring
    have h := Int.mul_ediv_cancel' (a := 3) (b := (2 : ℤ) ^ (2 * (s + 2) + 1) + 1)
      ⟨8 * c + 3, by
        rw [hpow]
        have hc' : (4 : ℤ) ^ (s + 1) = 3 * c + 1 := by linarith
        rw [hc']
        ring⟩
    change 3 * Type120.iV (s + 2) = 2 ^ (2 * (s + 2) + 1) + 1 at h
    rw [hpow] at h
    linarith
  have hNN : (2 : ℤ) ^ (s + 2 - 1) * 2 ^ (s + 2 - 1) = 4 ^ (s + 1) := by
    change (2 : ℤ) ^ (s + 1) * 2 ^ (s + 1) = 4 ^ (s + 1)
    rw [← pow_add]
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    ring
  exact ⟨Nat.le_add_left 2 s, hi, hF, by rw [hNN]; exact hG, by simp⟩

end Type32x

namespace Type320

abbrev k := Type32x.k

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-4, -1, -1]

@[expose] def uvA (i F : ℤ) : Fin 3 → ℤ := ![4 * F * i, -5 * i, 2 * i]

@[expose] def tM (i F G : ℤ) : IntMat :=
  ofCols ![4 - i, 1, 2] ![8 * G * i, -7 * i, -8 * i] (ρM *ᵥ uvA i F)

@[expose] def uvM (i F G : ℤ) : IntMat :=
  ofCols ![-i, 1, -1] (uvA i F) (ρM *ᵥ (tM i F G *ᵥ uvA i F))

@[expose] def uM (F : ℤ) : IntMat := uMat ![-1, 0, 0] (-8 * F)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (m : ℕ) (i F G : ℤ) : Compat (k m) (uvM i F G) := by
  intro r c
  fin_cases r <;> fin_cases c <;> simp [k, Type32x.k, dvd_mul_left]

theorem compat_t (m : ℕ) (i F G : ℤ) : Compat (k m) (tM i F G) := by
  intro r c
  fin_cases r <;> fin_cases c <;> simp [k, Type32x.k, dvd_mul_left]

theorem compat_u (m : ℕ) (i F G : ℤ) : Compat (k m) (uM F) := by
  intro r c
  fin_cases r <;> fin_cases c <;> simp [k, Type32x.k, dvd_mul_left]

theorem compat_rho (m : ℕ) (i F G : ℤ) : Compat (k m) ρM := by
  intro r c
  fin_cases r <;> fin_cases c <;> simp [k, Type32x.k, dvd_mul_left]

theorem uv_sq {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((uvM i F G) * (uvM i F G)) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![512*G^2 + 3264*G + 4872, -8192*G^3 - 72704*G^2 - 206720*G - 190608, -98304*G^4 - 1167360*G^3 - 4990464*G^2 - 9218496*G - 6255408; 640*G + 1520, -10240*G^2 - 48320*G - 56992, -122880*G^3 - 863744*G^2 - 2023936*G - 1580952; -64*G - 152, 1024*G^2 + 4736*G + 5472, 12288*G^3 + 80384*G^2 + 174592*G + 125864]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem t_sq {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((tM i F G) * (tM i F G)) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![128*G + 184, -4096*G^2 - 14592*G - 11552, -3072*G^2 - 12032*G - 11248; -32, 1408*G + 3352, 640*G + 1520; -64, 2432*G + 5776, 1472*G + 3504]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem uv_comm_t {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((tM i F G) * (uvM i F G)) ((uvM i F G) * (tM i F G)) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![1024*G^2 + 6336*G + 9272, -32768*G^3 - 280576*G^2 - 777728*G - 703456, -57344*G^3 - 354304*G^2 - 714624*G - 466944; 1280*G + 3072, -40960*G^2 - 195648*G - 233624, -1536*G^2 - 8448*G - 11400; -128*G - 336, 4096*G^2 + 20928*G + 26600, 39936*G^2 + 189312*G + 224352]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem rho_cube {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := 0) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem u_sq {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((uM F) * (uM F)) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := 0) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem u_rho {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) (ρM * ((uM F) * (ρM * (uM F)))) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![0, 32, 0; 0, 0, 0; 0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem uv_rho {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) (ρM * (uvM i F G)) ((tM i F G) * ρM) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![0, 0, -512*G^2 - 3392*G - 5296; 0, 0, -64*G - 184; 0, 0, -704*G - 1736]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem t_rho {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) (ρM * (tM i F G)) ((tM i F G) * ((uvM i F G) * ρM)) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![32, 28672*G^3 + 108032*G^2 + 29184*G - 155952, -28672*G^3 - 108544*G^2 - 29760*G + 157472; 16, -34304*G^2 - 162944*G - 193496, 34304*G^2 + 163648*G + 195168; 8, -36352*G^2 - 171712*G - 202768, 36352*G^2 + 172352*G + 204288]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem uv_comm_u {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((uM F) * (uvM i F G)) ((uvM i F G) * (uM F)) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![0, 512*G^2 + 3328*G + 5016, 18944*G^2 + 88576*G + 103512; 0, 640*G + 1552, 64*G + 184; 0, -64*G - 184, -640*G - 1552]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem t_u {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((uM F) * (tM i F G)) ((tM i F G) * ((uvM i F G) * (uM F))) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  have hs := Type32x.dvd_three_mul_add_seven ⟨hm, hi, hF, hG, hN⟩
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![-64, 28672*G^3 + 108032*G^2 + 29312*G - 155648, 512*G^2 + 256*G - 2280; -16, -34304*G^2 - 163456*G - 194712, -1216*G - 2888; -8, -36352*G^2 - 171968*G - 203376, -896*G - 2128]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

@[expose] def action {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM i F G) (tM i F G) (uM F) ρM
    (compat_uv m i F G) (compat_t m i F G) (compat_u m i F G) (compat_rho m i F G)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

@[expose] def actionPaper (m : ℕ) (hm : 3 ≤ m) : SigmaFourAction (k m) :=
  action (Type32x.data m (Nat.le_trans (by norm_num) hm))

theorem uv_a {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    (action h).φuv Torus.a = (4*F*i : ℤ) • Torus.c + (-5*i : ℤ) • Torus.a + (2*i : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM i F G) (compat_uv m i F G) 1 (4*F*i) (-5*i) (2*i) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    (action h).φuv Torus.b = (4*F*i^2 - 16*F*i - 40*G*i^2 - 120*i^2 : ℤ) • Torus.c +
      (-8*F*i - 26*i^2 : ℤ) • Torus.a + (-4*F*i + 5*i^2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM i F G) (compat_uv m i F G) 2 (4*F*i^2 - 16*F*i - 40*G*i^2 - 120*i^2) (-8*F*i - 26*i^2) (-4*F*i + 5*i^2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    (action h).φu Torus.c = (-1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (uM F) (compat_u m i F G) 0 (-1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end Type320

namespace Type330

abbrev k := Type32x.k

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-4, -1, -1]

@[expose] def uvA (i F : ℤ) : Fin 3 → ℤ := ![4 * F * i, -5 * i, 2 * i]

@[expose] def tM (i F G N : ℤ) : IntMat :=
  ofCols ![4 - i, 1, 2 + N] ![8 * G * i, -7 * i, -8 * i] (ρM *ᵥ uvA i F)

@[expose] def uvM (i F G N : ℤ) : IntMat :=
  ofCols ![-i, 1 + N, -1] (uvA i F) (ρM *ᵥ (tM i F G N *ᵥ uvA i F))

@[expose] def uM (F N : ℤ) : IntMat := uMat ![N - 1, 0, 0] (-8 * F)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (m : ℕ) (i F G N : ℤ) : Compat (k m) (uvM i F G N) := by
  intro r c
  fin_cases r <;> fin_cases c <;> simp [k, Type32x.k, dvd_mul_left]

theorem compat_t (m : ℕ) (i F G N : ℤ) : Compat (k m) (tM i F G N) := by
  intro r c
  fin_cases r <;> fin_cases c <;> simp [k, Type32x.k, dvd_mul_left]

theorem compat_u (m : ℕ) (i F G N : ℤ) : Compat (k m) (uM F N) := by
  intro r c
  fin_cases r <;> fin_cases c <;> simp [k, Type32x.k, dvd_mul_left]

theorem compat_rho (m : ℕ) (i F G N : ℤ) : Compat (k m) ρM := by
  intro r c
  fin_cases r <;> fin_cases c <;> simp [k, Type32x.k, dvd_mul_left]

theorem uv_sq {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((uvM i F G N) * (uvM i F G N)) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![73728*n^5 + 46080*n^4 + 94464*n^3 - 1440*n^2 + 3528*n - 90, -1572864*n^7 - 786432*n^6 - 2211840*n^5 - 133632*n^3 + 2304*n^2 - 2064*n + 48, 33554432*n^10 - 8388608*n^9 + 24117248*n^8 - 49020928*n^7 - 360448*n^6 - 4399104*n^5 - 72704*n^4 - 132352*n^3 - 704*n^2 - 1328*n + 16; 9216*n^4 + 69120*n^3 - 2880*n^2 + 2160*n - 99, -196608*n^6 - 1474560*n^5 + 9216*n^4 - 57600*n^3 + 288*n^2 + 288*n - 6, 4194304*n^9 + 28311552*n^8 - 23855104*n^7 + 638976*n^6 - 602112*n^5 - 294912*n^4 - 15616*n^3 - 9936*n^2 - 632*n - 30; 9216*n^4 - 6912*n^3 + 576*n^2 - 216*n + 9, -196608*n^6 + 147456*n^5 - 4608*n^3 + 576*n^2 - 288*n + 12, 4194304*n^9 - 6291456*n^8 + 2097152*n^7 - 786432*n^6 - 823296*n^5 + 55296*n^4 + 18944*n^3 + 1536*n^2 + 2104*n - 24]) 4 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (73728*n^4 + 55296*G*n^2 + 46080*n^3 + 41472*G^2 + 34560*G*n + 223488*n^2 + 264384*G + 79200*n + 394632) * hG'
    | linear_combination (-1572864*n^6 - 1179648*G*n^4 - 786432*n^5 - 884736*G^2*n^2 - 589824*G*n^3 - 4964352*n^4 - 663552*G^3 - 442368*G^2*n - 5787648*G*n^2 - 1376256*n^3 - 5889024*G^2 - 2064384*G*n - 8821248*n^2 - 16744320*G - 2406144*n - 15439248) * hG'
    | linear_combination (33554432*n^9 + 25165824*G*n^7 - 8388608*n^8 + 18874368*G^2*n^5 - 6291456*G*n^6 + 82837504*n^7 + 14155776*G^3*n^3 - 4718592*G^2*n^4 + 106168320*G*n^5 - 63700992*n^6 + 10616832*G^4*n - 3538944*G^3*n^2 + 112656384*G^2*n^3 - 58785792*G*n^4 + 144605184*n^5 - 7962624*G^4 + 109264896*G^3*n - 52346880*G^2*n^2 + 294248448*G*n^3 - 115875840*n^4 - 94556160*G^3 + 417835008*G^2*n - 189782016*G*n^2 + 252986368*n^3 - 404227584*G^2 + 704674560*G*n - 202915072*n^2 - 746698176*G + 442725440*n - 506688048) * hG'
    | linear_combination (9216*n^3 + 6912*G*n + 69120*n^2 + 51840*G + 13248*n + 123120) * hG'
    | linear_combination (-196608*n^5 - 147456*G*n^3 - 1474560*n^4 - 110592*G^2*n - 1105920*G*n^2 - 334848*n^3 - 829440*G^2 - 509184*G*n - 2638080*n^2 - 3913920*G - 585696*n - 4616352) * hG'
    | linear_combination (4194304*n^8 + 3145728*G*n^6 + 28311552*n^7 + 2359296*G^2*n^4 + 21233664*G*n^5 - 16515072*n^6 + 1769472*G^3*n^2 + 15925248*G^2*n^3 - 6881280*G*n^4 + 50184192*n^5 + 11943936*G^3*n - 1032192*G^2*n^2 + 74797056*G*n^3 - 29503488*n^4 - 9953280*G^3 + 83966976*G^2*n - 34169856*G*n^2 + 87527424*n^3 - 69963264*G^2 + 196540416*G*n - 51646720*n^2 - 163938816*G + 153163056*n - 128057112) * hG'
    | linear_combination (9216*n^3 + 6912*G*n - 6912*n^2 - 5184*G + 16704*n - 12312) * hG'
    | linear_combination (-196608*n^5 - 147456*G*n^3 + 147456*n^4 - 110592*G^2*n + 110592*G*n^2 - 344064*n^3 + 82944*G^2 - 516096*G*n + 253440*n^2 + 383616*G - 601536*n + 443232) * hG'
    | linear_combination (4194304*n^8 + 3145728*G*n^6 - 6291456*n^7 + 2359296*G^2*n^4 - 4718592*G*n^5 + 9437184*n^6 + 1769472*G^3*n^2 - 3538944*G^2*n^3 + 12582912*G*n^4 - 11796480*n^5 - 2654208*G^3*n + 13565952*G^2*n^2 - 17104896*G*n^3 + 15691776*n^4 + 995328*G^3 - 19021824*G^2*n + 33788928*G*n^2 - 20588544*n^3 + 6511104*G^2 - 45374976*G*n + 27479552*n^2 + 14141952*G - 36028416*n + 10194984) * hG'
    | ring1

theorem t_sq {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((tM i F G N) * (tM i F G N)) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![1024*n^4 + 1536*n^3 - 416*n^2 - 1032*n - 14, -65536*n^5 + 54272*n^3 + 1760*n, -49152*n^5 + 27648*n^3 + 912*n; -96*n^2 - 288*n - 3, 16896*n^3 + 600*n, 7680*n^3 + 240*n; -384*n^2 - 576*n + 6, 512*n^4 + 29184*n^3 - 880*n^2 + 912*n - 28, 1024*n^4 + 17664*n^3 - 416*n^2 + 624*n - 14]) 2 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (1024*n^3 + 768*G*n + 1536*n^2 + 1152*G + 1376*n + 1656) * hG'
    | linear_combination (-65536*n^4 - 49152*G*n^2 - 36864*G^2 - 60416*n^2 - 131328*G - 103968) * hG'
    | linear_combination (-49152*n^4 - 36864*G*n^2 - 27648*G^2 - 58368*n^2 - 108288*G - 101232) * hG'
    | linear_combination (-96*n - 288) * hG'
    | linear_combination (16896*n^2 + 12672*G + 30168) * hG'
    | linear_combination (7680*n^2 + 5760*G + 13680) * hG'
    | linear_combination (-384*n - 576) * hG'
    | linear_combination (512*n^3 + 384*G*n + 29184*n^2 + 21888*G + 16*n + 51984) * hG'
    | linear_combination (1024*n^3 + 768*G*n + 17664*n^2 + 13248*G + 1376*n + 31536) * hG'
    | ring1

theorem uv_comm_t {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((tM i F G N) * (uvM i F G N)) ((uvM i F G N) * (tM i F G N)) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![49152*n^6 + 73728*n^5 + 84480*n^4 + 55296*n^3 - 1056*n^2 + 1656*n - 114, -2097152*n^7 - 1048576*n^6 - 2457600*n^5 - 129024*n^3 + 3072*n^2 - 1696*n + 64, -1048576*n^8 - 3670016*n^7 + 131072*n^6 + 2260992*n^5 - 46080*n^4 + 78336*n^3 + 1216*n^2 + 128*n + 88; 6144*n^5 + 52224*n^4 + 45888*n^3 + 1248*n^2 + 2292*n - 66, -262144*n^6 - 1966080*n^5 - 1536*n^4 - 162048*n^3 + 3408*n^2 - 3144*n + 100, 65536*n^6 - 73728*n^5 - 15360*n^4 - 46080*n^3 + 1440*n^2 - 1368*n + 62; 6144*n^5 + 1536*n^4 - 4800*n^3 - 2064*n^2 - 1020*n - 66, -262144*n^6 + 196608*n^5 + 3072*n^4 + 65280*n^3 + 672*n^2 + 1848*n + 10, 212992*n^6 + 1892352*n^5 - 82944*n^4 + 106752*n^3 - 2352*n^2 + 1488*n + 14]) 3 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (49152*n^5 + 36864*G*n^3 + 73728*n^4 + 27648*G^2*n + 55296*G*n^2 + 170496*n^3 + 27648*G^2 + 192384*G*n + 184320*n^2 + 171072*G + 297312*n + 250344) * hG'
    | linear_combination (-2097152*n^6 - 1572864*G*n^4 - 1048576*n^5 - 1179648*G^2*n^2 - 786432*G*n^3 - 6127616*n^4 - 884736*G^3 - 589824*G^2*n - 7348224*G*n^2 - 1835008*n^3 - 7575552*G^2 - 2752512*G*n - 10852352*n^2 - 20998656*G - 3208192*n - 18993312) * hG'
    | linear_combination (-1048576*n^7 - 786432*G*n^5 - 3670016*n^6 - 589824*G^2*n^3 - 2752512*G*n^4 - 1703936*n^5 - 442368*G^3*n - 2064384*G^2*n^2 - 2654208*G*n^3 - 4161536*n^4 - 1548288*G^3 - 3022848*G^2*n - 7938048*G*n^2 - 3027968*n^3 - 9566208*G^2 - 6915840*G*n - 7204352*n^2 - 19294848*G - 5297728*n - 12607488) * hG'
    | linear_combination (6144*n^4 + 4608*G*n^2 + 52224*n^3 + 39168*G*n + 56640*n^2 + 34560*G + 92640*n + 82944) * hG'
    | linear_combination (-262144*n^5 - 196608*G*n^3 - 1966080*n^4 - 147456*G^2*n - 1474560*G*n^2 - 460288*n^3 - 1105920*G^2 - 689280*G*n - 3602688*n^2 - 5282496*G - 802096*n - 6307848) * hG'
    | linear_combination (65536*n^5 + 49152*G*n^3 - 73728*n^4 + 36864*G^2*n - 55296*G*n^2 + 99328*n^3 - 41472*G^2 + 160512*G*n - 175104*n^2 - 228096*G + 175264*n - 307800) * hG'
    | linear_combination (6144*n^4 + 4608*G*n^2 + 1536*n^3 + 1152*G*n + 5952*n^2 - 3456*G + 624*n - 9072) * hG'
    | linear_combination (-262144*n^5 - 196608*G*n^3 + 196608*n^4 - 147456*G^2*n + 147456*G*n^2 - 455680*n^3 + 110592*G^2 - 685824*G*n + 409344*n^2 + 565056*G - 796768*n + 718200) * hG'
    | linear_combination (212992*n^5 + 159744*G*n^3 + 1892352*n^4 + 119808*G^2*n + 1419264*G*n^2 + 289792*n^3 + 1078272*G^2 + 496896*G*n + 3418368*n^2 + 5111424*G + 504784*n + 6057504) * hG'
    | ring1

theorem rho_cube {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := 0) 0 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | ring1

theorem u_sq {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((uM F N) * (uM F N)) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![3*n - 3, 0, 128*n^3 - 128*n^2 - 8*n + 8; 0, 0, 0; 0, 0, 0]) 1 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (128*n^2 - 128*n) * hG'
    | ring1

theorem u_rho {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) (ρM * ((uM F N) * (ρM * (uM F N)))) (1) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![3*n - 3, -128*n^2 + 96*n + 2, 128*n^3 - 64*n^2 - 8*n + 4; 0, 0, 0; 0, 0, 0]) 1 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (-128*n + 96) * hG'
    | linear_combination (128*n^2 - 64*n) * hG'
    | ring1

theorem uv_rho {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) (ρM * (uvM i F G N)) ((tM i F G N) * ρM) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![0, 0, -8192*n^5 - 12032*n^3 - 1520*n; 0, 0, 1024*n^4 - 768*n^3 - 32*n^2 - 312*n - 2; 0, 0, -8448*n^3 - 840*n + 18]) 2 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (-8192*n^4 - 6144*G*n^2 - 4608*G^2 - 26368*n^2 - 30528*G - 47664) * hG'
    | linear_combination (1024*n^3 + 768*G*n - 768*n^2 - 576*G + 1760*n - 1656) * hG'
    | linear_combination (-8448*n^2 - 6336*G - 15624) * hG'
    | ring1

theorem t_rho {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) (ρM * (tM i F G N)) ((tM i F G N) * ((uvM i F G N) * ρM)) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![-1536*n^4 + 2640*n^2 + 864*n + 30, 1048576*n^8 + 1835008*n^7 - 1048576*n^6 - 4448256*n^5 + 46080*n^4 - 239616*n^3 + 1472*n^2 - 3088*n - 32, -1048576*n^8 - 1835008*n^7 + 1048576*n^6 + 4423680*n^5 - 39936*n^4 + 304896*n^3 - 12032*n^2 + 5152*n - 304; 1008*n^2 + 432*n + 18, -294912*n^6 - 1646592*n^5 + 12288*n^4 - 102912*n^3 + 480*n^2 - 1608*n - 6, 294912*n^6 + 1646592*n^5 - 12288*n^4 + 128256*n^3 - 4512*n^2 + 2400*n - 120; 1296*n^2 + 216*n + 27, -442368*n^6 - 1720320*n^5 + 82944*n^4 - 75264*n^3 + 3024*n^2 - 672*n, 442368*n^6 + 1720320*n^5 - 79872*n^4 + 98304*n^3 - 8304*n^2 + 1392*n - 168]) 3 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (-1536*n^3 - 1152*G*n - 48*n + 864) * hG'
    | linear_combination (1048576*n^7 + 786432*G*n^5 + 1835008*n^6 + 589824*G^2*n^3 + 1376256*G*n^4 + 786432*n^5 + 442368*G^3*n + 1032192*G^2*n^2 + 1966080*G*n^3 - 1236992*n^4 + 774144*G^3 + 2506752*G^2*n + 1480704*G*n^2 + 1422336*n^3 + 2916864*G^2 + 4507392*G*n - 2404352*n^2 + 787968*G + 2490560*n - 4210704) * hG'
    | linear_combination (-1048576*n^7 - 786432*G*n^5 - 1835008*n^6 - 589824*G^2*n^3 - 1376256*G*n^4 - 786432*n^5 - 442368*G^3*n - 1032192*G^2*n^2 - 1966080*G*n^3 + 1212416*n^4 - 774144*G^3 - 2506752*G^2*n - 1499136*G*n^2 - 1416192*n^3 - 2930688*G^2 - 4502784*G*n + 2426624*n^2 - 803520*G - 2490368*n + 4251744) * hG'
    | linear_combination (1008*n + 432) * hG'
    | linear_combination (-294912*n^5 - 221184*G*n^3 - 1646592*n^4 - 165888*G^2*n - 1234944*G*n^2 - 503808*n^3 - 926208*G^2 - 764928*G*n - 2984448*n^2 - 4399488*G - 881184*n - 5224392) * hG'
    | linear_combination (294912*n^5 + 221184*G*n^3 + 1646592*n^4 + 165888*G^2*n + 1234944*G*n^2 + 503808*n^3 + 926208*G^2 + 764928*G*n + 3009792*n^2 + 4418496*G + 877152*n + 5269536) * hG'
    | linear_combination (1296*n + 216) * hG'
    | linear_combination (-442368*n^5 - 331776*G*n^3 - 1720320*n^4 - 248832*G^2*n - 1290240*G*n^2 - 691200*n^3 - 981504*G^2 - 1099008*G*n - 3085824*n^2 - 4636224*G - 1206576*n - 5474736) * hG'
    | linear_combination (442368*n^5 + 331776*G*n^3 + 1720320*n^4 + 248832*G^2*n + 1290240*G*n^2 + 694272*n^3 + 981504*G^2 + 1101312*G*n + 3108864*n^2 + 4653504*G + 1206672*n + 5515776) * hG'
    | ring1

theorem uv_comm_u {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((uM F N) * (uvM i F G N)) ((uvM i F G N) * (uM F N)) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![-1152*n^2 + 72, 24576*n^5 + 27648*n^4 + 33792*n^3 - 864*n^2 + 1032*n - 54, -262144*n^7 + 409600*n^6 + 909312*n^5 - 52224*n^4 + 6912*n^3 - 3888*n^2 - 680*n - 58; -27*n, 3072*n^4 + 23040*n^3 + 480*n^2 + 1584*n - 42, -3072*n^4 + 1152*n^3 + 96*n^2 + 1008*n + 6; 27, 3072*n^4 - 2304*n^3 - 96*n^2 - 936*n - 6, -3072*n^4 - 23040*n^3 + 672*n^2 - 1584*n - 30]) 3 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (-1152*n) * hG'
    | linear_combination (24576*n^4 + 18432*G*n^2 + 27648*n^3 + 13824*G^2 + 20736*G*n + 76800*n^2 + 89856*G + 47520*n + 135432) * hG'
    | linear_combination (-262144*n^6 - 196608*G*n^4 + 409600*n^5 - 147456*G^2*n^2 + 307200*G*n^3 + 450560*n^4 + 230400*G^2*n - 6144*G*n^2 + 664576*n^3 + 511488*G^2 + 1036032*G*n + 795392*n^2 + 2391552*G + 1159120*n + 2794824) * hG'
    | linear_combination (3072*n^3 + 2304*G*n + 23040*n^2 + 17280*G + 5856*n + 41904) * hG'
    | linear_combination (-3072*n^3 - 2304*G*n + 1152*n^2 + 1728*G - 5280*n + 4968) * hG'
    | linear_combination (3072*n^3 + 2304*G*n - 2304*n^2 - 1728*G + 5280*n - 4968) * hG'
    | linear_combination (-3072*n^3 - 2304*G*n - 23040*n^2 - 17280*G - 4704*n - 41904) * hG'
    | ring1

theorem t_u {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (k m) ((uM F N) * (tM i F G N)) ((tM i F G N) * ((uvM i F G N) * (uM F N))) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi
  subst hF
  subst hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ k (s + 2) r = 4 * n := by
    intro r
    fin_cases r <;> simp [k, Type32x.k]
    all_goals
      rw [hn, pow_add]
      norm_num
      ring
  refine MatEq.of_three_pow_mul_witness (k := k (s + 2)) (W := !![-3072*n^5 + 1536*n^4 + 6432*n^3 - 336*n^2 - 1632*n - 12, 1048576*n^8 + 1835008*n^7 - 983040*n^6 - 4448256*n^5 - 118272*n^4 - 235008*n^3 + 3824*n^2 - 2944*n + 204, -131072*n^7 + 65536*n^6 + 258048*n^5 - 76800*n^4 - 83712*n^3 + 1056*n^2 - 2872*n + 110; 2016*n^3 - 144*n^2 - 369*n + 9, -294912*n^6 - 1646592*n^5 - 30720*n^4 - 121344*n^3 + 1824*n^2 - 2184*n + 78, 86016*n^5 - 6144*n^4 - 46464*n^3 + 192*n^2 - 1536*n + 12; 2592*n^3 - 864*n^2 - 135*n - 27, -442368*n^6 - 1720320*n^5 + 27648*n^4 - 84480*n^3 + 4752*n^2 - 960*n + 108, 110592*n^5 - 39936*n^4 - 35712*n^3 + 1248*n^2 - 1224*n + 78]) 3 ?_
  intro r c
  rw [h2m r]
  fin_cases r <;> fin_cases c <;>
    simp [hsub, hNn, -mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (-3072*n^4 - 2304*G*n^2 + 1536*n^3 + 1152*G*n + 1056*n^2 + 2352*n - 1728) * hG'
    | linear_combination (1048576*n^7 + 786432*G*n^5 + 1835008*n^6 + 589824*G^2*n^3 + 1376256*G*n^4 + 851968*n^5 + 442368*G^3*n + 1032192*G^2*n^2 + 2015232*G*n^3 - 1236992*n^4 + 774144*G^3 + 2543616*G^2*n + 1480704*G*n^2 + 1372672*n^3 + 2916864*G^2 + 4556160*G*n - 2399744*n^2 + 791424*G + 2406000*n - 4202496) * hG'
    | linear_combination (-131072*n^6 - 98304*G*n^4 + 65536*n^5 - 73728*G^2*n^2 + 49152*G*n^3 + 28672*n^4 + 36864*G^2*n - 150528*G*n^2 + 37888*n^3 + 13824*G^2 + 114432*G*n - 33536*n^2 + 6912*G + 67360*n - 61560) * hG'
    | linear_combination (2016*n^2 - 144*n - 432) * hG'
    | linear_combination (-294912*n^5 - 221184*G*n^3 - 1646592*n^4 - 165888*G^2*n - 1234944*G*n^2 - 546816*n^3 - 926208*G^2 - 797184*G*n - 3002880*n^2 - 4413312*G - 955104*n - 5257224) * hG'
    | linear_combination (86016*n^4 + 64512*G*n^2 - 6144*n^3 - 4608*G*n + 104064*n^2 - 32832*G - 10560*n - 77976) * hG'
    | linear_combination (2592*n^2 - 864*n - 216) * hG'
    | linear_combination (-442368*n^5 - 331776*G*n^3 - 1720320*n^4 - 248832*G^2*n - 1290240*G*n^2 - 746496*n^3 - 981504*G^2 - 1140480*G*n - 3095040*n^2 - 4643136*G - 1301616*n - 5491152) * hG'
    | linear_combination (110592*n^4 + 82944*G*n^2 - 39936*n^3 - 29952*G*n + 157824*n^2 - 24192*G - 68640*n - 57456) * hG'
    | ring1

@[expose] def action {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM i F G N) (tM i F G N) (uM F N) ρM
    (compat_uv m i F G N) (compat_t m i F G N) (compat_u m i F G N) (compat_rho m i F G N)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

@[expose] def actionPaper (m : ℕ) (hm : 3 ≤ m) : SigmaFourAction (k m) :=
  action (Type32x.data m (Nat.le_trans (by norm_num) hm))

end Type330

end CFSG.CGT.Stroth77
