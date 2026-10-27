module

public import CFSG.CGT.Stroth77.Types120
public import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem MatEq.of_dvd_mul_coprime {k : Fin 3 → ℕ} {A B : IntMat} {c : ℤ} (P : IntMat)
    (hc : ∀ i, IsCoprime ((2 : ℤ) ^ k i) c)
    (h : ∀ i j, c * (A i j - B i j) = (2 : ℤ) ^ k i * P i j) : MatEq k A B := by
  intro i j
  refine Int.modEq_iff_dvd.2 ((hc i).dvd_of_dvd_mul_left ?_)
  exact ⟨-P i j, by linear_combination -h i j⟩

theorem four_pow_eq_two_pow_two (s : ℕ) : (4 : ℤ) ^ s = (2 : ℤ) ^ (2 * s) := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]

theorem four_pow_eq_two_pow_sq (s : ℕ) : (4 : ℤ) ^ s = (((2 : ℤ) ^ s)) ^ 2 := by
  rw [four_pow_eq_two_pow_two]
  rw [← pow_mul]
  congr 1
  ring

theorem iV_eq_eight_GV_add_nineteen (s : ℕ) :
    Type120.iV (s + 4) = 8 * Type120.GV (s + 4) + 19 := by
  have hdvd : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 7 := by
    have h1 : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 1 := by
      simpa using sub_one_dvd_pow_sub_one (4 : ℤ) (s + 3)
    have h6 : (3 : ℤ) ∣ (6 : ℤ) := by norm_num
    convert dvd_sub h1 h6 using 1 <;> ring
  obtain ⟨c, hc⟩ := hdvd
  have h8 : (2 : ℤ) ^ (2 * (s + 4) + 1) = 8 * 4 ^ (s + 3) := by
    rw [show 2 * (s + 4) + 1 = 2 * (s + 3) + 3 by ring, pow_add]
    rw [← four_pow_eq_two_pow_two (s + 3)]
    norm_num
    ring
  have hdiv : (3 : ℤ) ∣ (2 : ℤ) ^ (2 * (s + 4) + 1) + 1 := by
    refine ⟨8 * c + 19, ?_⟩
    rw [h8, show (4 : ℤ) ^ (s + 3) = 3 * c + 7 by linarith]
    ring
  have h := Int.mul_ediv_cancel' hdiv
  have hG := Int.mul_ediv_cancel' (⟨c, hc⟩ : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 7)
  have hsub : s + 4 - 1 = s + 3 := by omega
  simp only [Type120.iV, Type120.GV, hsub]
  nlinarith [h, hG, h8]

theorem FV_eq_four_GV_add_nine (s : ℕ) :
    Type120.FV (s + 4) = 4 * Type120.GV (s + 4) + 9 := by
  have hdvd : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 7 := by
    have h1 : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 1 := by
      simpa using sub_one_dvd_pow_sub_one (4 : ℤ) (s + 3)
    have h6 : (3 : ℤ) ∣ (6 : ℤ) := by norm_num
    convert dvd_sub h1 h6 using 1 <;> ring
  obtain ⟨c, hc⟩ := hdvd
  have hdiv : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 4) - 1 := by
    refine ⟨4 * c + 9, ?_⟩
    rw [show s + 4 = s + 3 + 1 by ring, pow_succ]
    rw [show (4 : ℤ) ^ (s + 3) = 3 * c + 7 by linarith]
    ring
  have h := Int.mul_ediv_cancel' hdiv
  have hG := Int.mul_ediv_cancel' (⟨c, hc⟩ : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 7)
  have h4 : (4 : ℤ) ^ (s + 4) - 1 = 4 * ((4 : ℤ) ^ (s + 3) - 7) + 27 := by
    rw [show s + 4 = s + 3 + 1 by ring, pow_succ]
    ring
  have hsub : s + 4 - 1 = s + 3 := by omega
  simp only [Type120.FV, Type120.GV, hsub]
  nlinarith [h, hG, h4]

theorem three_mul_GV_add_seven (s : ℕ) :
    3 * Type120.GV (s + 4) + 7 = 64 * (((2 : ℤ) ^ s)) ^ 2 := by
  have hdvd : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 7 := by
    have h1 : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 1 := by
      simpa using sub_one_dvd_pow_sub_one (4 : ℤ) (s + 3)
    have h6 : (3 : ℤ) ∣ (6 : ℤ) := by norm_num
    convert dvd_sub h1 h6 using 1 <;> ring
  obtain ⟨c, hc⟩ := hdvd
  have hG := Int.mul_ediv_cancel' (⟨c, hc⟩ : (3 : ℤ) ∣ (4 : ℤ) ^ (s + 3) - 7)
  have h4 : (4 : ℤ) ^ (s + 3) = 64 * (((2 : ℤ) ^ s)) ^ 2 := by
    rw [show s + 3 = s + 3 by rfl, pow_add]
    rw [four_pow_eq_two_pow_sq s]
    norm_num
    ring
  have hsub : s + 4 - 1 = s + 3 := by omega
  simp only [Type120.GV, hsub]
  linarith

theorem sixty_four_mul_pow_two_sq (s : ℕ) :
    64 * (((2 : ℤ) ^ s)) ^ 2 = (2 : ℤ) ^ (2 * s + 6) := by
  rw [← four_pow_eq_two_pow_sq s]
  rw [four_pow_eq_two_pow_two]
  rw [show 2 * s + 6 = 2 * s + 6 by rfl, pow_add]
  norm_num
  ring


namespace Type220

@[expose] def k (s : ℕ) : Fin 3 → ℕ := ![s + 2, s + 4, s + 4]

structure Data (s : ℕ) (i F G : ℤ) : Prop where
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hG : 3 * G + 7 = 64 * (((2 : ℤ) ^ s)) ^ 2
  hs : ∀ r, (2 : ℤ) ^ k s r ∣ 3 * G + 7

theorem data (s : ℕ) : Data s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) where
  hi := iV_eq_eight_GV_add_nineteen s
  hF := FV_eq_four_GV_add_nine s
  hG := three_mul_GV_add_seven s
  hs := by
    intro r
    rw [three_mul_GV_add_seven s, sixty_four_mul_pow_two_sq s]
    fin_cases r <;> simp [k] <;> exact pow_dvd_pow 2 (by omega)

@[expose] def ρM : IntMat := ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1]

@[expose] def uvA (i F G : ℤ) : Fin 3 → ℤ := ![F * i, -5 * i, 2 * i]

@[expose] def tM (i F G : ℤ) : IntMat :=
  ofCols ![4 - i, 4, 8] ![2 * G * i, -7 * i, -8 * i] (ρM *ᵥ uvA i F G)

@[expose] def uvM (i F G : ℤ) : IntMat :=
  ofCols ![-i, 4, -4] (uvA i F G) (ρM *ᵥ (tM i F G *ᵥ uvA i F G))

@[expose] def uM (i F G : ℤ) : IntMat := uMat ![-1, 0, 0] (-2 * F)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (uvM i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-8*G - 19, 128*G^2 + 592*G + 684, -1536*G^3 - 13184*G^2 - 36568*G - 33060; 1, -40*G - 95, -1920*G^2 - 9088*G - 10754; -1, 16*G + 38, 192*G^2 + 928*G + 1121]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_t {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (tM i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-8*G - 15, 64*G^2 + 152*G, 128*G^2 + 528*G + 532; 1, -56*G - 133, -16*G - 38; 2, -64*G - 152, -56*G - 133]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (uM i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-1, -32*G - 72, -32*G - 72; 0, 0, 1; 0, 1, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) ρM := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem uv_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uvM i F G) * (uvM i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![512*G^2 + 3264*G + 4872, -2048*G^3 - 18176*G^2 - 51680*G - 47652, -24576*G^4 - 291840*G^3 - 1247616*G^2 - 2304624*G - 1563852; 2560*G + 6080, -10240*G^2 - 48320*G - 56992, -122880*G^3 - 863744*G^2 - 2023936*G - 1580952; -256*G - 608, 1024*G^2 + 4736*G + 5472, 12288*G^3 + 80384*G^2 + 174592*G + 125864]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem t_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((tM i F G) * (tM i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![128*G + 184, -1024*G^2 - 3648*G - 2888, -768*G^2 - 3008*G - 2812; -128, 1408*G + 3352, 640*G + 1520; -256, 2432*G + 5776, 1472*G + 3504]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem uv_comm_t {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((tM i F G) * (uvM i F G)) ((uvM i F G) * (tM i F G)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![1024*G^2 + 6336*G + 9272, -8192*G^3 - 70144*G^2 - 194432*G - 175864, -14336*G^3 - 88576*G^2 - 178656*G - 116736; 5120*G + 12288, -40960*G^2 - 195648*G - 233624, -1536*G^2 - 8448*G - 11400; -512*G - 1344, 4096*G^2 + 20928*G + 26600, 39936*G^2 + 189312*G + 224352]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem rho_cube {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem u_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM i F G) * (uM i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem u_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * ((uM i F G) * (ρM * (uM i F G)))) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 8, 0; 0, 0, 0; 0, 0, 0]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem uv_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (uvM i F G)) ((tM i F G) * ρM) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 0, -128*G^2 - 848*G - 1324; 0, 0, -64*G - 184; 0, 0, -704*G - 1736]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem t_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (tM i F G)) ((tM i F G) * ((uvM i F G) * ρM)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![32, 7168*G^3 + 27008*G^2 + 7296*G - 38988, -7168*G^3 - 27136*G^2 - 7440*G + 39368; 64, -34304*G^2 - 162944*G - 193496, 34304*G^2 + 163648*G + 195168; 32, -36352*G^2 - 171712*G - 202768, 36352*G^2 + 172352*G + 204288]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem uv_comm_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM i F G) * (uvM i F G)) ((uvM i F G) * (uM i F G)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 128*G^2 + 832*G + 1254, 4736*G^2 + 22144*G + 25878; 0, 640*G + 1552, 64*G + 184; 0, -64*G - 184, -640*G - 1552]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)
theorem t_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM i F G) * (tM i F G)) ((tM i F G) * ((uvM i F G) * (uM i F G))) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![-64, 7168*G^3 + 27008*G^2 + 7328*G - 38912, 128*G^2 + 64*G - 570; -64, -34304*G^2 - 163456*G - 194712, -1216*G - 2888; -32, -36352*G^2 - 171968*G - 203376, -896*G - 2128]) (by
    intro r c
    fin_cases r <;> fin_cases c <;> simp <;> ring1)

@[expose] def action {s : ℕ} {i F G : ℤ} (h : Data s i F G) : SigmaFourAction (k s) :=
  SigmaFourAction.ofMatEq (uvM i F G) (tM i F G) (uM i F G) ρM
    (compat_uv h) (compat_t h) (compat_u h) (compat_rho h)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

@[expose] def actionPaper (s : ℕ) : SigmaFourAction (k s) := action (data s)

end Type220

namespace Type221

@[expose] def k (s : ℕ) : Fin 3 → ℕ := ![s + 2, s + 4, s + 4]

structure Data (s : ℕ) (i F G : ℤ) : Prop where
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hG : 3 * G + 7 = 64 * (((2 : ℤ) ^ s)) ^ 2
  hs : ∀ r, (2 : ℤ) ^ k s r ∣ 3 * G + 7

theorem data (s : ℕ) : Data s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) where
  hi := iV_eq_eight_GV_add_nineteen s
  hF := FV_eq_four_GV_add_nine s
  hG := three_mul_GV_add_seven s
  hs := by
    intro r
    rw [three_mul_GV_add_seven s, sixty_four_mul_pow_two_sq s]
    fin_cases r <;> simp [k] <;> exact pow_dvd_pow 2 (by omega)

@[expose] def ρM : IntMat := ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1]

@[expose] def uvA (s : ℕ) (i F G : ℤ) : Fin 3 → ℤ := ![F * i, -5 * i, 2 * i + 8 * ((2 : ℤ) ^ s)]

@[expose] def tM (s : ℕ) (i F G : ℤ) : IntMat :=
  ofCols ![4 - i, 4, 8] ![2 * G * i, -7 * i + 8 * ((2 : ℤ) ^ s), -8 * i] (ρM *ᵥ uvA s i F G)

@[expose] def uvM (s : ℕ) (i F G : ℤ) : IntMat :=
  ofCols ![-i, 4, -4] (uvA s i F G) (ρM *ᵥ (tM s i F G *ᵥ uvA s i F G))

@[expose] def uM (s : ℕ) (i F G : ℤ) : IntMat := uMat ![-1, 0, 0] (-2 * F)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (uvM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-8*G - 19, 128*G^2 + 592*G + 684, -1536*G^3 + 1024*G^2*((2 : ℤ) ^ s) - 13184*G^2 + 6016*G*((2 : ℤ) ^ s) - 36568*G + 8512*((2 : ℤ) ^ s) - 33060; 1, -40*G - 95, -1920*G^2 + 576*G*((2 : ℤ) ^ s) - 9088*G + 64*((2 : ℤ) ^ s)^2 + 1368*((2 : ℤ) ^ s) - 10754; -1, 16*G + 8*((2 : ℤ) ^ s) + 38, 192*G^2 + 928*G + 1121]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_t {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (tM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-8*G - 15, 64*G^2 + 152*G, 128*G^2 + 528*G - 32*((2 : ℤ) ^ s) + 532; 1, -56*G + 8*((2 : ℤ) ^ s) - 133, -16*G - 8*((2 : ℤ) ^ s) - 38; 2, -64*G - 152, -56*G - 8*((2 : ℤ) ^ s) - 133]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (uM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-1, -32*G - 72, -32*G - 72; 0, 0, 1; 0, 1, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) ρM := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem uv_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uvM s i F G) * (uvM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![100663296*((2 : ℤ) ^ s)^5 - 3145728*((2 : ℤ) ^ s)^4 + 8060928*((2 : ℤ) ^ s)^3 - 178176*((2 : ℤ) ^ s)^2 + 18816*((2 : ℤ) ^ s) - 336, -8589934592*((2 : ℤ) ^ s)^7 + 67108864*((2 : ℤ) ^ s)^6 - 748683264*((2 : ℤ) ^ s)^5 + 786432*((2 : ℤ) ^ s)^4 - 2494464*((2 : ℤ) ^ s)^3 + 20736*((2 : ℤ) ^ s)^2 - 2080*((2 : ℤ) ^ s) + 38, -2199023255552*((2 : ℤ) ^ s)^9 + 68719476736*((2 : ℤ) ^ s)^8 - 261993005056*((2 : ℤ) ^ s)^7 + 5502926848*((2 : ℤ) ^ s)^6 - 1478492160*((2 : ℤ) ^ s)^5 + 30670848*((2 : ℤ) ^ s)^4 - 2879488*((2 : ℤ) ^ s)^3 + 58880*((2 : ℤ) ^ s)^2 - 1904*((2 : ℤ) ^ s) + 38; 5898240*((2 : ℤ) ^ s)^3 - 82944*((2 : ℤ) ^ s)^2 + 11088*((2 : ℤ) ^ s) - 162, -503316480*((2 : ℤ) ^ s)^5 - 4718592*((2 : ℤ) ^ s)^4 - 1026048*((2 : ℤ) ^ s)^3 - 8352*((2 : ℤ) ^ s)^2 + 780*((2 : ℤ) ^ s), -128849018880*((2 : ℤ) ^ s)^7 + 1811939328*((2 : ℤ) ^ s)^6 - 166723584*((2 : ℤ) ^ s)^5 + 786432*((2 : ℤ) ^ s)^4 - 411648*((2 : ℤ) ^ s)^3 + 23808*((2 : ℤ) ^ s)^2 - 1128*((2 : ℤ) ^ s) + 57; -589824*((2 : ℤ) ^ s)^3 - 1152*((2 : ℤ) ^ s) + 54, 50331648*((2 : ℤ) ^ s)^5 + 1179648*((2 : ℤ) ^ s)^4 - 98304*((2 : ℤ) ^ s)^3 - 2304*((2 : ℤ) ^ s)^2 - 384*((2 : ℤ) ^ s) - 9, 12884901888*((2 : ℤ) ^ s)^7 - 276824064*((2 : ℤ) ^ s)^5 - 5505024*((2 : ℤ) ^ s)^4 + 595968*((2 : ℤ) ^ s)^3 - 52896*((2 : ℤ) ^ s)^2 + 3180*((2 : ℤ) ^ s) - 84]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (13824*G^2 + 294912*G*((2 : ℤ) ^ s)^2 - 9216*G*((2 : ℤ) ^ s) + 88128*G + 6291456*((2 : ℤ) ^ s)^4 - 196608*((2 : ℤ) ^ s)^3 + 1191936*((2 : ℤ) ^ s)^2 - 32640*((2 : ℤ) ^ s) + 131544) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-55296*G^3 - 1179648*G^2*((2 : ℤ) ^ s)^2 + 9216*G^2*((2 : ℤ) ^ s) - 490752*G^2 - 25165824*G*((2 : ℤ) ^ s)^4 + 196608*G*((2 : ℤ) ^ s)^3 - 7698432*G*((2 : ℤ) ^ s)^2 + 45312*G*((2 : ℤ) ^ s) - 1395360*G - 536870912*((2 : ℤ) ^ s)^6 + 4194304*((2 : ℤ) ^ s)^5 - 105512960*((2 : ℤ) ^ s)^4 + 507904*((2 : ℤ) ^ s)^3 - 11696384*((2 : ℤ) ^ s)^2 + 56848*((2 : ℤ) ^ s) - 1286604) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-663552*G^4 - 14155776*G^3*((2 : ℤ) ^ s)^2 + 442368*G^3*((2 : ℤ) ^ s) - 7879680*G^3 - 301989888*G^2*((2 : ℤ) ^ s)^4 + 9437184*G^2*((2 : ℤ) ^ s)^3 - 135069696*G^2*((2 : ℤ) ^ s)^2 + 3852288*G^2*((2 : ℤ) ^ s) - 33685632*G^2 - 6442450944*G*((2 : ℤ) ^ s)^6 + 201326592*G*((2 : ℤ) ^ s)^5 - 2176843776*G*((2 : ℤ) ^ s)^4 + 60162048*G*((2 : ℤ) ^ s)^3 - 403445760*G*((2 : ℤ) ^ s)^2 + 10841856*G*((2 : ℤ) ^ s) - 62224848*G - 137438953472*((2 : ℤ) ^ s)^8 + 4294967296*((2 : ℤ) ^ s)^7 - 31406948352*((2 : ℤ) ^ s)^6 + 813694976*((2 : ℤ) ^ s)^5 - 3527540736*((2 : ℤ) ^ s)^4 + 90914816*((2 : ℤ) ^ s)^3 - 386004736*((2 : ℤ) ^ s)^2 + 9947488*((2 : ℤ) ^ s) - 42224004) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (69120*G + 1474560*((2 : ℤ) ^ s)^2 - 20736*((2 : ℤ) ^ s) + 164160) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-276480*G^2 - 5898240*G*((2 : ℤ) ^ s)^2 - 55296*G*((2 : ℤ) ^ s) - 1304640*G - 125829120*((2 : ℤ) ^ s)^4 - 1179648*((2 : ℤ) ^ s)^3 - 14019072*((2 : ℤ) ^ s)^2 - 131328*((2 : ℤ) ^ s) - 1538784) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-3317760*G^3 - 70778880*G^2*((2 : ℤ) ^ s)^2 + 995328*G^2*((2 : ℤ) ^ s) - 23321088*G^2 - 1509949440*G*((2 : ℤ) ^ s)^4 + 21233664*G*((2 : ℤ) ^ s)^3 - 332255232*G*((2 : ℤ) ^ s)^2 + 4654080*G*((2 : ℤ) ^ s) - 54646272*G - 32212254720*((2 : ℤ) ^ s)^6 + 452984832*((2 : ℤ) ^ s)^5 - 3564896256*((2 : ℤ) ^ s)^4 + 49741824*((2 : ℤ) ^ s)^3 - 390013440*((2 : ℤ) ^ s)^2 + 5446464*((2 : ℤ) ^ s) - 42685704) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-6912*G - 147456*((2 : ℤ) ^ s)^2 - 16416) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (27648*G^2 + 589824*G*((2 : ℤ) ^ s)^2 + 13824*G*((2 : ℤ) ^ s) + 127872*G + 12582912*((2 : ℤ) ^ s)^4 + 294912*((2 : ℤ) ^ s)^3 + 1351680*((2 : ℤ) ^ s)^2 + 31680*((2 : ℤ) ^ s) + 147744) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (331776*G^3 + 7077888*G^2*((2 : ℤ) ^ s)^2 + 2170368*G^2 + 150994944*G*((2 : ℤ) ^ s)^4 + 29786112*G*((2 : ℤ) ^ s)^2 - 64512*G*((2 : ℤ) ^ s) + 4713984*G + 3221225472*((2 : ℤ) ^ s)^6 + 283115520*((2 : ℤ) ^ s)^4 - 1376256*((2 : ℤ) ^ s)^3 + 31114752*((2 : ℤ) ^ s)^2 - 163968*((2 : ℤ) ^ s) + 3398328) * hG
theorem t_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((tM s i F G) * (tM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 2) (P := !![393216*((2 : ℤ) ^ s)^3 - 16512*((2 : ℤ) ^ s) - 144, -67108864*((2 : ℤ) ^ s)^5 + 131072*((2 : ℤ) ^ s)^4 + 3473408*((2 : ℤ) ^ s)^3 + 10496*((2 : ℤ) ^ s)^2 + 7040*((2 : ℤ) ^ s) + 20, -50331648*((2 : ℤ) ^ s)^5 - 393216*((2 : ℤ) ^ s)^4 + 1769472*((2 : ℤ) ^ s)^3 + 45312*((2 : ℤ) ^ s)^2 + 3792*((2 : ℤ) ^ s) + 18; -4608*((2 : ℤ) ^ s) - 18, 1081344*((2 : ℤ) ^ s)^3 - 4608*((2 : ℤ) ^ s)^2 + 2436*((2 : ℤ) ^ s) - 9, 491520*((2 : ℤ) ^ s)^3 + 10752*((2 : ℤ) ^ s)^2 + 960*((2 : ℤ) ^ s) + 3; -9216*((2 : ℤ) ^ s) - 36, 1867776*((2 : ℤ) ^ s)^3 + 3648*((2 : ℤ) ^ s), 1130496*((2 : ℤ) ^ s)^3 + 16896*((2 : ℤ) ^ s)^2 + 2532*((2 : ℤ) ^ s) - 3]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 2)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (1152*G + 24576*((2 : ℤ) ^ s)^2 + 1656) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-9216*G^2 - 196608*G*((2 : ℤ) ^ s)^2 + 384*G*((2 : ℤ) ^ s) - 32832*G - 4194304*((2 : ℤ) ^ s)^4 + 8192*((2 : ℤ) ^ s)^3 - 241664*((2 : ℤ) ^ s)^2 + 1552*((2 : ℤ) ^ s) - 25992) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-6912*G^2 - 147456*G*((2 : ℤ) ^ s)^2 - 1152*G*((2 : ℤ) ^ s) - 27072*G - 3145728*((2 : ℤ) ^ s)^4 - 24576*((2 : ℤ) ^ s)^3 - 233472*((2 : ℤ) ^ s)^2 + 144*((2 : ℤ) ^ s) - 25308) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1152) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (12672*G + 270336*((2 : ℤ) ^ s)^2 - 1152*((2 : ℤ) ^ s) + 30168) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (5760*G + 122880*((2 : ℤ) ^ s)^2 + 2688*((2 : ℤ) ^ s) + 13680) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-2304) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (21888*G + 466944*((2 : ℤ) ^ s)^2 + 51984) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (13248*G + 282624*((2 : ℤ) ^ s)^2 + 4224*((2 : ℤ) ^ s) + 31536) * hG
theorem uv_comm_t {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((tM s i F G) * (uvM s i F G)) ((uvM s i F G) * (tM s i F G)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![201326592*((2 : ℤ) ^ s)^5 - 6291456*((2 : ℤ) ^ s)^4 + 14352384*((2 : ℤ) ^ s)^3 - 356352*((2 : ℤ) ^ s)^2 + 27264*((2 : ℤ) ^ s) - 456, -34359738368*((2 : ℤ) ^ s)^7 + 1073741824*((2 : ℤ) ^ s)^6 - 2516582400*((2 : ℤ) ^ s)^5 + 62914560*((2 : ℤ) ^ s)^4 - 8257536*((2 : ℤ) ^ s)^3 + 196608*((2 : ℤ) ^ s)^2 - 7216*((2 : ℤ) ^ s) + 152, -60129542144*((2 : ℤ) ^ s)^7 + 1207959552*((2 : ℤ) ^ s)^6 + 2324692992*((2 : ℤ) ^ s)^5 - 32243712*((2 : ℤ) ^ s)^4 + 5031936*((2 : ℤ) ^ s)^3 + 12288*((2 : ℤ) ^ s)^2 + 512*((2 : ℤ) ^ s) + 156; 11796480*((2 : ℤ) ^ s)^3 - 165888*((2 : ℤ) ^ s)^2 + 36000*((2 : ℤ) ^ s) - 216, -2013265920*((2 : ℤ) ^ s)^5 + 28311552*((2 : ℤ) ^ s)^4 - 10223616*((2 : ℤ) ^ s)^3 + 101376*((2 : ℤ) ^ s)^2 - 12396*((2 : ℤ) ^ s) + 90, -75497472*((2 : ℤ) ^ s)^5 - 23986176*((2 : ℤ) ^ s)^4 - 2617344*((2 : ℤ) ^ s)^3 - 48192*((2 : ℤ) ^ s)^2 - 4824*((2 : ℤ) ^ s) + 48; -1179648*((2 : ℤ) ^ s)^3 - 16128*((2 : ℤ) ^ s), 201326592*((2 : ℤ) ^ s)^5 + 4177920*((2 : ℤ) ^ s)^3 - 9216*((2 : ℤ) ^ s)^2 + 7176*((2 : ℤ) ^ s) - 18, 1962934272*((2 : ℤ) ^ s)^5 - 26738688*((2 : ℤ) ^ s)^4 + 6635520*((2 : ℤ) ^ s)^3 - 12288*((2 : ℤ) ^ s)^2 + 5580*((2 : ℤ) ^ s) + 24]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (27648*G^2 + 589824*G*((2 : ℤ) ^ s)^2 - 18432*G*((2 : ℤ) ^ s) + 171072*G + 12582912*((2 : ℤ) ^ s)^4 - 393216*((2 : ℤ) ^ s)^3 + 2273280*((2 : ℤ) ^ s)^2 - 65280*((2 : ℤ) ^ s) + 250344) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-221184*G^3 - 4718592*G^2*((2 : ℤ) ^ s)^2 + 147456*G^2*((2 : ℤ) ^ s) - 1893888*G^2 - 100663296*G*((2 : ℤ) ^ s)^4 + 3145728*G*((2 : ℤ) ^ s)^3 - 29392896*G*((2 : ℤ) ^ s)^2 + 872448*G*((2 : ℤ) ^ s) - 5249664*G - 2147483648*((2 : ℤ) ^ s)^6 + 67108864*((2 : ℤ) ^ s)^5 - 392167424*((2 : ℤ) ^ s)^4 + 11272192*((2 : ℤ) ^ s)^3 - 43409408*((2 : ℤ) ^ s)^2 + 1245184*((2 : ℤ) ^ s) - 4748328) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-387072*G^3 - 8257536*G^2*((2 : ℤ) ^ s)^2 + 165888*G^2*((2 : ℤ) ^ s) - 2391552*G^2 - 176160768*G*((2 : ℤ) ^ s)^4 + 3538944*G*((2 : ℤ) ^ s)^3 - 31724544*G*((2 : ℤ) ^ s)^2 + 679680*G*((2 : ℤ) ^ s) - 4823712*G - 3758096384*((2 : ℤ) ^ s)^6 + 75497472*((2 : ℤ) ^ s)^5 - 265748480*((2 : ℤ) ^ s)^4 + 6242304*((2 : ℤ) ^ s)^3 - 28751744*((2 : ℤ) ^ s)^2 + 683520*((2 : ℤ) ^ s) - 3151872) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (138240*G + 2949120*((2 : ℤ) ^ s)^2 - 41472*((2 : ℤ) ^ s) + 331776) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-1105920*G^2 - 23592960*G*((2 : ℤ) ^ s)^2 + 331776*G*((2 : ℤ) ^ s) - 5282496*G - 503316480*((2 : ℤ) ^ s)^4 + 7077888*((2 : ℤ) ^ s)^3 - 57606144*((2 : ℤ) ^ s)^2 + 799488*((2 : ℤ) ^ s) - 6307848) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-41472*G^2 - 884736*G*((2 : ℤ) ^ s)^2 - 281088*G*((2 : ℤ) ^ s) - 228096*G - 18874368*((2 : ℤ) ^ s)^4 - 5996544*((2 : ℤ) ^ s)^3 - 2718720*((2 : ℤ) ^ s)^2 - 668352*((2 : ℤ) ^ s) - 307800) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-13824*G - 294912*((2 : ℤ) ^ s)^2 - 36288) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (110592*G^2 + 2359296*G*((2 : ℤ) ^ s)^2 + 565056*G + 50331648*((2 : ℤ) ^ s)^4 + 6549504*((2 : ℤ) ^ s)^2 - 2304*((2 : ℤ) ^ s) + 718200) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (1078272*G^2 + 23003136*G*((2 : ℤ) ^ s)^2 - 313344*G*((2 : ℤ) ^ s) + 5111424*G + 490733568*((2 : ℤ) ^ s)^4 - 6684672*((2 : ℤ) ^ s)^3 + 55332864*((2 : ℤ) ^ s)^2 - 734208*((2 : ℤ) ^ s) + 6057504) * hG
theorem rho_cube {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 0) (P := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 0)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem u_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (uM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 0) (P := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 0)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem u_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * ((uM s i F G) * (ρM * (uM s i F G)))) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 0) (P := !![0, 128*((2 : ℤ) ^ s), 0; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 0)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (8) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem uv_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (uvM s i F G)) ((tM s i F G) * ρM) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 2) (P := !![0, 0, -8388608*((2 : ℤ) ^ s)^5 + 262144*((2 : ℤ) ^ s)^4 - 770048*((2 : ℤ) ^ s)^3 + 14848*((2 : ℤ) ^ s)^2 - 6080*((2 : ℤ) ^ s) + 10; 0, 0, -49152*((2 : ℤ) ^ s)^3 - 1248*((2 : ℤ) ^ s); 0, 0, -540672*((2 : ℤ) ^ s)^3 + 6912*((2 : ℤ) ^ s)^2 - 3324*((2 : ℤ) ^ s) + 9]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 2)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-1152*G^2 - 24576*G*((2 : ℤ) ^ s)^2 + 768*G*((2 : ℤ) ^ s) - 7632*G - 524288*((2 : ℤ) ^ s)^4 + 16384*((2 : ℤ) ^ s)^3 - 105472*((2 : ℤ) ^ s)^2 + 2720*((2 : ℤ) ^ s) - 11916) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-576*G - 12288*((2 : ℤ) ^ s)^2 - 1656) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-6336*G - 135168*((2 : ℤ) ^ s)^2 + 1728*((2 : ℤ) ^ s) - 15624) * hG
theorem t_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (tM s i F G)) ((tM s i F G) * ((uvM s i F G) * ρM)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![13824*((2 : ℤ) ^ s) - 216, 30064771072*((2 : ℤ) ^ s)^7 - 469762048*((2 : ℤ) ^ s)^6 - 4558159872*((2 : ℤ) ^ s)^5 + 73138176*((2 : ℤ) ^ s)^4 - 14997504*((2 : ℤ) ^ s)^3 + 143616*((2 : ℤ) ^ s)^2 - 11680*((2 : ℤ) ^ s) - 2, -30064771072*((2 : ℤ) ^ s)^7 + 469762048*((2 : ℤ) ^ s)^6 + 4532994048*((2 : ℤ) ^ s)^5 - 72351744*((2 : ℤ) ^ s)^4 + 19175424*((2 : ℤ) ^ s)^3 - 182016*((2 : ℤ) ^ s)^2 + 19504*((2 : ℤ) ^ s) + 140; 6912*((2 : ℤ) ^ s) - 108, -1686110208*((2 : ℤ) ^ s)^5 + 36962304*((2 : ℤ) ^ s)^4 - 6623232*((2 : ℤ) ^ s)^3 + 97440*((2 : ℤ) ^ s)^2 - 6504*((2 : ℤ) ^ s) + 51, 1686110208*((2 : ℤ) ^ s)^5 - 36962304*((2 : ℤ) ^ s)^4 + 8245248*((2 : ℤ) ^ s)^3 - 118176*((2 : ℤ) ^ s)^2 + 9564*((2 : ℤ) ^ s) + 30; 3456*((2 : ℤ) ^ s) - 54, -1786773504*((2 : ℤ) ^ s)^5 + 27918336*((2 : ℤ) ^ s)^4 - 4620288*((2 : ℤ) ^ s)^3 + 30720*((2 : ℤ) ^ s)^2 - 2208*((2 : ℤ) ^ s) - 33, 1786773504*((2 : ℤ) ^ s)^5 - 27918336*((2 : ℤ) ^ s)^4 + 6094848*((2 : ℤ) ^ s)^3 - 51456*((2 : ℤ) ^ s)^2 + 4980*((2 : ℤ) ^ s) + 60]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (193536*G^3 + 4128768*G^2*((2 : ℤ) ^ s)^2 - 64512*G^2*((2 : ℤ) ^ s) + 729216*G^2 + 88080384*G*((2 : ℤ) ^ s)^4 - 1376256*G*((2 : ℤ) ^ s)^3 + 5913600*G*((2 : ℤ) ^ s)^2 - 86784*G*((2 : ℤ) ^ s) + 196992*G + 1879048192*((2 : ℤ) ^ s)^6 - 29360128*((2 : ℤ) ^ s)^5 - 79364096*((2 : ℤ) ^ s)^4 + 1359872*((2 : ℤ) ^ s)^3 - 9617792*((2 : ℤ) ^ s)^2 + 157712*((2 : ℤ) ^ s) - 1052676) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-193536*G^3 - 4128768*G^2*((2 : ℤ) ^ s)^2 + 64512*G^2*((2 : ℤ) ^ s) - 732672*G^2 - 88080384*G*((2 : ℤ) ^ s)^4 + 1376256*G*((2 : ℤ) ^ s)^3 - 5987328*G*((2 : ℤ) ^ s)^2 + 89088*G*((2 : ℤ) ^ s) - 200880*G - 1879048192*((2 : ℤ) ^ s)^6 + 29360128*((2 : ℤ) ^ s)^5 + 77791232*((2 : ℤ) ^ s)^4 - 1310720*((2 : ℤ) ^ s)^3 + 9706880*((2 : ℤ) ^ s)^2 - 154736*((2 : ℤ) ^ s) + 1062936) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-926208*G^2 - 19759104*G*((2 : ℤ) ^ s)^2 + 433152*G*((2 : ℤ) ^ s) - 4399488*G - 421527552*((2 : ℤ) ^ s)^4 + 9240576*((2 : ℤ) ^ s)^3 - 47760384*((2 : ℤ) ^ s)^2 + 1035264*((2 : ℤ) ^ s) - 5224392) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (926208*G^2 + 19759104*G*((2 : ℤ) ^ s)^2 - 433152*G*((2 : ℤ) ^ s) + 4418496*G + 421527552*((2 : ℤ) ^ s)^4 - 9240576*((2 : ℤ) ^ s)^3 + 48165888*((2 : ℤ) ^ s)^2 - 1040448*((2 : ℤ) ^ s) + 5269536) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-981504*G^2 - 20938752*G*((2 : ℤ) ^ s)^2 + 327168*G*((2 : ℤ) ^ s) - 4636224*G - 446693376*((2 : ℤ) ^ s)^4 + 6979584*((2 : ℤ) ^ s)^3 - 50012160*((2 : ℤ) ^ s)^2 + 771072*((2 : ℤ) ^ s) - 5474736) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (981504*G^2 + 20938752*G*((2 : ℤ) ^ s)^2 - 327168*G*((2 : ℤ) ^ s) + 4653504*G + 446693376*((2 : ℤ) ^ s)^4 - 6979584*((2 : ℤ) ^ s)^3 + 50380800*((2 : ℤ) ^ s)^2 - 776256*((2 : ℤ) ^ s) + 5515776) * hG
theorem uv_comm_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (uvM s i F G)) ((uvM s i F G) * (uM s i F G)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 2) (P := !![0, 8388608*((2 : ℤ) ^ s)^5 - 262144*((2 : ℤ) ^ s)^4 + 720896*((2 : ℤ) ^ s)^3 - 17920*((2 : ℤ) ^ s)^2 + 1376*((2 : ℤ) ^ s) - 16, 310378496*((2 : ℤ) ^ s)^5 - 4980736*((2 : ℤ) ^ s)^4 + 106496*((2 : ℤ) ^ s)^3 - 5632*((2 : ℤ) ^ s)^2 - 832*((2 : ℤ) ^ s) + 8; 0, 491520*((2 : ℤ) ^ s)^3 - 6912*((2 : ℤ) ^ s)^2 + 2076*((2 : ℤ) ^ s) - 9, 49152*((2 : ℤ) ^ s)^3 + 1248*((2 : ℤ) ^ s); 0, -49152*((2 : ℤ) ^ s)^3 - 1248*((2 : ℤ) ^ s), -491520*((2 : ℤ) ^ s)^3 + 6912*((2 : ℤ) ^ s)^2 - 2076*((2 : ℤ) ^ s) + 9]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 2)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (1152*G^2 + 24576*G*((2 : ℤ) ^ s)^2 - 768*G*((2 : ℤ) ^ s) + 7488*G + 524288*((2 : ℤ) ^ s)^4 - 16384*((2 : ℤ) ^ s)^3 + 102400*((2 : ℤ) ^ s)^2 - 2912*((2 : ℤ) ^ s) + 11286) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (42624*G^2 + 909312*G*((2 : ℤ) ^ s)^2 - 14592*G*((2 : ℤ) ^ s) + 199296*G + 19398656*((2 : ℤ) ^ s)^4 - 311296*((2 : ℤ) ^ s)^3 + 2128384*((2 : ℤ) ^ s)^2 - 34400*((2 : ℤ) ^ s) + 232902) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (5760*G + 122880*((2 : ℤ) ^ s)^2 - 1728*((2 : ℤ) ^ s) + 13968) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (576*G + 12288*((2 : ℤ) ^ s)^2 + 1656) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-576*G - 12288*((2 : ℤ) ^ s)^2 - 1656) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-5760*G - 122880*((2 : ℤ) ^ s)^2 + 1728*((2 : ℤ) ^ s) - 13968) * hG
theorem t_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (tM s i F G)) ((tM s i F G) * ((uvM s i F G) * (uM s i F G))) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![216 - 27648*((2 : ℤ) ^ s), 30064771072*((2 : ℤ) ^ s)^7 - 469762048*((2 : ℤ) ^ s)^6 - 4558159872*((2 : ℤ) ^ s)^5 + 73138176*((2 : ℤ) ^ s)^4 - 14702592*((2 : ℤ) ^ s)^3 + 171264*((2 : ℤ) ^ s)^2 - 11104*((2 : ℤ) ^ s) - 110, 25165824*((2 : ℤ) ^ s)^5 - 786432*((2 : ℤ) ^ s)^4 - 4915200*((2 : ℤ) ^ s)^3 + 93696*((2 : ℤ) ^ s)^2 - 9264*((2 : ℤ) ^ s) - 84; 108 - 6912*((2 : ℤ) ^ s), -1686110208*((2 : ℤ) ^ s)^5 + 36962304*((2 : ℤ) ^ s)^4 - 7802880*((2 : ℤ) ^ s)^3 + 115872*((2 : ℤ) ^ s)^2 - 8808*((2 : ℤ) ^ s) - 21, -2801664*((2 : ℤ) ^ s)^3 + 39168*((2 : ℤ) ^ s)^2 - 5364*((2 : ℤ) ^ s) - 45; 54 - 3456*((2 : ℤ) ^ s), -1786773504*((2 : ℤ) ^ s)^5 + 27918336*((2 : ℤ) ^ s)^4 - 5210112*((2 : ℤ) ^ s)^3 + 39936*((2 : ℤ) ^ s)^2 - 3360*((2 : ℤ) ^ s) - 69, -2064384*((2 : ℤ) ^ s)^3 + 29952*((2 : ℤ) ^ s)^2 - 3924*((2 : ℤ) ^ s) - 9]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (193536*G^3 + 4128768*G^2*((2 : ℤ) ^ s)^2 - 64512*G^2*((2 : ℤ) ^ s) + 729216*G^2 + 88080384*G*((2 : ℤ) ^ s)^4 - 1376256*G*((2 : ℤ) ^ s)^3 + 5913600*G*((2 : ℤ) ^ s)^2 - 86784*G*((2 : ℤ) ^ s) + 197856*G + 1879048192*((2 : ℤ) ^ s)^6 - 29360128*((2 : ℤ) ^ s)^5 - 79364096*((2 : ℤ) ^ s)^4 + 1359872*((2 : ℤ) ^ s)^3 - 9599360*((2 : ℤ) ^ s)^2 + 159440*((2 : ℤ) ^ s) - 1050624) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (3456*G^2 + 73728*G*((2 : ℤ) ^ s)^2 - 2304*G*((2 : ℤ) ^ s) + 1728*G + 1572864*((2 : ℤ) ^ s)^4 - 49152*((2 : ℤ) ^ s)^3 - 135168*((2 : ℤ) ^ s)^2 + 480*((2 : ℤ) ^ s) - 15390) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-926208*G^2 - 19759104*G*((2 : ℤ) ^ s)^2 + 433152*G*((2 : ℤ) ^ s) - 4413312*G - 421527552*((2 : ℤ) ^ s)^4 + 9240576*((2 : ℤ) ^ s)^3 - 48055296*((2 : ℤ) ^ s)^2 + 1039872*((2 : ℤ) ^ s) - 5257224) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-32832*G - 700416*((2 : ℤ) ^ s)^2 + 9792*((2 : ℤ) ^ s) - 77976) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-981504*G^2 - 20938752*G*((2 : ℤ) ^ s)^2 + 327168*G*((2 : ℤ) ^ s) - 4643136*G - 446693376*((2 : ℤ) ^ s)^4 + 6979584*((2 : ℤ) ^ s)^3 - 50159616*((2 : ℤ) ^ s)^2 + 773376*((2 : ℤ) ^ s) - 5491152) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-24192*G - 516096*((2 : ℤ) ^ s)^2 + 7488*((2 : ℤ) ^ s) - 57456) * hG

@[expose] def action {s : ℕ} {i F G : ℤ} (h : Data s i F G) : SigmaFourAction (k s) :=
  SigmaFourAction.ofMatEq (uvM s i F G) (tM s i F G) (uM s i F G) ρM
    (compat_uv h) (compat_t h) (compat_u h) (compat_rho h)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

@[expose] def actionPaper (s : ℕ) : SigmaFourAction (k s) := action (data s)

end Type221

namespace Type230

@[expose] def k (s : ℕ) : Fin 3 → ℕ := ![s + 2, s + 4, s + 4]

structure Data (s : ℕ) (i F G : ℤ) : Prop where
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hG : 3 * G + 7 = 64 * (((2 : ℤ) ^ s)) ^ 2
  hs : ∀ r, (2 : ℤ) ^ k s r ∣ 3 * G + 7

theorem data (s : ℕ) : Data s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) where
  hi := iV_eq_eight_GV_add_nineteen s
  hF := FV_eq_four_GV_add_nine s
  hG := three_mul_GV_add_seven s
  hs := by
    intro r
    rw [three_mul_GV_add_seven s, sixty_four_mul_pow_two_sq s]
    fin_cases r <;> simp [k] <;> exact pow_dvd_pow 2 (by omega)

@[expose] def ρM : IntMat := ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1]

@[expose] def uvA (s : ℕ) (i F G : ℤ) : Fin 3 → ℤ := ![2 * ((2 : ℤ) ^ s) + F * i, -5 * i + 8 * ((2 : ℤ) ^ s), 2 * i - 4 * ((2 : ℤ) ^ s)]

@[expose] def tM (s : ℕ) (i F G : ℤ) : IntMat :=
  ofCols ![4 - i, 4, 8 + 8 * ((2 : ℤ) ^ s)] ![2 * ((2 : ℤ) ^ s) + 2 * G * i, -7 * i - 4 * ((2 : ℤ) ^ s), -8 * i + 8 * ((2 : ℤ) ^ s)] (ρM *ᵥ uvA s i F G)

@[expose] def uvM (s : ℕ) (i F G : ℤ) : IntMat :=
  ofCols ![-i, 4 + 8 * ((2 : ℤ) ^ s), -4] (uvA s i F G) (ρM *ᵥ (tM s i F G *ᵥ uvA s i F G))

@[expose] def uM (s : ℕ) (i F G : ℤ) : IntMat := uMat ![-1 + 2 * ((2 : ℤ) ^ s), 0, 0] (-2 * F + 2 * ((2 : ℤ) ^ s))

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (uvM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-8*G - 19, 128*G^2 + 592*G + 8*((2 : ℤ) ^ s) + 684, -1536*G^3 - 1024*G^2*((2 : ℤ) ^ s) - 13184*G^2 - 3968*G*((2 : ℤ) ^ s) - 36568*G - 160*((2 : ℤ) ^ s)^2 - 3680*((2 : ℤ) ^ s) - 33060; 2*((2 : ℤ) ^ s) + 1, -40*G + 8*((2 : ℤ) ^ s) - 95, -256*G^2*((2 : ℤ) ^ s) - 1920*G^2 - 768*G*((2 : ℤ) ^ s) - 9088*G - 32*((2 : ℤ) ^ s)^2 - 396*((2 : ℤ) ^ s) - 10754; -1, 16*G - 4*((2 : ℤ) ^ s) + 38, -256*G^2*((2 : ℤ) ^ s) + 192*G^2 - 928*G*((2 : ℤ) ^ s) + 928*G - 80*((2 : ℤ) ^ s)^2 - 768*((2 : ℤ) ^ s) + 1121]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_t {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (tM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-8*G - 15, 64*G^2 + 152*G + 8*((2 : ℤ) ^ s), 128*G^2 + 528*G + 24*((2 : ℤ) ^ s) + 532; 1, -56*G - 4*((2 : ℤ) ^ s) - 133, -16*G + 4*((2 : ℤ) ^ s) - 38; 2*((2 : ℤ) ^ s) + 2, -64*G + 8*((2 : ℤ) ^ s) - 152, -56*G + 12*((2 : ℤ) ^ s) - 133]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (uM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![2*((2 : ℤ) ^ s) - 1, -32*G + 8*((2 : ℤ) ^ s) - 72, 64*G*((2 : ℤ) ^ s) - 32*G - 16*((2 : ℤ) ^ s)^2 + 152*((2 : ℤ) ^ s) - 72; 0, 0, 1; 0, 1, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) ρM := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem uv_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uvM s i F G) * (uvM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 4) (P := !![301989888*((2 : ℤ) ^ s)^5 + 11796480*((2 : ℤ) ^ s)^4 + 24182784*((2 : ℤ) ^ s)^3 - 354816*((2 : ℤ) ^ s)^2 + 60012*((2 : ℤ) ^ s) + 72, -25769803776*((2 : ℤ) ^ s)^7 - 503316480*((2 : ℤ) ^ s)^6 - 2255486976*((2 : ℤ) ^ s)^5 + 53084160*((2 : ℤ) ^ s)^4 - 9179136*((2 : ℤ) ^ s)^3 + 78120*((2 : ℤ) ^ s)^2 - 8544*((2 : ℤ) ^ s) - 60, 8796093022208*((2 : ℤ) ^ s)^10 - 6322191859712*((2 : ℤ) ^ s)^9 - 17179869184*((2 : ℤ) ^ s)^8 - 803561537536*((2 : ℤ) ^ s)^7 - 21023948800*((2 : ℤ) ^ s)^6 - 3603431424*((2 : ℤ) ^ s)^5 - 105918464*((2 : ℤ) ^ s)^4 - 7021792*((2 : ℤ) ^ s)^3 - 158960*((2 : ℤ) ^ s)^2 - 5342*((2 : ℤ) ^ s) - 98; 2359296*((2 : ℤ) ^ s)^4 + 17694720*((2 : ℤ) ^ s)^3 - 225792*((2 : ℤ) ^ s)^2 + 35532*((2 : ℤ) ^ s) + 36, -201326592*((2 : ℤ) ^ s)^6 - 1507590144*((2 : ℤ) ^ s)^5 + 33619968*((2 : ℤ) ^ s)^4 - 3926016*((2 : ℤ) ^ s)^3 + 20232*((2 : ℤ) ^ s)^2 + 1404*((2 : ℤ) ^ s) - 51, 68719476736*((2 : ℤ) ^ s)^9 + 463856467968*((2 : ℤ) ^ s)^8 - 395271208960*((2 : ℤ) ^ s)^7 - 19512950784*((2 : ℤ) ^ s)^6 + 60555264*((2 : ℤ) ^ s)^5 - 153243648*((2 : ℤ) ^ s)^4 + 738464*((2 : ℤ) ^ s)^3 - 195048*((2 : ℤ) ^ s)^2 - 2894*((2 : ℤ) ^ s) - 120; 2359296*((2 : ℤ) ^ s)^4 - 1769472*((2 : ℤ) ^ s)^3 - 101376*((2 : ℤ) ^ s)^2 - 1998*((2 : ℤ) ^ s) - 126, -201326592*((2 : ℤ) ^ s)^6 + 153354240*((2 : ℤ) ^ s)^5 + 7667712*((2 : ℤ) ^ s)^4 - 548352*((2 : ℤ) ^ s)^3 + 44244*((2 : ℤ) ^ s)^2 - 1656*((2 : ℤ) ^ s) + 12, 68719476736*((2 : ℤ) ^ s)^9 - 103079215104*((2 : ℤ) ^ s)^8 + 31943819264*((2 : ℤ) ^ s)^7 + 4120903680*((2 : ℤ) ^ s)^6 - 739246080*((2 : ℤ) ^ s)^5 + 72069120*((2 : ℤ) ^ s)^4 + 624272*((2 : ℤ) ^ s)^3 + 82248*((2 : ℤ) ^ s)^2 + 8263*((2 : ℤ) ^ s) + 66]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 4)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (41472*G^2 + 884736*G*((2 : ℤ) ^ s)^2 + 34560*G*((2 : ℤ) ^ s) + 264384*G + 18874368*((2 : ℤ) ^ s)^4 + 737280*((2 : ℤ) ^ s)^3 + 3575808*((2 : ℤ) ^ s)^2 + 58464*((2 : ℤ) ^ s) + 394632) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-165888*G^3 - 3538944*G^2*((2 : ℤ) ^ s)^2 - 69120*G^2*((2 : ℤ) ^ s) - 1472256*G^2 - 75497472*G*((2 : ℤ) ^ s)^4 - 1474560*G*((2 : ℤ) ^ s)^3 - 23122944*G*((2 : ℤ) ^ s)^2 - 167040*G*((2 : ℤ) ^ s) - 4186080*G - 1610612736*((2 : ℤ) ^ s)^6 - 31457280*((2 : ℤ) ^ s)^5 - 317128704*((2 : ℤ) ^ s)^4 - 122880*((2 : ℤ) ^ s)^3 - 35259648*((2 : ℤ) ^ s)^2 - 8760*((2 : ℤ) ^ s) - 3859812) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (2654208*G^4*((2 : ℤ) ^ s) - 1990656*G^4 + 56623104*G^3*((2 : ℤ) ^ s)^3 - 40697856*G^3*((2 : ℤ) ^ s)^2 + 24662016*G^3*((2 : ℤ) ^ s) - 23639040*G^3 + 1207959552*G^2*((2 : ℤ) ^ s)^5 - 868220928*G^2*((2 : ℤ) ^ s)^4 + 394002432*G^2*((2 : ℤ) ^ s)^3 - 395237376*G^2*((2 : ℤ) ^ s)^2 + 83003904*G^2*((2 : ℤ) ^ s) - 101056896*G^2 + 25769803776*G*((2 : ℤ) ^ s)^7 - 18522046464*G*((2 : ℤ) ^ s)^6 + 5586812928*G*((2 : ℤ) ^ s)^5 - 6405881856*G*((2 : ℤ) ^ s)^4 + 852240384*G*((2 : ℤ) ^ s)^3 - 1190266368*G*((2 : ℤ) ^ s)^2 + 119135424*G*((2 : ℤ) ^ s) - 186674544*G + 549755813888*((2 : ℤ) ^ s)^9 - 395136991232*((2 : ℤ) ^ s)^8 + 59055800320*((2 : ℤ) ^ s)^7 - 93440704512*((2 : ℤ) ^ s)^6 + 5145231360*((2 : ℤ) ^ s)^5 - 10445291520*((2 : ℤ) ^ s)^4 + 556139776*((2 : ℤ) ^ s)^3 - 1142896672*((2 : ℤ) ^ s)^2 + 60685904*((2 : ℤ) ^ s) - 126672012) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (27648*G*((2 : ℤ) ^ s) + 207360*G + 589824*((2 : ℤ) ^ s)^3 + 4423680*((2 : ℤ) ^ s)^2 + 8064*((2 : ℤ) ^ s) + 492480) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-110592*G^2*((2 : ℤ) ^ s) - 829440*G^2 - 2359296*G*((2 : ℤ) ^ s)^3 - 17667072*G*((2 : ℤ) ^ s)^2 - 122112*G*((2 : ℤ) ^ s) - 3913920*G - 50331648*((2 : ℤ) ^ s)^5 - 376897536*((2 : ℤ) ^ s)^4 + 2899968*((2 : ℤ) ^ s)^3 - 42204672*((2 : ℤ) ^ s)^2 + 322080*((2 : ℤ) ^ s) - 4616352) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (1769472*G^3*((2 : ℤ) ^ s)^2 + 11943936*G^3*((2 : ℤ) ^ s) - 9953280*G^3 + 37748736*G^2*((2 : ℤ) ^ s)^4 + 254803968*G^2*((2 : ℤ) ^ s)^3 - 204742656*G^2*((2 : ℤ) ^ s)^2 + 72852480*G^2*((2 : ℤ) ^ s) - 69963264*G^2 + 805306368*G*((2 : ℤ) ^ s)^6 + 5435817984*G*((2 : ℤ) ^ s)^5 - 4455923712*G*((2 : ℤ) ^ s)^4 + 960417792*G*((2 : ℤ) ^ s)^3 - 983657472*G*((2 : ℤ) ^ s)^2 + 143152128*G*((2 : ℤ) ^ s) - 163938816*G + 17179869184*((2 : ℤ) ^ s)^8 + 115964116992*((2 : ℤ) ^ s)^7 - 96938754048*((2 : ℤ) ^ s)^6 + 7805337600*((2 : ℤ) ^ s)^5 - 10587537408*((2 : ℤ) ^ s)^4 + 815397888*((2 : ℤ) ^ s)^3 - 1157830528*((2 : ℤ) ^ s)^2 + 89064912*((2 : ℤ) ^ s) - 128057112) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (27648*G*((2 : ℤ) ^ s) - 20736*G + 589824*((2 : ℤ) ^ s)^3 - 442368*((2 : ℤ) ^ s)^2 + 39168*((2 : ℤ) ^ s) - 49248) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-110592*G^2*((2 : ℤ) ^ s) + 82944*G^2 - 2359296*G*((2 : ℤ) ^ s)^3 + 1797120*G*((2 : ℤ) ^ s)^2 - 426240*G*((2 : ℤ) ^ s) + 383616*G - 50331648*((2 : ℤ) ^ s)^5 + 38338560*((2 : ℤ) ^ s)^4 - 3588096*((2 : ℤ) ^ s)^3 + 4056192*((2 : ℤ) ^ s)^2 - 381792*((2 : ℤ) ^ s) + 443232) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (1769472*G^3*((2 : ℤ) ^ s)^2 - 2654208*G^3*((2 : ℤ) ^ s) + 995328*G^3 + 37748736*G^2*((2 : ℤ) ^ s)^4 - 56623104*G^2*((2 : ℤ) ^ s)^3 + 29933568*G^2*((2 : ℤ) ^ s)^2 - 16367616*G^2*((2 : ℤ) ^ s) + 6511104*G^2 + 805306368*G*((2 : ℤ) ^ s)^6 - 1207959552*G*((2 : ℤ) ^ s)^5 + 550502400*G*((2 : ℤ) ^ s)^4 - 215949312*G*((2 : ℤ) ^ s)^3 + 102125568*G*((2 : ℤ) ^ s)^2 - 32131584*G*((2 : ℤ) ^ s) + 14141952*G + 17179869184*((2 : ℤ) ^ s)^8 - 25769803776*((2 : ℤ) ^ s)^7 + 9865003008*((2 : ℤ) ^ s)^6 - 1788346368*((2 : ℤ) ^ s)^5 + 894173184*((2 : ℤ) ^ s)^4 - 177583104*((2 : ℤ) ^ s)^3 + 97948160*((2 : ℤ) ^ s)^2 - 19558272*((2 : ℤ) ^ s) + 10194984) * hG
theorem t_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((tM s i F G) * (tM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 2) (P := !![262144*((2 : ℤ) ^ s)^4 + 393216*((2 : ℤ) ^ s)^3 - 6656*((2 : ℤ) ^ s)^2 - 16404*((2 : ℤ) ^ s) + 112, -67108864*((2 : ℤ) ^ s)^5 + 196608*((2 : ℤ) ^ s)^4 + 3473408*((2 : ℤ) ^ s)^3 - 24192*((2 : ℤ) ^ s)^2 + 7130*((2 : ℤ) ^ s) - 30, -50331648*((2 : ℤ) ^ s)^5 + 458752*((2 : ℤ) ^ s)^4 + 1769472*((2 : ℤ) ^ s)^3 - 36992*((2 : ℤ) ^ s)^2 + 3828*((2 : ℤ) ^ s) - 20; -1536*((2 : ℤ) ^ s)^2 - 4590*((2 : ℤ) ^ s) + 6, 1081344*((2 : ℤ) ^ s)^3 + 768*((2 : ℤ) ^ s)^2 + 2427*((2 : ℤ) ^ s) + 6, 491520*((2 : ℤ) ^ s)^3 - 6912*((2 : ℤ) ^ s)^2 + 978*((2 : ℤ) ^ s); -6144*((2 : ℤ) ^ s)^2 - 9162*((2 : ℤ) ^ s) + 78, 32768*((2 : ℤ) ^ s)^4 + 1867776*((2 : ℤ) ^ s)^3 - 20416*((2 : ℤ) ^ s)^2 + 3693*((2 : ℤ) ^ s) - 31, 65536*((2 : ℤ) ^ s)^4 + 1130496*((2 : ℤ) ^ s)^3 - 22400*((2 : ℤ) ^ s)^2 + 2622*((2 : ℤ) ^ s) - 17]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 2)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (768*G*((2 : ℤ) ^ s) + 1152*G + 16384*((2 : ℤ) ^ s)^3 + 24576*((2 : ℤ) ^ s)^2 + 1376*((2 : ℤ) ^ s) + 1656) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-9216*G^2 - 196608*G*((2 : ℤ) ^ s)^2 + 576*G*((2 : ℤ) ^ s) - 32832*G - 4194304*((2 : ℤ) ^ s)^4 + 12288*((2 : ℤ) ^ s)^3 - 241664*((2 : ℤ) ^ s)^2 - 168*((2 : ℤ) ^ s) - 25992) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-6912*G^2 - 147456*G*((2 : ℤ) ^ s)^2 + 1344*G*((2 : ℤ) ^ s) - 27072*G - 3145728*((2 : ℤ) ^ s)^4 + 28672*((2 : ℤ) ^ s)^3 - 233472*((2 : ℤ) ^ s)^2 + 824*((2 : ℤ) ^ s) - 25308) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-384*((2 : ℤ) ^ s) - 1152) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (12672*G + 270336*((2 : ℤ) ^ s)^2 + 192*((2 : ℤ) ^ s) + 30168) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (5760*G + 122880*((2 : ℤ) ^ s)^2 - 1728*((2 : ℤ) ^ s) + 13680) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1536*((2 : ℤ) ^ s) - 2304) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (384*G*((2 : ℤ) ^ s) + 21888*G + 8192*((2 : ℤ) ^ s)^3 + 466944*((2 : ℤ) ^ s)^2 - 4208*((2 : ℤ) ^ s) + 51984) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (768*G*((2 : ℤ) ^ s) + 13248*G + 16384*((2 : ℤ) ^ s)^3 + 282624*((2 : ℤ) ^ s)^2 - 3808*((2 : ℤ) ^ s) + 31536) * hG
theorem uv_comm_t {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((tM s i F G) * (uvM s i F G)) ((uvM s i F G) * (tM s i F G)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![201326592*((2 : ℤ) ^ s)^6 + 207618048*((2 : ℤ) ^ s)^5 + 21626880*((2 : ℤ) ^ s)^4 + 14118912*((2 : ℤ) ^ s)^3 - 235920*((2 : ℤ) ^ s)^2 + 29484*((2 : ℤ) ^ s) - 276, -34359738368*((2 : ℤ) ^ s)^7 - 872415232*((2 : ℤ) ^ s)^6 - 2510290944*((2 : ℤ) ^ s)^5 + 53084160*((2 : ℤ) ^ s)^4 - 8859648*((2 : ℤ) ^ s)^3 + 111216*((2 : ℤ) ^ s)^2 - 7552*((2 : ℤ) ^ s) + 58, -17179869184*((2 : ℤ) ^ s)^8 - 60129542144*((2 : ℤ) ^ s)^7 + 1409286144*((2 : ℤ) ^ s)^6 + 2308964352*((2 : ℤ) ^ s)^5 - 21037056*((2 : ℤ) ^ s)^4 + 5108736*((2 : ℤ) ^ s)^3 + 94288*((2 : ℤ) ^ s)^2 - 304*((2 : ℤ) ^ s) + 60; 1572864*((2 : ℤ) ^ s)^5 + 13369344*((2 : ℤ) ^ s)^4 + 11673600*((2 : ℤ) ^ s)^3 - 99408*((2 : ℤ) ^ s)^2 + 37212*((2 : ℤ) ^ s) - 192, -268435456*((2 : ℤ) ^ s)^6 - 2011693056*((2 : ℤ) ^ s)^5 + 32145408*((2 : ℤ) ^ s)^4 - 10567680*((2 : ℤ) ^ s)^3 + 98544*((2 : ℤ) ^ s)^2 - 12804*((2 : ℤ) ^ s) + 67, 67108864*((2 : ℤ) ^ s)^6 - 73138176*((2 : ℤ) ^ s)^5 + 20054016*((2 : ℤ) ^ s)^4 - 3110400*((2 : ℤ) ^ s)^3 + 114756*((2 : ℤ) ^ s)^2 - 5823*((2 : ℤ) ^ s) + 53; 1572864*((2 : ℤ) ^ s)^5 + 393216*((2 : ℤ) ^ s)^4 - 1256448*((2 : ℤ) ^ s)^3 - 105672*((2 : ℤ) ^ s)^2 - 14988*((2 : ℤ) ^ s) - 102, -268435456*((2 : ℤ) ^ s)^6 + 202899456*((2 : ℤ) ^ s)^5 + 11599872*((2 : ℤ) ^ s)^4 + 3916800*((2 : ℤ) ^ s)^3 + 4536*((2 : ℤ) ^ s)^2 + 7011*((2 : ℤ) ^ s) + 1, 218103808*((2 : ℤ) ^ s)^6 + 1959788544*((2 : ℤ) ^ s)^5 - 37552128*((2 : ℤ) ^ s)^4 + 7037952*((2 : ℤ) ^ s)^3 - 39564*((2 : ℤ) ^ s)^2 + 5433*((2 : ℤ) ^ s) + 2]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (27648*G^2*((2 : ℤ) ^ s) + 27648*G^2 + 589824*G*((2 : ℤ) ^ s)^3 + 608256*G*((2 : ℤ) ^ s)^2 + 192384*G*((2 : ℤ) ^ s) + 171072*G + 12582912*((2 : ℤ) ^ s)^5 + 12976128*((2 : ℤ) ^ s)^4 + 2727936*((2 : ℤ) ^ s)^3 + 2301696*((2 : ℤ) ^ s)^2 + 283488*((2 : ℤ) ^ s) + 250344) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-221184*G^3 - 4718592*G^2*((2 : ℤ) ^ s)^2 - 119808*G^2*((2 : ℤ) ^ s) - 1893888*G^2 - 100663296*G*((2 : ℤ) ^ s)^4 - 2555904*G*((2 : ℤ) ^ s)^3 - 29374464*G*((2 : ℤ) ^ s)^2 - 403584*G*((2 : ℤ) ^ s) - 5249664*G - 2147483648*((2 : ℤ) ^ s)^6 - 54525952*((2 : ℤ) ^ s)^5 - 391774208*((2 : ℤ) ^ s)^4 - 2646016*((2 : ℤ) ^ s)^3 - 43404032*((2 : ℤ) ^ s)^2 - 282592*((2 : ℤ) ^ s) - 4748328) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-110592*G^3*((2 : ℤ) ^ s) - 387072*G^3 - 2359296*G^2*((2 : ℤ) ^ s)^3 - 8257536*G^2*((2 : ℤ) ^ s)^2 - 580608*G^2*((2 : ℤ) ^ s) - 2391552*G^2 - 50331648*G*((2 : ℤ) ^ s)^5 - 176160768*G*((2 : ℤ) ^ s)^4 - 6881280*G*((2 : ℤ) ^ s)^3 - 31770624*G*((2 : ℤ) ^ s)^2 - 964800*G*((2 : ℤ) ^ s) - 4823712*G - 1073741824*((2 : ℤ) ^ s)^7 - 3758096384*((2 : ℤ) ^ s)^6 - 29360128*((2 : ℤ) ^ s)^5 - 266731520*((2 : ℤ) ^ s)^4 - 4526080*((2 : ℤ) ^ s)^3 - 28854464*((2 : ℤ) ^ s)^2 - 489120*((2 : ℤ) ^ s) - 3151872) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (18432*G*((2 : ℤ) ^ s)^2 + 156672*G*((2 : ℤ) ^ s) + 138240*G + 393216*((2 : ℤ) ^ s)^4 + 3342336*((2 : ℤ) ^ s)^3 + 2961408*((2 : ℤ) ^ s)^2 + 340608*((2 : ℤ) ^ s) + 331776) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-147456*G^2*((2 : ℤ) ^ s) - 1105920*G^2 - 3145728*G*((2 : ℤ) ^ s)^3 - 23574528*G*((2 : ℤ) ^ s)^2 - 311424*G*((2 : ℤ) ^ s) - 5282496*G - 67108864*((2 : ℤ) ^ s)^5 - 502923264*((2 : ℤ) ^ s)^4 + 696320*((2 : ℤ) ^ s)^3 - 57649152*((2 : ℤ) ^ s)^2 + 100688*((2 : ℤ) ^ s) - 6307848) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (36864*G^2*((2 : ℤ) ^ s) - 41472*G^2 + 786432*G*((2 : ℤ) ^ s)^3 - 857088*G*((2 : ℤ) ^ s)^2 + 407040*G*((2 : ℤ) ^ s) - 228096*G + 16777216*((2 : ℤ) ^ s)^5 - 18284544*((2 : ℤ) ^ s)^4 + 6848512*((2 : ℤ) ^ s)^3 - 2777472*((2 : ℤ) ^ s)^2 + 777664*((2 : ℤ) ^ s) - 307800) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (18432*G*((2 : ℤ) ^ s)^2 + 4608*G*((2 : ℤ) ^ s) - 13824*G + 393216*((2 : ℤ) ^ s)^4 + 98304*((2 : ℤ) ^ s)^3 - 271104*((2 : ℤ) ^ s)^2 - 15936*((2 : ℤ) ^ s) - 36288) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-147456*G^2*((2 : ℤ) ^ s) + 110592*G^2 - 3145728*G*((2 : ℤ) ^ s)^3 + 2377728*G*((2 : ℤ) ^ s)^2 - 552192*G*((2 : ℤ) ^ s) + 565056*G - 67108864*((2 : ℤ) ^ s)^5 + 50724864*((2 : ℤ) ^ s)^4 - 4440064*((2 : ℤ) ^ s)^3 + 6527232*((2 : ℤ) ^ s)^2 - 484768*((2 : ℤ) ^ s) + 718200) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (119808*G^2*((2 : ℤ) ^ s) + 1078272*G^2 + 2555904*G*((2 : ℤ) ^ s)^3 + 22966272*G*((2 : ℤ) ^ s)^2 + 119040*G*((2 : ℤ) ^ s) + 5111424*G + 54525952*((2 : ℤ) ^ s)^5 + 489947136*((2 : ℤ) ^ s)^4 - 3424256*((2 : ℤ) ^ s)^3 + 55347456*((2 : ℤ) ^ s)^2 - 384176*((2 : ℤ) ^ s) + 6057504) * hG
theorem rho_cube {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 0) (P := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 0)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem u_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (uM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 1) (P := !![3*((2 : ℤ) ^ s) - 3, 0, 512*((2 : ℤ) ^ s)^3 - 518*((2 : ℤ) ^ s)^2 + 4*((2 : ℤ) ^ s) + 2; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 1)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (32*((2 : ℤ) ^ s)^2 - 32*((2 : ℤ) ^ s)) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem u_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * ((uM s i F G) * (ρM * (uM s i F G)))) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 1) (P := !![3*((2 : ℤ) ^ s) - 3, -512*((2 : ℤ) ^ s)^2 + 390*((2 : ℤ) ^ s) - 4, 512*((2 : ℤ) ^ s)^3 - 262*((2 : ℤ) ^ s)^2 + ((2 : ℤ) ^ s) + 1; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 1)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (24 - 32*((2 : ℤ) ^ s)) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (32*((2 : ℤ) ^ s)^2 - 16*((2 : ℤ) ^ s)) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem uv_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (uvM s i F G)) ((tM s i F G) * ρM) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 2) (P := !![0, 0, -8388608*((2 : ℤ) ^ s)^5 - 770048*((2 : ℤ) ^ s)^3 - 3072*((2 : ℤ) ^ s)^2 - 5990*((2 : ℤ) ^ s) + 12; 0, 0, 65536*((2 : ℤ) ^ s)^4 - 49152*((2 : ℤ) ^ s)^3 - 3200*((2 : ℤ) ^ s)^2 - 1203*((2 : ℤ) ^ s) - 2; 0, 0, -540672*((2 : ℤ) ^ s)^3 + 1920*((2 : ℤ) ^ s)^2 - 3333*((2 : ℤ) ^ s) + 15]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 2)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-1152*G^2 - 24576*G*((2 : ℤ) ^ s)^2 - 7632*G - 524288*((2 : ℤ) ^ s)^4 - 105472*((2 : ℤ) ^ s)^2 - 192*((2 : ℤ) ^ s) - 11916) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (768*G*((2 : ℤ) ^ s) - 576*G + 16384*((2 : ℤ) ^ s)^3 - 12288*((2 : ℤ) ^ s)^2 + 992*((2 : ℤ) ^ s) - 1656) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-6336*G - 135168*((2 : ℤ) ^ s)^2 + 480*((2 : ℤ) ^ s) - 15624) * hG
theorem t_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (tM s i F G)) ((tM s i F G) * ((uvM s i F G) * ρM)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![-393216*((2 : ℤ) ^ s)^4 + 42240*((2 : ℤ) ^ s)^2 + 13716*((2 : ℤ) ^ s) + 138, 17179869184*((2 : ℤ) ^ s)^8 + 30064771072*((2 : ℤ) ^ s)^7 - 2046820352*((2 : ℤ) ^ s)^6 - 4539285504*((2 : ℤ) ^ s)^5 + 76087296*((2 : ℤ) ^ s)^4 - 16103424*((2 : ℤ) ^ s)^3 + 52952*((2 : ℤ) ^ s)^2 - 12292*((2 : ℤ) ^ s) - 34, -17179869184*((2 : ℤ) ^ s)^8 - 30064771072*((2 : ℤ) ^ s)^7 + 2046820352*((2 : ℤ) ^ s)^6 + 4514119680*((2 : ℤ) ^ s)^5 - 75694080*((2 : ℤ) ^ s)^4 + 20281344*((2 : ℤ) ^ s)^3 - 127448*((2 : ℤ) ^ s)^2 + 20602*((2 : ℤ) ^ s) - 248; 16128*((2 : ℤ) ^ s)^2 + 6966*((2 : ℤ) ^ s) + 72, -301989888*((2 : ℤ) ^ s)^6 - 1686110208*((2 : ℤ) ^ s)^5 + 15335424*((2 : ℤ) ^ s)^4 - 6673920*((2 : ℤ) ^ s)^3 - 3132*((2 : ℤ) ^ s)^2 - 6387*((2 : ℤ) ^ s) - 27, 301989888*((2 : ℤ) ^ s)^6 + 1686110208*((2 : ℤ) ^ s)^5 - 15335424*((2 : ℤ) ^ s)^4 + 8295936*((2 : ℤ) ^ s)^3 - 18756*((2 : ℤ) ^ s)^2 + 9420*((2 : ℤ) ^ s) - 90; 20736*((2 : ℤ) ^ s)^2 + 3348*((2 : ℤ) ^ s) + 54, -452984832*((2 : ℤ) ^ s)^6 - 1781268480*((2 : ℤ) ^ s)^5 + 46792704*((2 : ℤ) ^ s)^4 - 5299200*((2 : ℤ) ^ s)^3 + 52320*((2 : ℤ) ^ s)^2 - 2529*((2 : ℤ) ^ s) + 3, 452984832*((2 : ℤ) ^ s)^6 + 1781268480*((2 : ℤ) ^ s)^5 - 46596096*((2 : ℤ) ^ s)^4 + 6773760*((2 : ℤ) ^ s)^3 - 88416*((2 : ℤ) ^ s)^2 + 5571*((2 : ℤ) ^ s) - 108]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1152*G*((2 : ℤ) ^ s) - 24576*((2 : ℤ) ^ s)^3 - 48*((2 : ℤ) ^ s) + 864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (110592*G^3*((2 : ℤ) ^ s) + 193536*G^3 + 2359296*G^2*((2 : ℤ) ^ s)^3 + 4128768*G^2*((2 : ℤ) ^ s)^2 + 493056*G^2*((2 : ℤ) ^ s) + 729216*G^2 + 50331648*G*((2 : ℤ) ^ s)^5 + 88080384*G*((2 : ℤ) ^ s)^4 + 5013504*G*((2 : ℤ) ^ s)^3 + 5968896*G*((2 : ℤ) ^ s)^2 + 717504*G*((2 : ℤ) ^ s) + 196992*G + 1073741824*((2 : ℤ) ^ s)^7 + 1879048192*((2 : ℤ) ^ s)^6 - 10485760*((2 : ℤ) ^ s)^5 - 78184448*((2 : ℤ) ^ s)^4 + 3608576*((2 : ℤ) ^ s)^3 - 9557888*((2 : ℤ) ^ s)^2 + 397768*((2 : ℤ) ^ s) - 1052676) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-110592*G^3*((2 : ℤ) ^ s) - 193536*G^3 - 2359296*G^2*((2 : ℤ) ^ s)^3 - 4128768*G^2*((2 : ℤ) ^ s)^2 - 493056*G^2*((2 : ℤ) ^ s) - 732672*G^2 - 50331648*G*((2 : ℤ) ^ s)^5 - 88080384*G*((2 : ℤ) ^ s)^4 - 5013504*G*((2 : ℤ) ^ s)^3 - 6042624*G*((2 : ℤ) ^ s)^2 - 716352*G*((2 : ℤ) ^ s) - 200880*G - 1073741824*((2 : ℤ) ^ s)^7 - 1879048192*((2 : ℤ) ^ s)^6 + 10485760*((2 : ℤ) ^ s)^5 + 76611584*((2 : ℤ) ^ s)^4 - 3584000*((2 : ℤ) ^ s)^3 + 9646976*((2 : ℤ) ^ s)^2 - 399736*((2 : ℤ) ^ s) + 1062936) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (4032*((2 : ℤ) ^ s) + 1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-165888*G^2*((2 : ℤ) ^ s) - 926208*G^2 - 3538944*G*((2 : ℤ) ^ s)^3 - 19759104*G*((2 : ℤ) ^ s)^2 - 594432*G*((2 : ℤ) ^ s) - 4399488*G - 75497472*((2 : ℤ) ^ s)^5 - 421527552*((2 : ℤ) ^ s)^4 - 4423680*((2 : ℤ) ^ s)^3 - 47773056*((2 : ℤ) ^ s)^2 - 484704*((2 : ℤ) ^ s) - 5224392) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (165888*G^2*((2 : ℤ) ^ s) + 926208*G^2 + 3538944*G*((2 : ℤ) ^ s)^3 + 19759104*G*((2 : ℤ) ^ s)^2 + 594432*G*((2 : ℤ) ^ s) + 4418496*G + 75497472*((2 : ℤ) ^ s)^5 + 421527552*((2 : ℤ) ^ s)^4 + 4423680*((2 : ℤ) ^ s)^3 + 48178560*((2 : ℤ) ^ s)^2 + 479232*((2 : ℤ) ^ s) + 5269536) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (5184*((2 : ℤ) ^ s) + 864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-248832*G^2*((2 : ℤ) ^ s) - 981504*G^2 - 5308416*G*((2 : ℤ) ^ s)^3 - 20874240*G*((2 : ℤ) ^ s)^2 - 612864*G*((2 : ℤ) ^ s) - 4636224*G - 113246208*((2 : ℤ) ^ s)^5 - 445317120*((2 : ℤ) ^ s)^4 - 688128*((2 : ℤ) ^ s)^3 - 50031360*((2 : ℤ) ^ s)^2 - 62832*((2 : ℤ) ^ s) - 5474736) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (248832*G^2*((2 : ℤ) ^ s) + 981504*G^2 + 5308416*G*((2 : ℤ) ^ s)^3 + 20874240*G*((2 : ℤ) ^ s)^2 + 615168*G*((2 : ℤ) ^ s) + 4653504*G + 113246208*((2 : ℤ) ^ s)^5 + 445317120*((2 : ℤ) ^ s)^4 + 737280*((2 : ℤ) ^ s)^3 + 50400000*((2 : ℤ) ^ s)^2 + 59184*((2 : ℤ) ^ s) + 5515776) * hG
theorem uv_comm_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (uvM s i F G)) ((uvM s i F G) * (uM s i F G)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![-18432*((2 : ℤ) ^ s)^2 + 216*((2 : ℤ) ^ s) + 72, 25165824*((2 : ℤ) ^ s)^5 + 1769472*((2 : ℤ) ^ s)^4 + 2144256*((2 : ℤ) ^ s)^3 - 40212*((2 : ℤ) ^ s)^2 + 4497*((2 : ℤ) ^ s) - 18, -268435456*((2 : ℤ) ^ s)^7 + 422576128*((2 : ℤ) ^ s)^6 + 938213376*((2 : ℤ) ^ s)^5 - 30812160*((2 : ℤ) ^ s)^4 + 716400*((2 : ℤ) ^ s)^3 - 10068*((2 : ℤ) ^ s)^2 - 2996*((2 : ℤ) ^ s) - 19; -27*((2 : ℤ) ^ s), 196608*((2 : ℤ) ^ s)^4 + 1474560*((2 : ℤ) ^ s)^3 - 13056*((2 : ℤ) ^ s)^2 + 6363*((2 : ℤ) ^ s) - 33, -196608*((2 : ℤ) ^ s)^4 + 142848*((2 : ℤ) ^ s)^3 + 9654*((2 : ℤ) ^ s)^2 + 3627*((2 : ℤ) ^ s) - 21; 27, 196608*((2 : ℤ) ^ s)^4 - 147456*((2 : ℤ) ^ s)^3 - 9600*((2 : ℤ) ^ s)^2 - 3609*((2 : ℤ) ^ s) + 21, -196608*((2 : ℤ) ^ s)^4 - 1474560*((2 : ℤ) ^ s)^3 + 17664*((2 : ℤ) ^ s)^2 - 6417*((2 : ℤ) ^ s) + 15]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1152*((2 : ℤ) ^ s)) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (3456*G^2 + 73728*G*((2 : ℤ) ^ s)^2 + 5184*G*((2 : ℤ) ^ s) + 22464*G + 1572864*((2 : ℤ) ^ s)^4 + 110592*((2 : ℤ) ^ s)^3 + 306048*((2 : ℤ) ^ s)^2 + 9576*((2 : ℤ) ^ s) + 33858) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-36864*G^2*((2 : ℤ) ^ s)^2 + 57600*G^2*((2 : ℤ) ^ s) + 127872*G^2 - 786432*G*((2 : ℤ) ^ s)^4 + 1238016*G*((2 : ℤ) ^ s)^3 + 2576640*G*((2 : ℤ) ^ s)^2 + 179520*G*((2 : ℤ) ^ s) + 597888*G - 16777216*((2 : ℤ) ^ s)^6 + 26411008*((2 : ℤ) ^ s)^5 + 56803328*((2 : ℤ) ^ s)^4 + 962944*((2 : ℤ) ^ s)^3 + 6257504*((2 : ℤ) ^ s)^2 + 104740*((2 : ℤ) ^ s) + 698706) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (2304*G*((2 : ℤ) ^ s) + 17280*G + 49152*((2 : ℤ) ^ s)^3 + 368640*((2 : ℤ) ^ s)^2 + 2112*((2 : ℤ) ^ s) + 41904) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-2304*G*((2 : ℤ) ^ s) + 1728*G - 49152*((2 : ℤ) ^ s)^3 + 35712*((2 : ℤ) ^ s)^2 - 2976*((2 : ℤ) ^ s) + 4968) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (2304*G*((2 : ℤ) ^ s) - 1728*G + 49152*((2 : ℤ) ^ s)^3 - 36864*((2 : ℤ) ^ s)^2 + 2976*((2 : ℤ) ^ s) - 4968) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-2304*G*((2 : ℤ) ^ s) - 17280*G - 49152*((2 : ℤ) ^ s)^3 - 368640*((2 : ℤ) ^ s)^2 - 960*((2 : ℤ) ^ s) - 41904) * hG
theorem t_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (tM s i F G)) ((tM s i F G) * ((uvM s i F G) * (uM s i F G))) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![-786432*((2 : ℤ) ^ s)^5 + 393216*((2 : ℤ) ^ s)^4 + 102912*((2 : ℤ) ^ s)^3 - 5808*((2 : ℤ) ^ s)^2 - 27336*((2 : ℤ) ^ s) + 42, 17179869184*((2 : ℤ) ^ s)^8 + 30064771072*((2 : ℤ) ^ s)^7 - 1979711488*((2 : ℤ) ^ s)^6 - 4540071936*((2 : ℤ) ^ s)^5 + 65568768*((2 : ℤ) ^ s)^4 - 15650304*((2 : ℤ) ^ s)^3 + 34280*((2 : ℤ) ^ s)^2 - 11323*((2 : ℤ) ^ s) + 133, -134217728*((2 : ℤ) ^ s)^7 + 68681728*((2 : ℤ) ^ s)^6 + 39321600*((2 : ℤ) ^ s)^5 - 5121024*((2 : ℤ) ^ s)^4 - 4802640*((2 : ℤ) ^ s)^3 + 7668*((2 : ℤ) ^ s)^2 - 9451*((2 : ℤ) ^ s) + 158; 32256*((2 : ℤ) ^ s)^3 - 2196*((2 : ℤ) ^ s)^2 - 6795*((2 : ℤ) ^ s) - 45, -301989888*((2 : ℤ) ^ s)^6 - 1686110208*((2 : ℤ) ^ s)^5 + 12582912*((2 : ℤ) ^ s)^4 - 7830528*((2 : ℤ) ^ s)^3 + 6960*((2 : ℤ) ^ s)^2 - 8484*((2 : ℤ) ^ s) + 84, 5505024*((2 : ℤ) ^ s)^5 - 439296*((2 : ℤ) ^ s)^4 - 2798808*((2 : ℤ) ^ s)^3 + 10830*((2 : ℤ) ^ s)^2 - 5352*((2 : ℤ) ^ s) + 84; 41472*((2 : ℤ) ^ s)^3 - 14040*((2 : ℤ) ^ s)^2 - 3213*((2 : ℤ) ^ s) - 54, -452984832*((2 : ℤ) ^ s)^6 - 1781268480*((2 : ℤ) ^ s)^5 + 43253760*((2 : ℤ) ^ s)^4 - 5829120*((2 : ℤ) ^ s)^3 + 61320*((2 : ℤ) ^ s)^2 - 3618*((2 : ℤ) ^ s) + 75, 7077888*((2 : ℤ) ^ s)^5 - 2675712*((2 : ℤ) ^ s)^4 - 2022480*((2 : ℤ) ^ s)^3 + 21930*((2 : ℤ) ^ s)^2 - 4140*((2 : ℤ) ^ s) + 60]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-2304*G*((2 : ℤ) ^ s)^2 + 1152*G*((2 : ℤ) ^ s) - 49152*((2 : ℤ) ^ s)^4 + 24576*((2 : ℤ) ^ s)^3 + 1056*((2 : ℤ) ^ s)^2 + 2352*((2 : ℤ) ^ s) - 1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (110592*G^3*((2 : ℤ) ^ s) + 193536*G^3 + 2359296*G^2*((2 : ℤ) ^ s)^3 + 4128768*G^2*((2 : ℤ) ^ s)^2 + 502272*G^2*((2 : ℤ) ^ s) + 729216*G^2 + 50331648*G*((2 : ℤ) ^ s)^5 + 88080384*G*((2 : ℤ) ^ s)^4 + 5210112*G*((2 : ℤ) ^ s)^3 + 5966592*G*((2 : ℤ) ^ s)^2 + 729696*G*((2 : ℤ) ^ s) + 197856*G + 1073741824*((2 : ℤ) ^ s)^7 + 1879048192*((2 : ℤ) ^ s)^6 - 6291456*((2 : ℤ) ^ s)^5 - 78233600*((2 : ℤ) ^ s)^4 + 3409920*((2 : ℤ) ^ s)^3 - 9534944*((2 : ℤ) ^ s)^2 + 374900*((2 : ℤ) ^ s) - 1050624) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-18432*G^2*((2 : ℤ) ^ s)^2 + 9216*G^2*((2 : ℤ) ^ s) + 3456*G^2 - 393216*G*((2 : ℤ) ^ s)^4 + 201216*G*((2 : ℤ) ^ s)^3 + 29184*G*((2 : ℤ) ^ s)^2 + 28608*G*((2 : ℤ) ^ s) + 1728*G - 8388608*((2 : ℤ) ^ s)^6 + 4292608*((2 : ℤ) ^ s)^5 + 1540096*((2 : ℤ) ^ s)^4 + 149440*((2 : ℤ) ^ s)^3 - 131744*((2 : ℤ) ^ s)^2 + 17128*((2 : ℤ) ^ s) - 15390) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (8064*((2 : ℤ) ^ s)^2 - 576*((2 : ℤ) ^ s) - 1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-165888*G^2*((2 : ℤ) ^ s) - 926208*G^2 - 3538944*G*((2 : ℤ) ^ s)^3 - 19759104*G*((2 : ℤ) ^ s)^2 - 626688*G*((2 : ℤ) ^ s) - 4413312*G - 75497472*((2 : ℤ) ^ s)^5 - 421527552*((2 : ℤ) ^ s)^4 - 5111808*((2 : ℤ) ^ s)^3 - 48062208*((2 : ℤ) ^ s)^2 - 557472*((2 : ℤ) ^ s) - 5257224) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (64512*G*((2 : ℤ) ^ s)^2 - 4608*G*((2 : ℤ) ^ s) - 32832*G + 1376256*((2 : ℤ) ^ s)^4 - 109824*((2 : ℤ) ^ s)^3 - 549120*((2 : ℤ) ^ s)^2 - 7968*((2 : ℤ) ^ s) - 77976) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (10368*((2 : ℤ) ^ s)^2 - 3456*((2 : ℤ) ^ s) - 864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-248832*G^2*((2 : ℤ) ^ s) - 981504*G^2 - 5308416*G*((2 : ℤ) ^ s)^3 - 20874240*G*((2 : ℤ) ^ s)^2 - 654336*G*((2 : ℤ) ^ s) - 4643136*G - 113246208*((2 : ℤ) ^ s)^5 - 445317120*((2 : ℤ) ^ s)^4 - 1572864*((2 : ℤ) ^ s)^3 - 50163840*((2 : ℤ) ^ s)^2 - 157296*((2 : ℤ) ^ s) - 5491152) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (82944*G*((2 : ℤ) ^ s)^2 - 29952*G*((2 : ℤ) ^ s) - 24192*G + 1769472*((2 : ℤ) ^ s)^4 - 668928*((2 : ℤ) ^ s)^3 - 312192*((2 : ℤ) ^ s)^2 - 64320*((2 : ℤ) ^ s) - 57456) * hG

@[expose] def action {s : ℕ} {i F G : ℤ} (h : Data s i F G) : SigmaFourAction (k s) :=
  SigmaFourAction.ofMatEq (uvM s i F G) (tM s i F G) (uM s i F G) ρM
    (compat_uv h) (compat_t h) (compat_u h) (compat_rho h)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

@[expose] def actionPaper (s : ℕ) : SigmaFourAction (k s) := action (data s)

end Type230

namespace Type231

@[expose] def k (s : ℕ) : Fin 3 → ℕ := ![s + 2, s + 4, s + 4]

structure Data (s : ℕ) (i F G : ℤ) : Prop where
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hG : 3 * G + 7 = 64 * (((2 : ℤ) ^ s)) ^ 2
  hs : ∀ r, (2 : ℤ) ^ k s r ∣ 3 * G + 7

theorem data (s : ℕ) : Data s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) where
  hi := iV_eq_eight_GV_add_nineteen s
  hF := FV_eq_four_GV_add_nine s
  hG := three_mul_GV_add_seven s
  hs := by
    intro r
    rw [three_mul_GV_add_seven s, sixty_four_mul_pow_two_sq s]
    fin_cases r <;> simp [k] <;> exact pow_dvd_pow 2 (by omega)

@[expose] def ρM : IntMat := ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1]

@[expose] def uvA (s : ℕ) (i F G : ℤ) : Fin 3 → ℤ := ![2 * ((2 : ℤ) ^ s) + F * i, -5 * i + 8 * ((2 : ℤ) ^ s), 2 * i + 4 * ((2 : ℤ) ^ s)]

@[expose] def tM (s : ℕ) (i F G : ℤ) : IntMat :=
  ofCols ![4 - i, 4, 8 + 8 * ((2 : ℤ) ^ s)] ![2 * ((2 : ℤ) ^ s) + 2 * G * i, -7 * i + 4 * ((2 : ℤ) ^ s), -8 * i + 8 * ((2 : ℤ) ^ s)] (ρM *ᵥ uvA s i F G)

@[expose] def uvM (s : ℕ) (i F G : ℤ) : IntMat :=
  ofCols ![-i, 4 + 8 * ((2 : ℤ) ^ s), -4] (uvA s i F G) (ρM *ᵥ (tM s i F G *ᵥ uvA s i F G))

@[expose] def uM (s : ℕ) (i F G : ℤ) : IntMat := uMat ![-1 + 2 * ((2 : ℤ) ^ s), 0, 0] (-2 * F + 2 * ((2 : ℤ) ^ s))

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (uvM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-8*G - 19, 128*G^2 + 592*G + 8*((2 : ℤ) ^ s) + 684, -1536*G^3 - 13184*G^2 + 2048*G*((2 : ℤ) ^ s) - 36568*G - 352*((2 : ℤ) ^ s)^2 + 4832*((2 : ℤ) ^ s) - 33060; 2*((2 : ℤ) ^ s) + 1, -40*G + 8*((2 : ℤ) ^ s) - 95, -256*G^2*((2 : ℤ) ^ s) - 1920*G^2 - 192*G*((2 : ℤ) ^ s) - 9088*G - 96*((2 : ℤ) ^ s)^2 + 972*((2 : ℤ) ^ s) - 10754; -1, 16*G + 4*((2 : ℤ) ^ s) + 38, -256*G^2*((2 : ℤ) ^ s) + 192*G^2 - 928*G*((2 : ℤ) ^ s) + 928*G - 80*((2 : ℤ) ^ s)^2 - 768*((2 : ℤ) ^ s) + 1121]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_t {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (tM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![-8*G - 15, 64*G^2 + 152*G + 8*((2 : ℤ) ^ s), 128*G^2 + 528*G - 8*((2 : ℤ) ^ s) + 532; 1, -56*G + 4*((2 : ℤ) ^ s) - 133, -16*G - 4*((2 : ℤ) ^ s) - 38; 2*((2 : ℤ) ^ s) + 2, -64*G + 8*((2 : ℤ) ^ s) - 152, -56*G + 4*((2 : ℤ) ^ s) - 133]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) (uM s i F G) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![2*((2 : ℤ) ^ s) - 1, -32*G + 8*((2 : ℤ) ^ s) - 72, 64*G*((2 : ℤ) ^ s) - 32*G - 16*((2 : ℤ) ^ s)^2 + 152*((2 : ℤ) ^ s) - 72; 0, 0, 1; 0, 1, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem compat_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) : Compat (k s) ρM := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;> simp [pow_add] <;> norm_num <;> ring

theorem uv_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uvM s i F G) * (uvM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 4) (P := !![301989888*((2 : ℤ) ^ s)^5 + 2359296*((2 : ℤ) ^ s)^4 + 24182784*((2 : ℤ) ^ s)^3 - 889344*((2 : ℤ) ^ s)^2 + 63900*((2 : ℤ) ^ s) - 936, -25769803776*((2 : ℤ) ^ s)^7 - 301989888*((2 : ℤ) ^ s)^6 - 2264924160*((2 : ℤ) ^ s)^5 + 55443456*((2 : ℤ) ^ s)^4 - 8275968*((2 : ℤ) ^ s)^3 + 129960*((2 : ℤ) ^ s)^2 - 8040*((2 : ℤ) ^ s) + 54, 8796093022208*((2 : ℤ) ^ s)^10 - 6597069766656*((2 : ℤ) ^ s)^9 + 188978561024*((2 : ℤ) ^ s)^8 - 805709021184*((2 : ℤ) ^ s)^7 - 4590665728*((2 : ℤ) ^ s)^6 - 2967994368*((2 : ℤ) ^ s)^5 - 30126080*((2 : ℤ) ^ s)^4 - 4998432*((2 : ℤ) ^ s)^3 - 8528*((2 : ℤ) ^ s)^2 - 3978*((2 : ℤ) ^ s) + 16; 2359296*((2 : ℤ) ^ s)^4 + 17694720*((2 : ℤ) ^ s)^3 - 474624*((2 : ℤ) ^ s)^2 + 36828*((2 : ℤ) ^ s) - 450, -201326592*((2 : ℤ) ^ s)^6 - 1512308736*((2 : ℤ) ^ s)^5 + 19464192*((2 : ℤ) ^ s)^4 - 3419136*((2 : ℤ) ^ s)^3 - 10008*((2 : ℤ) ^ s)^2 + 1764*((2 : ℤ) ^ s) - 51, 68719476736*((2 : ℤ) ^ s)^9 + 463856467968*((2 : ℤ) ^ s)^8 - 402518966272*((2 : ℤ) ^ s)^7 - 14039384064*((2 : ℤ) ^ s)^6 + 376700928*((2 : ℤ) ^ s)^5 - 157704192*((2 : ℤ) ^ s)^4 + 2496992*((2 : ℤ) ^ s)^3 - 139032*((2 : ℤ) ^ s)^2 - 1742*((2 : ℤ) ^ s) + 51; 2359296*((2 : ℤ) ^ s)^4 - 1769472*((2 : ℤ) ^ s)^3 - 101376*((2 : ℤ) ^ s)^2 - 1674*((2 : ℤ) ^ s) + 36, -201326592*((2 : ℤ) ^ s)^6 + 148635648*((2 : ℤ) ^ s)^5 + 11206656*((2 : ℤ) ^ s)^4 - 317952*((2 : ℤ) ^ s)^3 + 34092*((2 : ℤ) ^ s)^2 - 1188*((2 : ℤ) ^ s) - 15, 68719476736*((2 : ℤ) ^ s)^9 - 103079215104*((2 : ℤ) ^ s)^8 + 31943819264*((2 : ℤ) ^ s)^7 + 4120903680*((2 : ℤ) ^ s)^6 - 743964672*((2 : ℤ) ^ s)^5 + 55554048*((2 : ℤ) ^ s)^4 + 1131152*((2 : ℤ) ^ s)^3 - 81624*((2 : ℤ) ^ s)^2 + 9595*((2 : ℤ) ^ s) - 186]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 4)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (41472*G^2 + 884736*G*((2 : ℤ) ^ s)^2 + 6912*G*((2 : ℤ) ^ s) + 264384*G + 18874368*((2 : ℤ) ^ s)^4 + 147456*((2 : ℤ) ^ s)^3 + 3575808*((2 : ℤ) ^ s)^2 - 39456*((2 : ℤ) ^ s) + 394632) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-165888*G^3 - 3538944*G^2*((2 : ℤ) ^ s)^2 - 41472*G^2*((2 : ℤ) ^ s) - 1472256*G^2 - 75497472*G*((2 : ℤ) ^ s)^4 - 884736*G*((2 : ℤ) ^ s)^3 - 23150592*G*((2 : ℤ) ^ s)^2 - 31104*G*((2 : ℤ) ^ s) - 4186080*G - 1610612736*((2 : ℤ) ^ s)^6 - 18874368*((2 : ℤ) ^ s)^5 - 317718528*((2 : ℤ) ^ s)^4 + 1400832*((2 : ℤ) ^ s)^3 - 35267712*((2 : ℤ) ^ s)^2 + 161784*((2 : ℤ) ^ s) - 3859812) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (2654208*G^4*((2 : ℤ) ^ s) - 1990656*G^4 + 56623104*G^3*((2 : ℤ) ^ s)^3 - 42467328*G^3*((2 : ℤ) ^ s)^2 + 25989120*G^3*((2 : ℤ) ^ s) - 23639040*G^3 + 1207959552*G^2*((2 : ℤ) ^ s)^5 - 905969664*G^2*((2 : ℤ) ^ s)^4 + 422313984*G^2*((2 : ℤ) ^ s)^3 - 407918592*G^2*((2 : ℤ) ^ s)^2 + 94560768*G^2*((2 : ℤ) ^ s) - 101056896*G^2 + 25769803776*G*((2 : ℤ) ^ s)^7 - 19327352832*G*((2 : ℤ) ^ s)^6 + 6190792704*G*((2 : ℤ) ^ s)^5 - 6588334080*G*((2 : ℤ) ^ s)^4 + 1032505344*G*((2 : ℤ) ^ s)^3 - 1218682368*G*((2 : ℤ) ^ s)^2 + 151660992*G*((2 : ℤ) ^ s) - 186674544*G + 549755813888*((2 : ℤ) ^ s)^9 - 412316860416*((2 : ℤ) ^ s)^8 + 71940702208*((2 : ℤ) ^ s)^7 - 95453970432*((2 : ℤ) ^ s)^6 + 7581597696*((2 : ℤ) ^ s)^5 - 10625777664*((2 : ℤ) ^ s)^4 + 827354368*((2 : ℤ) ^ s)^3 - 1162515744*((2 : ℤ) ^ s)^2 + 90528368*((2 : ℤ) ^ s) - 126672012) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (27648*G*((2 : ℤ) ^ s) + 207360*G + 589824*((2 : ℤ) ^ s)^3 + 4423680*((2 : ℤ) ^ s)^2 - 54144*((2 : ℤ) ^ s) + 492480) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-110592*G^2*((2 : ℤ) ^ s) - 829440*G^2 - 2359296*G*((2 : ℤ) ^ s)^3 - 17722368*G*((2 : ℤ) ^ s)^2 - 288000*G*((2 : ℤ) ^ s) - 3913920*G - 50331648*((2 : ℤ) ^ s)^5 - 378077184*((2 : ℤ) ^ s)^4 - 638976*((2 : ℤ) ^ s)^3 - 42206976*((2 : ℤ) ^ s)^2 - 71904*((2 : ℤ) ^ s) - 4616352) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (1769472*G^3*((2 : ℤ) ^ s)^2 + 11943936*G^3*((2 : ℤ) ^ s) - 9953280*G^3 + 37748736*G^2*((2 : ℤ) ^ s)^4 + 254803968*G^2*((2 : ℤ) ^ s)^3 - 208723968*G^2*((2 : ℤ) ^ s)^2 + 75838464*G^2*((2 : ℤ) ^ s) - 69963264*G^2 + 805306368*G*((2 : ℤ) ^ s)^6 + 5435817984*G*((2 : ℤ) ^ s)^5 - 4540858368*G*((2 : ℤ) ^ s)^4 + 1024561152*G*((2 : ℤ) ^ s)^3 - 998532096*G*((2 : ℤ) ^ s)^2 + 157114368*G*((2 : ℤ) ^ s) - 163938816*G + 17179869184*((2 : ℤ) ^ s)^8 + 115964116992*((2 : ℤ) ^ s)^7 - 98750693376*((2 : ℤ) ^ s)^6 + 9173729280*((2 : ℤ) ^ s)^5 - 10706681856*((2 : ℤ) ^ s)^4 + 963950592*((2 : ℤ) ^ s)^3 - 1170428800*((2 : ℤ) ^ s)^2 + 105404304*((2 : ℤ) ^ s) - 128057112) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (27648*G*((2 : ℤ) ^ s) - 20736*G + 589824*((2 : ℤ) ^ s)^3 - 442368*((2 : ℤ) ^ s)^2 + 39168*((2 : ℤ) ^ s) - 49248) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-110592*G^2*((2 : ℤ) ^ s) + 82944*G^2 - 2359296*G*((2 : ℤ) ^ s)^3 + 1741824*G*((2 : ℤ) ^ s)^2 - 384768*G*((2 : ℤ) ^ s) + 383616*G - 50331648*((2 : ℤ) ^ s)^5 + 37158912*((2 : ℤ) ^ s)^4 - 2703360*((2 : ℤ) ^ s)^3 + 3984768*((2 : ℤ) ^ s)^2 - 286752*((2 : ℤ) ^ s) + 443232) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (1769472*G^3*((2 : ℤ) ^ s)^2 - 2654208*G^3*((2 : ℤ) ^ s) + 995328*G^3 + 37748736*G^2*((2 : ℤ) ^ s)^4 - 56623104*G^2*((2 : ℤ) ^ s)^3 + 29933568*G^2*((2 : ℤ) ^ s)^2 - 16367616*G^2*((2 : ℤ) ^ s) + 6511104*G^2 + 805306368*G*((2 : ℤ) ^ s)^6 - 1207959552*G*((2 : ℤ) ^ s)^5 + 550502400*G*((2 : ℤ) ^ s)^4 - 215949312*G*((2 : ℤ) ^ s)^3 + 102070272*G*((2 : ℤ) ^ s)^2 - 32325120*G*((2 : ℤ) ^ s) + 14141952*G + 17179869184*((2 : ℤ) ^ s)^8 - 25769803776*((2 : ℤ) ^ s)^7 + 9865003008*((2 : ℤ) ^ s)^6 - 1788346368*((2 : ℤ) ^ s)^5 + 892993536*((2 : ℤ) ^ s)^4 - 181711872*((2 : ℤ) ^ s)^3 + 97945856*((2 : ℤ) ^ s)^2 - 20050176*((2 : ℤ) ^ s) + 10194984) * hG
theorem t_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((tM s i F G) * (tM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 2) (P := !![262144*((2 : ℤ) ^ s)^4 + 393216*((2 : ℤ) ^ s)^3 - 6656*((2 : ℤ) ^ s)^2 - 16548*((2 : ℤ) ^ s) - 32, -67108864*((2 : ℤ) ^ s)^5 + 327680*((2 : ℤ) ^ s)^4 + 3473408*((2 : ℤ) ^ s)^3 - 13696*((2 : ℤ) ^ s)^2 + 7022*((2 : ℤ) ^ s) - 10, -50331648*((2 : ℤ) ^ s)^5 + 65536*((2 : ℤ) ^ s)^4 + 1769472*((2 : ℤ) ^ s)^3 + 8320*((2 : ℤ) ^ s)^2 + 3612*((2 : ℤ) ^ s) - 2; -1536*((2 : ℤ) ^ s)^2 - 4626*((2 : ℤ) ^ s) - 12, 1081344*((2 : ℤ) ^ s)^3 - 3840*((2 : ℤ) ^ s)^2 + 2391*((2 : ℤ) ^ s) - 3, 491520*((2 : ℤ) ^ s)^3 + 3840*((2 : ℤ) ^ s)^2 + 942*((2 : ℤ) ^ s) + 3; -6144*((2 : ℤ) ^ s)^2 - 9198*((2 : ℤ) ^ s) + 42, 32768*((2 : ℤ) ^ s)^4 + 1867776*((2 : ℤ) ^ s)^3 - 20416*((2 : ℤ) ^ s)^2 + 3693*((2 : ℤ) ^ s) - 31, 65536*((2 : ℤ) ^ s)^4 + 1130496*((2 : ℤ) ^ s)^3 - 5504*((2 : ℤ) ^ s)^2 + 2478*((2 : ℤ) ^ s) - 20]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 2)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (768*G*((2 : ℤ) ^ s) + 1152*G + 16384*((2 : ℤ) ^ s)^3 + 24576*((2 : ℤ) ^ s)^2 + 1376*((2 : ℤ) ^ s) + 1656) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-9216*G^2 - 196608*G*((2 : ℤ) ^ s)^2 + 960*G*((2 : ℤ) ^ s) - 32832*G - 4194304*((2 : ℤ) ^ s)^4 + 20480*((2 : ℤ) ^ s)^3 - 241664*((2 : ℤ) ^ s)^2 + 1384*((2 : ℤ) ^ s) - 25992) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-6912*G^2 - 147456*G*((2 : ℤ) ^ s)^2 + 192*G*((2 : ℤ) ^ s) - 27072*G - 3145728*((2 : ℤ) ^ s)^4 + 4096*((2 : ℤ) ^ s)^3 - 233472*((2 : ℤ) ^ s)^2 + 968*((2 : ℤ) ^ s) - 25308) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-384*((2 : ℤ) ^ s) - 1152) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (12672*G + 270336*((2 : ℤ) ^ s)^2 - 960*((2 : ℤ) ^ s) + 30168) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (5760*G + 122880*((2 : ℤ) ^ s)^2 + 960*((2 : ℤ) ^ s) + 13680) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1536*((2 : ℤ) ^ s) - 2304) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (384*G*((2 : ℤ) ^ s) + 21888*G + 8192*((2 : ℤ) ^ s)^3 + 466944*((2 : ℤ) ^ s)^2 - 4208*((2 : ℤ) ^ s) + 51984) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (768*G*((2 : ℤ) ^ s) + 13248*G + 16384*((2 : ℤ) ^ s)^3 + 282624*((2 : ℤ) ^ s)^2 + 416*((2 : ℤ) ^ s) + 31536) * hG
theorem uv_comm_t {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((tM s i F G) * (uvM s i F G)) ((uvM s i F G) * (tM s i F G)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![201326592*((2 : ℤ) ^ s)^6 + 201326592*((2 : ℤ) ^ s)^5 + 15335424*((2 : ℤ) ^ s)^4 + 13762560*((2 : ℤ) ^ s)^3 - 589680*((2 : ℤ) ^ s)^2 + 31404*((2 : ℤ) ^ s) - 732, -34359738368*((2 : ℤ) ^ s)^7 + 201326592*((2 : ℤ) ^ s)^6 - 2516582400*((2 : ℤ) ^ s)^5 + 115998720*((2 : ℤ) ^ s)^4 - 9658368*((2 : ℤ) ^ s)^3 + 310416*((2 : ℤ) ^ s)^2 - 9088*((2 : ℤ) ^ s) + 210, -17179869184*((2 : ℤ) ^ s)^8 - 60129542144*((2 : ℤ) ^ s)^7 + 2617245696*((2 : ℤ) ^ s)^6 + 2302672896*((2 : ℤ) ^ s)^5 - 53280768*((2 : ℤ) ^ s)^4 + 5028864*((2 : ℤ) ^ s)^3 + 109168*((2 : ℤ) ^ s)^2 - 1624*((2 : ℤ) ^ s) + 216; 1572864*((2 : ℤ) ^ s)^5 + 13369344*((2 : ℤ) ^ s)^4 + 11507712*((2 : ℤ) ^ s)^3 - 264432*((2 : ℤ) ^ s)^2 + 37860*((2 : ℤ) ^ s) - 408, -268435456*((2 : ℤ) ^ s)^6 - 2011693056*((2 : ℤ) ^ s)^5 + 60456960*((2 : ℤ) ^ s)^4 - 10881024*((2 : ℤ) ^ s)^3 + 200784*((2 : ℤ) ^ s)^2 - 13416*((2 : ℤ) ^ s) + 157, 67108864*((2 : ℤ) ^ s)^6 - 74711040*((2 : ℤ) ^ s)^5 - 3932160*((2 : ℤ) ^ s)^4 - 2941440*((2 : ℤ) ^ s)^3 + 65052*((2 : ℤ) ^ s)^2 - 5919*((2 : ℤ) ^ s) + 101; 1572864*((2 : ℤ) ^ s)^5 + 393216*((2 : ℤ) ^ s)^4 - 1256448*((2 : ℤ) ^ s)^3 - 105672*((2 : ℤ) ^ s)^2 - 14988*((2 : ℤ) ^ s) - 102, -268435456*((2 : ℤ) ^ s)^6 + 202899456*((2 : ℤ) ^ s)^5 + 11599872*((2 : ℤ) ^ s)^4 + 3916800*((2 : ℤ) ^ s)^3 - 4680*((2 : ℤ) ^ s)^2 + 7119*((2 : ℤ) ^ s) - 17, 218103808*((2 : ℤ) ^ s)^6 + 1961361408*((2 : ℤ) ^ s)^5 - 64290816*((2 : ℤ) ^ s)^4 + 7440384*((2 : ℤ) ^ s)^3 - 53364*((2 : ℤ) ^ s)^2 + 5565*((2 : ℤ) ^ s) + 26]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (27648*G^2*((2 : ℤ) ^ s) + 27648*G^2 + 589824*G*((2 : ℤ) ^ s)^3 + 589824*G*((2 : ℤ) ^ s)^2 + 173952*G*((2 : ℤ) ^ s) + 171072*G + 12582912*((2 : ℤ) ^ s)^5 + 12582912*((2 : ℤ) ^ s)^4 + 2334720*((2 : ℤ) ^ s)^3 + 2236416*((2 : ℤ) ^ s)^2 + 218208*((2 : ℤ) ^ s) + 250344) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-221184*G^3 - 4718592*G^2*((2 : ℤ) ^ s)^2 + 27648*G^2*((2 : ℤ) ^ s) - 1893888*G^2 - 100663296*G*((2 : ℤ) ^ s)^4 + 589824*G*((2 : ℤ) ^ s)^3 - 29392896*G*((2 : ℤ) ^ s)^2 + 468864*G*((2 : ℤ) ^ s) - 5249664*G - 2147483648*((2 : ℤ) ^ s)^6 + 12582912*((2 : ℤ) ^ s)^5 - 392167424*((2 : ℤ) ^ s)^4 + 8626176*((2 : ℤ) ^ s)^3 - 43496960*((2 : ℤ) ^ s)^2 + 962592*((2 : ℤ) ^ s) - 4748328) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-110592*G^3*((2 : ℤ) ^ s) - 387072*G^3 - 2359296*G^2*((2 : ℤ) ^ s)^3 - 8257536*G^2*((2 : ℤ) ^ s)^2 - 414720*G^2*((2 : ℤ) ^ s) - 2391552*G^2 - 50331648*G*((2 : ℤ) ^ s)^5 - 176160768*G*((2 : ℤ) ^ s)^4 - 3342336*G*((2 : ℤ) ^ s)^3 - 31789056*G*((2 : ℤ) ^ s)^2 - 285120*G*((2 : ℤ) ^ s) - 4823712*G - 1073741824*((2 : ℤ) ^ s)^7 - 3758096384*((2 : ℤ) ^ s)^6 + 46137344*((2 : ℤ) ^ s)^5 - 267124736*((2 : ℤ) ^ s)^4 + 1716224*((2 : ℤ) ^ s)^3 - 28902464*((2 : ℤ) ^ s)^2 + 194400*((2 : ℤ) ^ s) - 3151872) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (18432*G*((2 : ℤ) ^ s)^2 + 156672*G*((2 : ℤ) ^ s) + 138240*G + 393216*((2 : ℤ) ^ s)^4 + 3342336*((2 : ℤ) ^ s)^3 + 2919936*((2 : ℤ) ^ s)^2 + 299136*((2 : ℤ) ^ s) + 331776) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-147456*G^2*((2 : ℤ) ^ s) - 1105920*G^2 - 3145728*G*((2 : ℤ) ^ s)^3 - 23574528*G*((2 : ℤ) ^ s)^2 + 20352*G*((2 : ℤ) ^ s) - 5282496*G - 67108864*((2 : ℤ) ^ s)^5 - 502923264*((2 : ℤ) ^ s)^4 + 7774208*((2 : ℤ) ^ s)^3 - 57727488*((2 : ℤ) ^ s)^2 + 900176*((2 : ℤ) ^ s) - 6307848) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (36864*G^2*((2 : ℤ) ^ s) - 41472*G^2 + 786432*G*((2 : ℤ) ^ s)^3 - 875520*G*((2 : ℤ) ^ s)^2 + 125952*G*((2 : ℤ) ^ s) - 228096*G + 16777216*((2 : ℤ) ^ s)^5 - 18677760*((2 : ℤ) ^ s)^4 + 851968*((2 : ℤ) ^ s)^3 - 2778240*((2 : ℤ) ^ s)^2 + 109312*((2 : ℤ) ^ s) - 307800) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (18432*G*((2 : ℤ) ^ s)^2 + 4608*G*((2 : ℤ) ^ s) - 13824*G + 393216*((2 : ℤ) ^ s)^4 + 98304*((2 : ℤ) ^ s)^3 - 271104*((2 : ℤ) ^ s)^2 - 15936*((2 : ℤ) ^ s) - 36288) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-147456*G^2*((2 : ℤ) ^ s) + 110592*G^2 - 3145728*G*((2 : ℤ) ^ s)^3 + 2377728*G*((2 : ℤ) ^ s)^2 - 552192*G*((2 : ℤ) ^ s) + 565056*G - 67108864*((2 : ℤ) ^ s)^5 + 50724864*((2 : ℤ) ^ s)^4 - 4440064*((2 : ℤ) ^ s)^3 + 6527232*((2 : ℤ) ^ s)^2 - 487072*((2 : ℤ) ^ s) + 718200) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (119808*G^2*((2 : ℤ) ^ s) + 1078272*G^2 + 2555904*G*((2 : ℤ) ^ s)^3 + 22984704*G*((2 : ℤ) ^ s)^2 - 194304*G*((2 : ℤ) ^ s) + 5111424*G + 54525952*((2 : ℤ) ^ s)^5 + 490340352*((2 : ℤ) ^ s)^4 - 10108928*((2 : ℤ) ^ s)^3 + 55491072*((2 : ℤ) ^ s)^2 - 1118384*((2 : ℤ) ^ s) + 6057504) * hG
theorem rho_cube {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 0) (P := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 0)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem u_sq {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (uM s i F G)) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 1) (P := !![3*((2 : ℤ) ^ s) - 3, 0, 512*((2 : ℤ) ^ s)^3 - 518*((2 : ℤ) ^ s)^2 + 4*((2 : ℤ) ^ s) + 2; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 1)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (32*((2 : ℤ) ^ s)^2 - 32*((2 : ℤ) ^ s)) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem u_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * ((uM s i F G) * (ρM * (uM s i F G)))) (1) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 1) (P := !![3*((2 : ℤ) ^ s) - 3, -512*((2 : ℤ) ^ s)^2 + 390*((2 : ℤ) ^ s) - 4, 512*((2 : ℤ) ^ s)^3 - 262*((2 : ℤ) ^ s)^2 + ((2 : ℤ) ^ s) + 1; 0, 0, 0; 0, 0, 0]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 1)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (24 - 32*((2 : ℤ) ^ s)) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (32*((2 : ℤ) ^ s)^2 - 16*((2 : ℤ) ^ s)) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
theorem uv_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (uvM s i F G)) ((tM s i F G) * ρM) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 2) (P := !![0, 0, -8388608*((2 : ℤ) ^ s)^5 + 262144*((2 : ℤ) ^ s)^4 - 770048*((2 : ℤ) ^ s)^3 + 11776*((2 : ℤ) ^ s)^2 - 6098*((2 : ℤ) ^ s) + 22; 0, 0, 65536*((2 : ℤ) ^ s)^4 - 49152*((2 : ℤ) ^ s)^3 - 3200*((2 : ℤ) ^ s)^2 - 1203*((2 : ℤ) ^ s) - 2; 0, 0, -540672*((2 : ℤ) ^ s)^3 + 8832*((2 : ℤ) ^ s)^2 - 3369*((2 : ℤ) ^ s) + 24]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 2)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-1152*G^2 - 24576*G*((2 : ℤ) ^ s)^2 + 768*G*((2 : ℤ) ^ s) - 7632*G - 524288*((2 : ℤ) ^ s)^4 + 16384*((2 : ℤ) ^ s)^3 - 105472*((2 : ℤ) ^ s)^2 + 2528*((2 : ℤ) ^ s) - 11916) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (768*G*((2 : ℤ) ^ s) - 576*G + 16384*((2 : ℤ) ^ s)^3 - 12288*((2 : ℤ) ^ s)^2 + 992*((2 : ℤ) ^ s) - 1656) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-6336*G - 135168*((2 : ℤ) ^ s)^2 + 2208*((2 : ℤ) ^ s) - 15624) * hG
theorem t_rho {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) (ρM * (tM s i F G)) ((tM s i F G) * ((uvM s i F G) * ρM)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![-393216*((2 : ℤ) ^ s)^4 + 42240*((2 : ℤ) ^ s)^2 + 13716*((2 : ℤ) ^ s) - 78, 17179869184*((2 : ℤ) ^ s)^8 + 30064771072*((2 : ℤ) ^ s)^7 - 2516582400*((2 : ℤ) ^ s)^6 - 4542431232*((2 : ℤ) ^ s)^5 + 149225472*((2 : ℤ) ^ s)^4 - 16355328*((2 : ℤ) ^ s)^3 + 193112*((2 : ℤ) ^ s)^2 - 11908*((2 : ℤ) ^ s) - 36, -17179869184*((2 : ℤ) ^ s)^8 - 30064771072*((2 : ℤ) ^ s)^7 + 2516582400*((2 : ℤ) ^ s)^6 + 4517265408*((2 : ℤ) ^ s)^5 - 148045824*((2 : ℤ) ^ s)^4 + 20533248*((2 : ℤ) ^ s)^3 - 306008*((2 : ℤ) ^ s)^2 + 20326*((2 : ℤ) ^ s) - 108; 16128*((2 : ℤ) ^ s)^2 + 6858*((2 : ℤ) ^ s) - 36, -301989888*((2 : ℤ) ^ s)^6 - 1686110208*((2 : ℤ) ^ s)^5 + 52297728*((2 : ℤ) ^ s)^4 - 6931968*((2 : ℤ) ^ s)^3 + 94956*((2 : ℤ) ^ s)^2 - 6459*((2 : ℤ) ^ s) + 24, 301989888*((2 : ℤ) ^ s)^6 + 1686110208*((2 : ℤ) ^ s)^5 - 52297728*((2 : ℤ) ^ s)^4 + 8553984*((2 : ℤ) ^ s)^3 - 137580*((2 : ℤ) ^ s)^2 + 9708*((2 : ℤ) ^ s) - 60; 20736*((2 : ℤ) ^ s)^2 + 3348*((2 : ℤ) ^ s), -452984832*((2 : ℤ) ^ s)^6 - 1784414208*((2 : ℤ) ^ s)^5 + 74711040*((2 : ℤ) ^ s)^4 - 5624832*((2 : ℤ) ^ s)^3 + 83472*((2 : ℤ) ^ s)^2 - 2613*((2 : ℤ) ^ s) - 30, 452984832*((2 : ℤ) ^ s)^6 + 1784414208*((2 : ℤ) ^ s)^5 - 74514432*((2 : ℤ) ^ s)^4 + 7099392*((2 : ℤ) ^ s)^3 - 140304*((2 : ℤ) ^ s)^2 + 5763*((2 : ℤ) ^ s) - 48]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1152*G*((2 : ℤ) ^ s) - 24576*((2 : ℤ) ^ s)^3 - 48*((2 : ℤ) ^ s) + 864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (110592*G^3*((2 : ℤ) ^ s) + 193536*G^3 + 2359296*G^2*((2 : ℤ) ^ s)^3 + 4128768*G^2*((2 : ℤ) ^ s)^2 + 428544*G^2*((2 : ℤ) ^ s) + 729216*G^2 + 50331648*G*((2 : ℤ) ^ s)^5 + 88080384*G*((2 : ℤ) ^ s)^4 + 3637248*G*((2 : ℤ) ^ s)^3 + 5959680*G*((2 : ℤ) ^ s)^2 + 630720*G*((2 : ℤ) ^ s) + 196992*G + 1073741824*((2 : ℤ) ^ s)^7 + 1879048192*((2 : ℤ) ^ s)^6 - 39845888*((2 : ℤ) ^ s)^5 - 78381056*((2 : ℤ) ^ s)^4 + 4968448*((2 : ℤ) ^ s)^3 - 9595136*((2 : ℤ) ^ s)^2 + 555480*((2 : ℤ) ^ s) - 1052676) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-110592*G^3*((2 : ℤ) ^ s) - 193536*G^3 - 2359296*G^2*((2 : ℤ) ^ s)^3 - 4128768*G^2*((2 : ℤ) ^ s)^2 - 428544*G^2*((2 : ℤ) ^ s) - 732672*G^2 - 50331648*G*((2 : ℤ) ^ s)^5 - 88080384*G*((2 : ℤ) ^ s)^4 - 3637248*G*((2 : ℤ) ^ s)^3 - 6033408*G*((2 : ℤ) ^ s)^2 - 627264*G*((2 : ℤ) ^ s) - 200880*G - 1073741824*((2 : ℤ) ^ s)^7 - 1879048192*((2 : ℤ) ^ s)^6 + 39845888*((2 : ℤ) ^ s)^5 + 76808192*((2 : ℤ) ^ s)^4 - 4894720*((2 : ℤ) ^ s)^3 + 9684224*((2 : ℤ) ^ s)^2 - 554472*((2 : ℤ) ^ s) + 1062936) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (4032*((2 : ℤ) ^ s) + 1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-165888*G^2*((2 : ℤ) ^ s) - 926208*G^2 - 3538944*G*((2 : ℤ) ^ s)^3 - 19759104*G*((2 : ℤ) ^ s)^2 - 161280*G*((2 : ℤ) ^ s) - 4399488*G - 75497472*((2 : ℤ) ^ s)^5 - 421527552*((2 : ℤ) ^ s)^4 + 4816896*((2 : ℤ) ^ s)^3 - 47837568*((2 : ℤ) ^ s)^2 + 550560*((2 : ℤ) ^ s) - 5224392) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (165888*G^2*((2 : ℤ) ^ s) + 926208*G^2 + 3538944*G*((2 : ℤ) ^ s)^3 + 19759104*G*((2 : ℤ) ^ s)^2 + 161280*G*((2 : ℤ) ^ s) + 4418496*G + 75497472*((2 : ℤ) ^ s)^5 + 421527552*((2 : ℤ) ^ s)^4 - 4816896*((2 : ℤ) ^ s)^3 + 48243072*((2 : ℤ) ^ s)^2 - 561216*((2 : ℤ) ^ s) + 5269536) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (5184*((2 : ℤ) ^ s) + 864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-248832*G^2*((2 : ℤ) ^ s) - 981504*G^2 - 5308416*G*((2 : ℤ) ^ s)^3 - 20911104*G*((2 : ℤ) ^ s)^2 - 285696*G*((2 : ℤ) ^ s) - 4636224*G - 113246208*((2 : ℤ) ^ s)^5 - 446103552*((2 : ℤ) ^ s)^4 + 6291456*((2 : ℤ) ^ s)^3 - 50198784*((2 : ℤ) ^ s)^2 + 708240*((2 : ℤ) ^ s) - 5474736) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (248832*G^2*((2 : ℤ) ^ s) + 981504*G^2 + 5308416*G*((2 : ℤ) ^ s)^3 + 20911104*G*((2 : ℤ) ^ s)^2 + 288000*G*((2 : ℤ) ^ s) + 4653504*G + 113246208*((2 : ℤ) ^ s)^5 + 446103552*((2 : ℤ) ^ s)^4 - 6242304*((2 : ℤ) ^ s)^3 + 50567424*((2 : ℤ) ^ s)^2 - 717072*((2 : ℤ) ^ s) + 5515776) * hG
theorem uv_comm_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (uvM s i F G)) ((uvM s i F G) * (uM s i F G)) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![-18432*((2 : ℤ) ^ s)^2 + 216*((2 : ℤ) ^ s) + 72, 25165824*((2 : ℤ) ^ s)^5 + 983040*((2 : ℤ) ^ s)^4 + 2162688*((2 : ℤ) ^ s)^3 - 94188*((2 : ℤ) ^ s)^2 + 4857*((2 : ℤ) ^ s) - 66, -268435456*((2 : ℤ) ^ s)^7 + 422576128*((2 : ℤ) ^ s)^6 + 939786240*((2 : ℤ) ^ s)^5 - 45754368*((2 : ℤ) ^ s)^4 + 1045104*((2 : ℤ) ^ s)^3 - 28476*((2 : ℤ) ^ s)^2 - 2468*((2 : ℤ) ^ s) + 5; -27*((2 : ℤ) ^ s), 196608*((2 : ℤ) ^ s)^4 + 1474560*((2 : ℤ) ^ s)^3 - 33792*((2 : ℤ) ^ s)^2 + 6471*((2 : ℤ) ^ s) - 60, -196608*((2 : ℤ) ^ s)^4 + 142848*((2 : ℤ) ^ s)^3 + 9654*((2 : ℤ) ^ s)^2 + 3627*((2 : ℤ) ^ s) - 21; 27, 196608*((2 : ℤ) ^ s)^4 - 147456*((2 : ℤ) ^ s)^3 - 9600*((2 : ℤ) ^ s)^2 - 3609*((2 : ℤ) ^ s) + 21, -196608*((2 : ℤ) ^ s)^4 - 1474560*((2 : ℤ) ^ s)^3 + 38400*((2 : ℤ) ^ s)^2 - 6525*((2 : ℤ) ^ s) + 42]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-1152*((2 : ℤ) ^ s)) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (3456*G^2 + 73728*G*((2 : ℤ) ^ s)^2 + 2880*G*((2 : ℤ) ^ s) + 22464*G + 1572864*((2 : ℤ) ^ s)^4 + 61440*((2 : ℤ) ^ s)^3 + 307200*((2 : ℤ) ^ s)^2 + 840*((2 : ℤ) ^ s) + 33858) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-36864*G^2*((2 : ℤ) ^ s)^2 + 57600*G^2*((2 : ℤ) ^ s) + 127872*G^2 - 786432*G*((2 : ℤ) ^ s)^4 + 1238016*G*((2 : ℤ) ^ s)^3 + 2581248*G*((2 : ℤ) ^ s)^2 + 135744*G*((2 : ℤ) ^ s) + 597888*G - 16777216*((2 : ℤ) ^ s)^6 + 26411008*((2 : ℤ) ^ s)^5 + 56901632*((2 : ℤ) ^ s)^4 + 29056*((2 : ℤ) ^ s)^3 + 6288800*((2 : ℤ) ^ s)^2 + 1540*((2 : ℤ) ^ s) + 698706) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (2304*G*((2 : ℤ) ^ s) + 17280*G + 49152*((2 : ℤ) ^ s)^3 + 368640*((2 : ℤ) ^ s)^2 - 3072*((2 : ℤ) ^ s) + 41904) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-2304*G*((2 : ℤ) ^ s) + 1728*G - 49152*((2 : ℤ) ^ s)^3 + 35712*((2 : ℤ) ^ s)^2 - 2976*((2 : ℤ) ^ s) + 4968) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (0) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (2304*G*((2 : ℤ) ^ s) - 1728*G + 49152*((2 : ℤ) ^ s)^3 - 36864*((2 : ℤ) ^ s)^2 + 2976*((2 : ℤ) ^ s) - 4968) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-2304*G*((2 : ℤ) ^ s) - 17280*G - 49152*((2 : ℤ) ^ s)^3 - 368640*((2 : ℤ) ^ s)^2 + 4224*((2 : ℤ) ^ s) - 41904) * hG
theorem t_u {s : ℕ} {i F G : ℤ} (h : Data s i F G) :
    MatEq (k s) ((uM s i F G) * (tM s i F G)) ((tM s i F G) * ((uvM s i F G) * (uM s i F G))) := by
  obtain ⟨hi, hF, hG, hs⟩ := h
  subst hi hF
  refine MatEq.of_dvd_mul_coprime (c := (3 : ℤ) ^ 3) (P := !![-786432*((2 : ℤ) ^ s)^5 + 393216*((2 : ℤ) ^ s)^4 + 102912*((2 : ℤ) ^ s)^3 - 5808*((2 : ℤ) ^ s)^2 - 27768*((2 : ℤ) ^ s) + 258, 17179869184*((2 : ℤ) ^ s)^8 + 30064771072*((2 : ℤ) ^ s)^7 - 2449473536*((2 : ℤ) ^ s)^6 - 4543217664*((2 : ℤ) ^ s)^5 + 138706944*((2 : ℤ) ^ s)^4 - 15902208*((2 : ℤ) ^ s)^3 + 202088*((2 : ℤ) ^ s)^2 - 11263*((2 : ℤ) ^ s) + 23, -134217728*((2 : ℤ) ^ s)^7 + 68681728*((2 : ℤ) ^ s)^6 + 39321600*((2 : ℤ) ^ s)^5 - 5907456*((2 : ℤ) ^ s)^4 - 4894800*((2 : ℤ) ^ s)^3 + 102444*((2 : ℤ) ^ s)^2 - 9955*((2 : ℤ) ^ s) + 74; 32256*((2 : ℤ) ^ s)^3 - 2412*((2 : ℤ) ^ s)^2 - 6903*((2 : ℤ) ^ s) + 63, -301989888*((2 : ℤ) ^ s)^6 - 1686110208*((2 : ℤ) ^ s)^5 + 49545216*((2 : ℤ) ^ s)^4 - 8070144*((2 : ℤ) ^ s)^3 + 123264*((2 : ℤ) ^ s)^2 - 8844*((2 : ℤ) ^ s) + 63, 5505024*((2 : ℤ) ^ s)^5 - 476160*((2 : ℤ) ^ s)^4 - 2816808*((2 : ℤ) ^ s)^3 + 50358*((2 : ℤ) ^ s)^2 - 5604*((2 : ℤ) ^ s) + 39; 41472*((2 : ℤ) ^ s)^3 - 14040*((2 : ℤ) ^ s)^2 - 3321*((2 : ℤ) ^ s), -452984832*((2 : ℤ) ^ s)^6 - 1784414208*((2 : ℤ) ^ s)^5 + 71172096*((2 : ℤ) ^ s)^4 - 6154752*((2 : ℤ) ^ s)^3 + 101688*((2 : ℤ) ^ s)^2 - 3810*((2 : ℤ) ^ s) + 6, 7077888*((2 : ℤ) ^ s)^5 - 2675712*((2 : ℤ) ^ s)^4 - 2040912*((2 : ℤ) ^ s)^3 + 52098*((2 : ℤ) ^ s)^2 - 4284*((2 : ℤ) ^ s) + 51]) ?_ ?_
  · intro r
    have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
    exact h23.pow (m := k s r) (n := 3)
  · intro r c
    fin_cases r
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (-2304*G*((2 : ℤ) ^ s)^2 + 1152*G*((2 : ℤ) ^ s) - 49152*((2 : ℤ) ^ s)^4 + 24576*((2 : ℤ) ^ s)^3 + 1056*((2 : ℤ) ^ s)^2 + 2352*((2 : ℤ) ^ s) - 1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (110592*G^3*((2 : ℤ) ^ s) + 193536*G^3 + 2359296*G^2*((2 : ℤ) ^ s)^3 + 4128768*G^2*((2 : ℤ) ^ s)^2 + 437760*G^2*((2 : ℤ) ^ s) + 729216*G^2 + 50331648*G*((2 : ℤ) ^ s)^5 + 88080384*G*((2 : ℤ) ^ s)^4 + 3833856*G*((2 : ℤ) ^ s)^3 + 5957376*G*((2 : ℤ) ^ s)^2 + 642912*G*((2 : ℤ) ^ s) + 197856*G + 1073741824*((2 : ℤ) ^ s)^7 + 1879048192*((2 : ℤ) ^ s)^6 - 35651584*((2 : ℤ) ^ s)^5 - 78430208*((2 : ℤ) ^ s)^4 + 4769792*((2 : ℤ) ^ s)^3 - 9572192*((2 : ℤ) ^ s)^2 + 534340*((2 : ℤ) ^ s) - 1050624) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-18432*G^2*((2 : ℤ) ^ s)^2 + 9216*G^2*((2 : ℤ) ^ s) + 3456*G^2 - 393216*G*((2 : ℤ) ^ s)^4 + 201216*G*((2 : ℤ) ^ s)^3 + 29184*G*((2 : ℤ) ^ s)^2 + 26304*G*((2 : ℤ) ^ s) + 1728*G - 8388608*((2 : ℤ) ^ s)^6 + 4292608*((2 : ℤ) ^ s)^5 + 1540096*((2 : ℤ) ^ s)^4 + 100288*((2 : ℤ) ^ s)^3 - 137504*((2 : ℤ) ^ s)^2 + 17608*((2 : ℤ) ^ s) - 15390) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (8064*((2 : ℤ) ^ s)^2 - 576*((2 : ℤ) ^ s) - 1728) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-165888*G^2*((2 : ℤ) ^ s) - 926208*G^2 - 3538944*G*((2 : ℤ) ^ s)^3 - 19759104*G*((2 : ℤ) ^ s)^2 - 193536*G*((2 : ℤ) ^ s) - 4413312*G - 75497472*((2 : ℤ) ^ s)^5 - 421527552*((2 : ℤ) ^ s)^4 + 4128768*((2 : ℤ) ^ s)^3 - 48122112*((2 : ℤ) ^ s)^2 + 482400*((2 : ℤ) ^ s) - 5257224) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (64512*G*((2 : ℤ) ^ s)^2 - 4608*G*((2 : ℤ) ^ s) - 32832*G + 1376256*((2 : ℤ) ^ s)^4 - 119040*((2 : ℤ) ^ s)^3 - 553728*((2 : ℤ) ^ s)^2 + 1824*((2 : ℤ) ^ s) - 77976) * hG
    · fin_cases c
      · simp [pow_add] <;> norm_num <;> linear_combination (10368*((2 : ℤ) ^ s)^2 - 3456*((2 : ℤ) ^ s) - 864) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (-248832*G^2*((2 : ℤ) ^ s) - 981504*G^2 - 5308416*G*((2 : ℤ) ^ s)^3 - 20911104*G*((2 : ℤ) ^ s)^2 - 327168*G*((2 : ℤ) ^ s) - 4643136*G - 113246208*((2 : ℤ) ^ s)^5 - 446103552*((2 : ℤ) ^ s)^4 + 5406720*((2 : ℤ) ^ s)^3 - 50331264*((2 : ℤ) ^ s)^2 + 616080*((2 : ℤ) ^ s) - 5491152) * hG
      · simp [pow_add] <;> norm_num <;> linear_combination (82944*G*((2 : ℤ) ^ s)^2 - 29952*G*((2 : ℤ) ^ s) - 24192*G + 1769472*((2 : ℤ) ^ s)^4 - 668928*((2 : ℤ) ^ s)^3 - 316800*((2 : ℤ) ^ s)^2 - 56832*((2 : ℤ) ^ s) - 57456) * hG

@[expose] def action {s : ℕ} {i F G : ℤ} (h : Data s i F G) : SigmaFourAction (k s) :=
  SigmaFourAction.ofMatEq (uvM s i F G) (tM s i F G) (uM s i F G) ρM
    (compat_uv h) (compat_t h) (compat_u h) (compat_rho h)
    (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h) (u_rho h)
    (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

@[expose] def actionPaper (s : ℕ) : SigmaFourAction (k s) := action (data s)

end Type231

end CFSG.CGT.Stroth77
