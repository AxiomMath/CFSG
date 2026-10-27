module

public import CFSG.CGT.Stroth77.SigmaFour
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type120

@[expose] def iV (n : ℕ) : ℤ := (2 ^ (2 * n + 1) + 1) / 3

@[expose] def FV (n : ℕ) : ℤ := (4 ^ n - 1) / 3

@[expose] def GV (n : ℕ) : ℤ := (4 ^ (n - 1) - 7) / 3

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 1, m + 1]

structure Data (m : ℕ) (i F G : ℤ) : Prop where
  hi : i = 8 * G + 19
  hF : F = 4 * G + 9
  hs : ∀ r, (2 : ℤ) ^ k m r ∣ 3 * G + 7

@[expose] def ρM : IntMat := ofCols ![1, 0, 0] ![0, 0, 1] ![-2, -1, -1]

@[expose] def uvA (i F : ℤ) : Fin 3 → ℤ := ![2 * F * i, -5 * i, 2 * i]

@[expose] def tM (i F G : ℤ) : IntMat :=
  ofCols ![4 - i, 2, 4] ![4 * G * i, -7 * i, -8 * i] (ρM *ᵥ uvA i F)

@[expose] def uvM (i F G : ℤ) : IntMat :=
  ofCols ![-i, 2, -2] (uvA i F) (ρM *ᵥ (tM i F G *ᵥ uvA i F))

@[expose] def uM (F : ℤ) : IntMat := uMat ![-1, 0, 0] (-4 * F)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    Compat (k m) (uvM i F G) := by
  obtain ⟨hi, hF, -⟩ := h
  subst hi hF
  exact Compat.of_witness (C := !![-8*G - 19, 128*G^2 + 592*G + 684, -1536*G^3 - 13184*G^2 - 36568*G - 33060; 1, -40*G - 95, -1920*G^2 - 9088*G - 10754; -1, 16*G + 38, 192*G^2 + 928*G + 1121]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    Compat (k m) (tM i F G) := by
  obtain ⟨hi, hF, -⟩ := h
  subst hi hF
  exact Compat.of_witness (C := !![-8*G - 15, 64*G^2 + 152*G, 128*G^2 + 528*G + 532; 1, -56*G - 133, -16*G - 38; 2, -64*G - 152, -56*G - 133]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    Compat (k m) (uM F) := by
  obtain ⟨hi, hF, -⟩ := h
  subst hi hF
  exact Compat.of_witness (C := !![-1, -32*G - 72, -32*G - 72; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    Compat (k m) (ρM) := by
  obtain ⟨hi, hF, -⟩ := h
  subst hi hF
  exact Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) ((uvM i F G) * (uvM i F G)) (1) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![512*G^2 + 3264*G + 4872, -4096*G^3 - 36352*G^2 - 103360*G - 95304, -49152*G^4 - 583680*G^3 - 2495232*G^2 - 4609248*G - 3127704; 1280*G + 3040, -10240*G^2 - 48320*G - 56992, -122880*G^3 - 863744*G^2 - 2023936*G - 1580952; -128*G - 304, 1024*G^2 + 4736*G + 5472, 12288*G^3 + 80384*G^2 + 174592*G + 125864]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) ((tM i F G) * (tM i F G)) (1) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![128*G + 184, -2048*G^2 - 7296*G - 5776, -1536*G^2 - 6016*G - 5624; -64, 1408*G + 3352, 640*G + 1520; -128, 2432*G + 5776, 1472*G + 3504]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) ((tM i F G) * (uvM i F G)) ((uvM i F G) * (tM i F G)) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![1024*G^2 + 6336*G + 9272, -16384*G^3 - 140288*G^2 - 388864*G - 351728, -28672*G^3 - 177152*G^2 - 357312*G - 233472; 2560*G + 6144, -40960*G^2 - 195648*G - 233624, -1536*G^2 - 8448*G - 11400; -256*G - 672, 4096*G^2 + 20928*G + 26600, 39936*G^2 + 189312*G + 224352]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) ((uM F) * (uM F)) (1) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) (ρM * ((uM F) * (ρM * (uM F)))) (1) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 16, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) (ρM * (uvM i F G)) ((tM i F G) * ρM) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 0, -256*G^2 - 1696*G - 2648; 0, 0, -64*G - 184; 0, 0, -704*G - 1736]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) (ρM * (tM i F G)) ((tM i F G) * ((uvM i F G) * ρM)) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![32, 14336*G^3 + 54016*G^2 + 14592*G - 77976, -14336*G^3 - 54272*G^2 - 14880*G + 78736; 32, -34304*G^2 - 162944*G - 193496, 34304*G^2 + 163648*G + 195168; 16, -36352*G^2 - 171712*G - 202768, 36352*G^2 + 172352*G + 204288]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) ((uM F) * (uvM i F G)) ((uvM i F G) * (uM F)) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![0, 256*G^2 + 1664*G + 2508, 9472*G^2 + 44288*G + 51756; 0, 640*G + 1552, 64*G + 184; 0, -64*G - 184, -640*G - 1552]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    MatEq (k m) ((uM F) * (tM i F G)) ((tM i F G) * ((uvM i F G) * (uM F))) := by
  obtain ⟨hi, hF, hs⟩ := h
  subst hi hF
  exact MatEq.of_dvd (3 * G + 7) hs (P := !![-64, 14336*G^3 + 54016*G^2 + 14656*G - 77824, 256*G^2 + 128*G - 1140; -32, -34304*G^2 - 163456*G - 194712, -1216*G - 2888; -16, -36352*G^2 - 171968*G - 203376, -896*G - 2128]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action {m : ℕ} {i F G : ℤ} (h : Data m i F G) : SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM i F G) (tM i F G) (uM F) ρM (compat_uv h) (compat_t h)
    (compat_u h) (compat_rho h) (uv_sq h) (t_sq h) (uv_comm_t h) (rho_cube h) (u_sq h)
    (u_rho h) (uv_rho h) (t_rho h) (uv_comm_u h) (t_u h)

theorem uv_a {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φuv Torus.a = (2*F*i : ℤ) • Torus.c + (-5*i : ℤ) • Torus.a + (2*i : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM i F G) (compat_uv h) 1 (2*F*i) (-5*i) (2*i) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φuv Torus.b = (2*F*i^2 - 8*F*i - 20*G*i^2 - 60*i^2 : ℤ) • Torus.c + (-8*F*i - 26*i^2 : ℤ) • Torus.a + (-4*F*i + 5*i^2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM i F G) (compat_uv h) 2 (2*F*i^2 - 8*F*i - 20*G*i^2 - 60*i^2) (-8*F*i - 26*i^2) (-4*F*i + 5*i^2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φt Torus.c = (4 - i : ℤ) • Torus.c + (2 : ℤ) • Torus.a + (4 : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM i F G) (compat_t h) 0 (4 - i) (2) (4) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φt Torus.a = (4*G*i : ℤ) • Torus.c + (-7*i : ℤ) • Torus.a + (-8*i : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM i F G) (compat_t h) 1 (4*G*i) (-7*i) (-8*i) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φt Torus.b = (2*F*i - 4*i : ℤ) • Torus.c + (-2*i : ℤ) • Torus.a + (-7*i : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM i F G) (compat_t h) 2 (2*F*i - 4*i) (-2*i) (-7*i) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φu Torus.c = (-1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (uM F) (compat_u h) 0 (-1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φρ Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (ρM) (compat_rho h) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φρ Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM) (compat_rho h) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b {m : ℕ} {i F G : ℤ} (h : Data m i F G) :
    (action h).φρ Torus.b = (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM) (compat_rho h) 2 (-2) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem data (m : ℕ) (hm : 1 ≤ m) : Data m (iV (m + 1)) (FV (m + 1)) (GV (m + 1)) := by
  have h4 : (4 : ℤ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  have hdvd : ∀ e : ℕ, (3 : ℤ) ∣ 4 ^ e - 1 := fun e => by
    simpa using sub_one_dvd_pow_sub_one (4 : ℤ) e
  obtain ⟨c, hc⟩ := hdvd m
  have hG : 3 * GV (m + 1) + 7 = 4 ^ m := by
    have := Int.mul_ediv_cancel' (a := 3) (b := (4 : ℤ) ^ m - 7) ⟨c - 2, by linarith⟩
    simp only [GV, Nat.add_sub_cancel]
    linarith
  have hF : FV (m + 1) = 4 * GV (m + 1) + 9 := by
    have := Int.mul_ediv_cancel' (hdvd (m + 1))
    simp only [FV]
    rw [pow_succ] at this ⊢
    linarith
  have hi : iV (m + 1) = 8 * GV (m + 1) + 19 := by
    have h8 : (2 : ℤ) ^ (2 * (m + 1) + 1) = 8 * 4 ^ m := by
      rw [h4, show 2 * (m + 1) + 1 = 2 * m + 3 by ring, pow_add]; norm_num; ring
    have := Int.mul_ediv_cancel' (a := 3) (b := (2 : ℤ) ^ (2 * (m + 1) + 1) + 1)
      ⟨8 * c + 3, by rw [h8]; linarith⟩
    simp only [iV]
    linarith
  refine ⟨hi, hF, fun r => ?_⟩
  rw [hG, h4]
  refine pow_dvd_pow 2 ?_
  fin_cases r <;> simp [k] <;> omega

@[expose] def actionPaper (m : ℕ) (hm : 1 ≤ m) : SigmaFourAction (k m) :=
  action (data m hm)

end Type120

end CFSG.CGT.Stroth77
