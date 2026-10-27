module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  Matrix
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

structure CxStr (fr : Frame Q) (bar : V ≃ₗ[K] V) : Prop where
  mem : bar ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  sq : ∀ v, bar (bar v) = -v
  orth : ∀ X Y, polar Q (fr.incl X) (bar (fr.incl Y)) = 0

@[expose] def detPolar (A B : Matrix (Fin 2) (Fin 2) K) : K :=
  A 1 1 * B 0 0 + A 0 0 * B 1 1 - A 1 0 * B 0 1 - A 0 1 * B 1 0

@[expose] def cxVec (fr : Frame Q) (bar : V ≃ₗ[K] V) (A B : Matrix (Fin 2) (Fin 2) K) : V :=
  fr.incl A + bar (fr.incl B)

section CxVec

variable {fr : Frame Q} {bar : V ≃ₗ[K] V}

theorem polar_incl_incl (A B : Matrix (Fin 2) (Fin 2) K) :
    polar Q (fr.incl A) (fr.incl B) = detPolar A B := by
  rw [Frame.polar_incl_right, Frame.coords_incl]
  simp [detPolar]

theorem polar_cxVec (hb : CxStr fr bar) (A B A' B' : Matrix (Fin 2) (Fin 2) K) :
    polar Q (cxVec fr bar A B) (cxVec fr bar A' B') = detPolar A A' + detPolar B B' := by
  have h1 : polar Q (fr.incl A) (bar (fr.incl B')) = 0 := hb.orth A B'
  have h2 : polar Q (bar (fr.incl B)) (fr.incl A') = 0 := by
    rw [polar_comm]
    exact hb.orth A' B
  have h3 : polar Q (bar (fr.incl B)) (bar (fr.incl B')) = detPolar B B' := by
    rw [polar_map_of_mem hb.mem, polar_incl_incl]
  unfold cxVec
  simp only [polar_add_left, polar_add_right, h1, h2, h3, polar_incl_incl]
  ring

theorem Q_cxVec (hb : CxStr fr bar) (A B : Matrix (Fin 2) (Fin 2) K) :
    Q (cxVec fr bar A B) = A.det + B.det := by
  unfold cxVec
  rw [QuadraticMap.map_add Q, hb.orth, map_of_mem hb.mem, Frame.Q_incl, Frame.Q_incl]
  ring

theorem cxVec_add (A B A' B' : Matrix (Fin 2) (Fin 2) K) :
    cxVec fr bar (A + A') (B + B') = cxVec fr bar A B + cxVec fr bar A' B' := by
  unfold cxVec
  rw [map_add, map_add, map_add]
  abel

theorem cxVec_smul (c : K) (A B : Matrix (Fin 2) (Fin 2) K) :
    cxVec fr bar (c • A) (c • B) = c • cxVec fr bar A B := by
  unfold cxVec
  rw [map_smul, map_smul, map_smul, smul_add]

theorem bar_cxVec (hb : CxStr fr bar) (A B : Matrix (Fin 2) (Fin 2) K) :
    bar (cxVec fr bar A B) = cxVec fr bar (-B) A := by
  unfold cxVec
  rw [map_add, hb.sq, map_neg, neg_add_eq_sub, sub_eq_add_neg, add_comm]

end CxVec

section Diag

variable {fr : Frame Q} {bar : V ≃ₗ[K] V}

@[expose] noncomputable def diagFrame (hb : CxStr fr bar) (h2 : (2 : K) ≠ 0) (ε : K)
    (hε : ε * ε = 1) : Frame Q where
  P := ⟨cxVec fr bar !![1, 0; 0, 0] !![0, -ε; 0, 0],
    (2 : K)⁻¹ • cxVec fr bar !![0, 0; 0, 1] !![0, 0; ε, 0],
    by rw [Q_cxVec hb]; simp [Matrix.det_fin_two],
    by rw [map_smul_eq_sq, Q_cxVec hb]; simp [Matrix.det_fin_two],
    by
      rw [polar_smul_right_eq, polar_cxVec hb]
      simp [detPolar, hε]
      field_simp
      norm_num⟩
  P' := ⟨cxVec fr bar !![0, ε; 0, 0] !![1, 0; 0, 0],
    (2 : K)⁻¹ • cxVec fr bar !![0, 0; -ε, 0] !![0, 0; 0, 1],
    by rw [Q_cxVec hb]; simp [Matrix.det_fin_two],
    by rw [map_smul_eq_sq, Q_cxVec hb]; simp [Matrix.det_fin_two],
    by
      rw [polar_smul_right_eq, polar_cxVec hb]
      simp [detPolar, hε]
      field_simp
      norm_num⟩
  orth :=
    ⟨by rw [polar_cxVec hb]; simp [detPolar],
      by rw [polar_smul_right_eq, polar_cxVec hb]; simp [detPolar],
      by rw [polar_smul_left_eq, polar_cxVec hb]; simp [detPolar],
      by rw [polar_smul_left_eq, polar_smul_right_eq, polar_cxVec hb]; simp [detPolar]⟩

@[expose] def diagY₁ (ε : K) (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![X 0 0, -(ε * X 0 1); -(ε * ((2 : K)⁻¹ * X 1 0)), (2 : K)⁻¹ * X 1 1]

@[expose] def diagY₂ (ε : K) (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![-X 0 1, -(ε * X 0 0); ε * ((2 : K)⁻¹ * X 1 1), (2 : K)⁻¹ * X 1 0]

@[expose] def cxJ : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, 0]

theorem diagFrame_incl (hb : CxStr fr bar) (h2 : (2 : K) ≠ 0) {ε : K} (hε : ε * ε = 1)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (diagFrame hb h2 ε hε).incl X = cxVec fr bar (diagY₁ ε X) (diagY₂ ε X) := by
  rw [Frame.incl_apply]
  change X 0 0 • cxVec fr bar !![1, 0; 0, 0] !![0, -ε; 0, 0] +
      X 1 1 • ((2 : K)⁻¹ • cxVec fr bar !![0, 0; 0, 1] !![0, 0; ε, 0]) +
      (-X 0 1) • cxVec fr bar !![0, ε; 0, 0] !![1, 0; 0, 0] +
      X 1 0 • ((2 : K)⁻¹ • cxVec fr bar !![0, 0; -ε, 0] !![0, 0; 0, 1]) = _
  simp only [← cxVec_smul, ← cxVec_add]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagY₁, diagY₂] <;> ring

theorem diagFrame_bar_incl (hb : CxStr fr bar) (h2 : (2 : K) ≠ 0) {ε : K} (hε : ε * ε = 1)
    (X : Matrix (Fin 2) (Fin 2) K) :
    bar ((diagFrame hb h2 ε hε).incl X) = (diagFrame hb h2 ε hε).incl (X * cxJ) := by
  rw [diagFrame_incl, diagFrame_incl, bar_cxVec hb]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagY₁, diagY₂, cxJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagFrame_orth (hb : CxStr fr bar) (h2 : (2 : K) ≠ 0) (X Y : Matrix (Fin 2) (Fin 2) K) :
    polar Q ((diagFrame hb h2 1 (by norm_num)).incl X)
      ((diagFrame hb h2 (-1) (by norm_num)).incl Y) = 0 := by
  rw [diagFrame_incl, diagFrame_incl, polar_cxVec hb]
  simp only [detPolar, diagY₁, diagY₂]
  simp
  ring

end Diag

section Commute

variable {F : Frame Q} {g : V ≃ₗ[K] V}

theorem coords_apply_of_incl_mul (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {J J' : Matrix (Fin 2) (Fin 2) K} (hJ : J' * J = 1) (hg : ∀ Y, g (F.incl Y) = F.incl (Y * J))
    (x : V) : F.coords (g x) = F.coords x * J := by
  have hr : F.coords (g (x - F.incl (F.coords x))) = 0 := by
    have hperp : x - F.incl (F.coords x) ∈ F.perp := by
      rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
    rw [← Frame.mem_perp_iff, Frame.mem_perp_iff_forall_incl]
    intro Y
    have h1 : F.incl Y = g (F.incl (Y * J')) := by
      rw [hg, Matrix.mul_assoc, hJ, Matrix.mul_one]
    rw [h1, polar_map_of_mem hgO]
    exact (Frame.mem_perp_iff_forall_incl F).mp hperp _
  have hx : g x = g (F.incl (F.coords x)) + g (x - F.incl (F.coords x)) := by
    rw [← map_add]
    congr 1
    abel
  rw [hx, map_add, hg, hr, add_zero, Frame.coords_incl]

theorem commute_La_of_incl_mul (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {J J' : Matrix (Fin 2) (Fin 2) K} (hJ : J' * J = 1) (hg : ∀ Y, g (F.incl Y) = F.incl (Y * J))
    (A : SL(2, K)) : g * F.La A = F.La A * g := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_apply, Frame.La_apply, map_add, hg,
    coords_apply_of_incl_mul hgO hJ hg x, Matrix.sub_mul, Matrix.mul_assoc]

end Commute

end CFSG.ClassicalInvolution.Asc77
