module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutToral
public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Orth

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem q8_matrix_decomp (h3 : (3 : K) = 0) (M : Matrix (Fin 2) (Fin 2) K) :
    M = (2 * (M 0 0 + M 1 1)) • (1 : Matrix (Fin 2) (Fin 2) K)
      + (2 * (M 0 1 - M 1 0)) • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)
      + (M 0 0 - M 1 1 + M 0 1 + M 1 0) • (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) K)
      + (M 0 0 - M 1 1 - M 0 1 - M 1 0) •
        (!![0, 1; -1, 0] * !![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-M 0 0) * h3
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-M 0 1) * h3
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-M 1 0) * h3
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-M 1 1) * h3

private abbrev CommRQ8 (F : Frame Q) (T : V ≃ₗ[K] V) (N : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ x : V, T (F.incl (N * F.coords x)) = F.incl (N * F.coords (T x))

private theorem commRQ8_one {F : Frame Q} {T : V ≃ₗ[K] V}
    (hP : ∀ x : V, T (F.incl (F.coords x)) = F.incl (F.coords (T x))) : CommRQ8 F T 1 := by
  intro x
  simp only [Matrix.one_mul]
  exact hP x

private theorem commRQ8_add {F : Frame Q} {T : V ≃ₗ[K] V} {N N' : Matrix (Fin 2) (Fin 2) K}
    (h : CommRQ8 F T N) (h' : CommRQ8 F T N') : CommRQ8 F T (N + N') := by
  intro x
  simp only [Matrix.add_mul, map_add, h x, h' x]

private theorem commRQ8_smul {F : Frame Q} {T : V ≃ₗ[K] V} {N : Matrix (Fin 2) (Fin 2) K}
    (c : K) (h : CommRQ8 F T N) : CommRQ8 F T (c • N) := by
  intro x
  simp only [Matrix.smul_mul, map_smul, h x]

private theorem commRQ8_mul {F : Frame Q} {T : V ≃ₗ[K] V} {N N' : Matrix (Fin 2) (Fin 2) K}
    (h : CommRQ8 F T N) (h' : CommRQ8 F T N') : CommRQ8 F T (N * N') := by
  intro x
  have e : ∀ y : V, F.incl ((N * N') * F.coords y) =
      F.incl (N * F.coords (F.incl (N' * F.coords y))) := by
    intro y
    rw [F.coords_incl, Matrix.mul_assoc]
  rw [e x, e (T x), h (F.incl (N' * F.coords x)), h' x]

private theorem commRQ8_of_La {F : Frame Q} {T : V ≃ₗ[K] V}
    (hP : ∀ x : V, T (F.incl (F.coords x)) = F.incl (F.coords (T x)))
    {a : SL(2, K)} (ha : T * F.La a = F.La a * T) :
    CommRQ8 F T (a : Matrix (Fin 2) (Fin 2) K) := by
  intro x
  have h := LinearEquiv.congr_fun ha x
  simp only [LinearEquiv.mul_apply, F.La_apply, map_add, map_sub, hP x] at h
  exact sub_left_inj.mp (add_left_cancel h)

theorem commute_La_of_commute_Q8 [Finite K] (hK : Nat.card K = 3) (F : Frame Q)
    {T : V ≃ₗ[K] V} (hT : ∀ a ∈ commutator SL(2, K), T * F.La a = F.La a * T)
    (A : SL(2, K)) : T * F.La A = F.La A * T := by
  have h3 : (3 : K) = 0 := OrthQ8.three_eq_zero hK
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  have hI_mem : (OrthQ8.sl2I : SL(2, K)) ∈ commutator SL(2, K) :=
    (OrthQ8.mem_commutator_sl2_iff hK).mpr OrthQ8.sl2I_pow_four
  have hJ_mem : OrthQ8.sl2J h3 ∈ commutator SL(2, K) :=
    (OrthQ8.mem_commutator_sl2_iff hK).mpr (OrthQ8.sl2J_pow_four h3)
  have hneg_mem : (-1 : SL(2, K)) ∈ commutator SL(2, K) := by
    have h := pow_mem hI_mem 2
    rwa [OrthQ8.sl2I_sq] at h
  have hP : ∀ x : V, T (F.incl (F.coords x)) = F.incl (F.coords (T x)) := by
    intro x
    have h := LinearEquiv.congr_fun (hT (-1) hneg_mem) x
    simp only [LinearEquiv.mul_apply, F.La_neg_one_apply, map_sub, map_smul] at h
    exact smul_right_injective V h2 (sub_right_inj.mp h)
  have hone : CommRQ8 F T 1 := commRQ8_one hP
  have hI : CommRQ8 F T ((OrthQ8.sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) :=
    commRQ8_of_La hP (hT _ hI_mem)
  have hJ : CommRQ8 F T ((OrthQ8.sl2J h3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) :=
    commRQ8_of_La hP (hT _ hJ_mem)
  rw [OrthQ8.coe_sl2I] at hI
  rw [OrthQ8.coe_sl2J h3] at hJ
  have hIJ := commRQ8_mul hI hJ
  have hall : ∀ M : Matrix (Fin 2) (Fin 2) K, CommRQ8 F T M := by
    intro M
    rw [q8_matrix_decomp h3 M]
    exact commRQ8_add (commRQ8_add (commRQ8_add (commRQ8_smul _ hone) (commRQ8_smul _ hI))
      (commRQ8_smul _ hJ)) (commRQ8_smul _ hIJ)
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, F.La_apply, map_add, map_sub,
    hall (A : Matrix (Fin 2) (Fin 2) K) x, hP x]

theorem exists_mulRight_of_commute_Q8 [Finite K] (hK : Nat.card K = 3) (F : Frame Q)
    {T : V ≃ₗ[K] V} (hT : ∀ a ∈ commutator SL(2, K), T * F.La a = F.La a * T) :
    ∃ P : Matrix (Fin 2) (Fin 2) K, ∀ Y, T (F.incl Y) = F.incl (Y * P) := by
  obtain ⟨P, hP, -⟩ := ModelFacts.OrthAut.exists_mulRight_of_commute_La F (T : V →ₗ[K] V)
    fun A x => by
      have := LinearEquiv.congr_fun (commute_La_of_commute_Q8 hK F hT A) x
      simpa using this
  exact ⟨P, hP⟩

theorem exists_smul_of_commute_Q8_swap [Finite K] (hK : Nat.card K = 3) (F : Frame Q)
    {T : V ≃ₗ[K] V} (hT : ∀ a ∈ commutator SL(2, K), T * F.La a = F.La a * T)
    (hT' : ∀ a ∈ commutator SL(2, K), T * F.swap.La a = F.swap.La a * T) :
    ∃ c : K, ∀ v ∈ F.span, T v = c • v := by
  obtain ⟨c, hc⟩ := ModelFacts.OrthAut.exists_scalar_of_commute_La_swap F (T : V →ₗ[K] V)
    (fun A x => by
      have := LinearEquiv.congr_fun (commute_La_of_commute_Q8 hK F hT A) x
      simpa using this)
    (fun A x => by
      have := LinearEquiv.congr_fun (commute_La_of_commute_Q8 hK F.swap hT' A) x
      simpa using this)
  refine ⟨c, ?_⟩
  rintro v ⟨Y, rfl⟩
  exact hc Y

theorem commute_swap_La_of_eqOn_La (F : Frame Q) {T : V ≃ₗ[K] V} (a : SL(2, K))
    (hperp : ∀ v ∈ F.perp, T v ∈ F.perp) (hspan : ∀ v ∈ F.span, T v = F.La a v)
    (b : SL(2, K)) : T * F.swap.La b = F.swap.La b * T := by
  have hfix : ∀ v ∈ F.perp, F.swap.La b v = v := fun v hv =>
    F.swap.La_apply_of_coords_eq_zero b
      (F.swap.mem_perp_iff.mp (by rw [F.perp_swap]; exact hv))
  have hstab : ∀ v ∈ F.span, F.swap.La b v ∈ F.span := by
    rintro _ ⟨Y, rfl⟩
    exact ⟨_, (CFSG.ClassicalInvolution.ModelFacts.OrthAut.swap_La_incl F b Y).symm⟩
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ : ∃ x₁ ∈ F.span, ∃ x₂ ∈ F.perp, x = x₁ + x₂ :=
    ⟨F.incl (F.coords x), ⟨_, rfl⟩, x - F.incl (F.coords x),
      by rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self], by abel⟩
  have hc := LinearEquiv.congr_fun (F.La_comm_La_swap a b) x₁
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hc
  simp only [LinearEquiv.mul_apply, map_add, hfix x₂ hx₂, hspan _ (hstab x₁ hx₁),
    hfix (T x₂) (hperp x₂ hx₂), hspan x₁ hx₁, hc]

theorem det_eq_one_of_mul_self_eq_neg_one [Finite K] (hK : Nat.card K = 3)
    {X : Matrix (Fin 2) (Fin 2) K} (hX : X * X = -1) : X.det = 1 := by
  have h00 := congrFun (congrFun hX 0) 0
  have h01 := congrFun (congrFun hX 0) 1
  have h10 := congrFun (congrFun hX 1) 0
  have h11 := congrFun (congrFun hX 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two]
  by_cases hs : X 0 0 + X 1 1 = 0
  · linear_combination (-1 : K) * h00 + (X 0 0) * hs
  · have hb : X 0 1 = 0 := by
      have : X 0 1 * (X 0 0 + X 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp this).resolve_right hs
    have h00' : X 0 0 * X 0 0 = -1 := by
      rw [hb] at h00
      linear_combination h00
    exact absurd h00' (sq_ne_neg_one hK (X 0 0))

theorem eq_one_or_neg_one_of_det_eq_one [Finite K] (hK : Nat.card K = 3)
    {X : Matrix (Fin 2) (Fin 2) K} (hdet : X.det = 1) (hX : X * X = 1) : X = 1 ∨ X = -1 := by
  let g : SL(2, K) := ⟨X, hdet⟩
  have hsq : g ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hX)
  rcases eq_one_or_neg_one hK hsq with h | h
  · exact Or.inl (by simpa [g] using congrArg Subtype.val h)
  · exact Or.inr (by simpa [g] using congrArg Subtype.val h)

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3
