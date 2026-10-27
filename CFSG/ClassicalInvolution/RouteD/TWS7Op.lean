module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.RouteD.TWS7Alg

public section

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  Matrix
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.RouteD.TWS7

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def opOf (F : Frame Q) (N : Matrix (Fin 2) (Fin 2) K) : V →ₗ[K] V :=
  F.incl ∘ₗ (LinearMap.mulLeft K N) ∘ₗ F.coords

theorem opOf_apply (F : Frame Q) (N : Matrix (Fin 2) (Fin 2) K) (y : V) :
    opOf F N y = F.incl (N * F.coords y) := rfl

theorem La_apply_eq_opOf (F : Frame Q) (A : SL(2, K)) (y : V) :
    F.La A y = y + opOf F ((A : Matrix (Fin 2) (Fin 2) K) - 1) y := by
  rw [Frame.La_apply, opOf_apply, Matrix.sub_mul, Matrix.one_mul]

theorem det_eq_zero_of_mul_self_eq_zero {N : Matrix (Fin 2) (Fin 2) K} (h : N * N = 0) :
    N.det = 0 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_zero] at this
  exact mul_self_eq_zero.mp this

theorem trace_eq_zero_of_mul_self_eq_zero {N : Matrix (Fin 2) (Fin 2) K} (h : N * N = 0)
    (hN : N ≠ 0) : N 0 0 + N 1 1 = 0 := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_of_fin_two N
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11 ⊢
  by_contra hne
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right hne
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right hne
  subst hb hc
  have ha : a = 0 := by simpa using h00
  have hd : d = 0 := by simpa using h11
  subst ha hd
  exact hN (by ext i j; fin_cases i <;> fin_cases j <;> simp)

section Op

variable (F : Frame Q) {N : Matrix (Fin 2) (Fin 2) K}

theorem Q_opOf (hN2 : N * N = 0) (y : V) : Q (opOf F N y) = 0 := by
  rw [opOf_apply, Frame.Q_incl, Matrix.det_mul, det_eq_zero_of_mul_self_eq_zero hN2, zero_mul]

theorem polar_ker_opOf (hN2 : N * N = 0) (hN : N ≠ 0) (y : V) (hy : opOf F N y = 0) (z : V) :
    polar Q y (opOf F N z) = 0 := by
  have h1 : N * F.coords y = 0 := by
    have := congrArg F.coords hy
    rwa [opOf_apply, Frame.coords_incl, map_zero] at this
  have htr := trace_eq_zero_of_mul_self_eq_zero hN2 hN
  rw [opOf_apply, Frame.polar_incl_right]
  generalize F.coords y = C at h1 ⊢
  generalize F.coords z = Z
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_of_fin_two N
  obtain ⟨c₀, c₁, c₂, c₃, rfl⟩ := exists_eq_of_fin_two C
  obtain ⟨z₀, z₁, z₂, z₃, rfl⟩ := exists_eq_of_fin_two Z
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e10 := congrFun (congrFun h1 1) 0
  have e11 := congrFun (congrFun h1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11 htr ⊢
  linear_combination (z₀ * c₃ - z₂ * c₁ - z₁ * c₂ + z₃ * c₀) * htr - z₀ * e11 + z₂ * e01 +
    z₁ * e10 - z₃ * e00

theorem opOf_ne_zero (hN : N ≠ 0) : opOf F N ≠ 0 := by
  intro h
  apply hN
  have := LinearMap.congr_fun h (F.incl 1)
  rw [opOf_apply, Frame.coords_incl, Matrix.mul_one] at this
  exact F.incl_injective (by simpa using this)

theorem opOf_opOf (hN2 : N * N = 0) (y : V) : opOf F N (opOf F N y) = 0 := by
  rw [opOf_apply, opOf_apply, Frame.coords_incl, ← Matrix.mul_assoc, hN2, Matrix.zero_mul]
  simp

end Op

section Unip

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem nilpotent_of_pow_char {A : SL(2, K)} (hA : A ^ p = 1) (hA1 : A ≠ 1) :
    ((A : Matrix (Fin 2) (Fin 2) K) - 1) * ((A : Matrix (Fin 2) (Fin 2) K) - 1) = 0 ∧
      (A : Matrix (Fin 2) (Fin 2) K) - 1 ≠ 0 := by
  have hcoe : (A : Matrix (Fin 2) (Fin 2) K) ^ p = 1 := by
    have := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K)) hA
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  have hNp : ((A : Matrix (Fin 2) (Fin 2) K) - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute p (Commute.one_right _), hcoe, one_pow, sub_self]
  have hdet : ((A : Matrix (Fin 2) (Fin 2) K) - 1).det = 0 := by
    have := congrArg Matrix.det hNp
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp this
  have hA1' : (A : Matrix (Fin 2) (Fin 2) K) - 1 ≠ 0 := by
    intro h
    apply hA1
    exact Subtype.ext (sub_eq_zero.mp h)
  refine ⟨?_, hA1'⟩
  have hA2 := A.2
  obtain ⟨a, b, c, d, hAe⟩ := exists_eq_of_fin_two (A : Matrix (Fin 2) (Fin 2) K)
  rw [hAe] at hA2 hdet ⊢
  rw [Matrix.det_fin_two] at hA2 hdet
  simp at hA2 hdet
  have hd : a + d = 2 := by linear_combination hA2 - hdet
  have e : (!![a, b; c, d] - 1 : Matrix (Fin 2) (Fin 2) K) = !![a - 1, b; c, d - 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-1) * hdet + (a - 1) * hd
  · linear_combination b * hd
  · linear_combination c * hd
  · linear_combination (-1) * hdet + (d - 1) * hd

end Unip

section Transport

variable (F : Frame Q) {g : V ≃ₗ[K] V}

theorem transport_commute_right (h2 : (2 : K) ≠ 0) (hg : g * F.La (-1) = F.La (-1) * g)
    (hcent : ∀ B : SL(2, K), g * F.swap.La B = F.swap.La B * g) (B : SL(2, K))
    (X : Matrix (Fin 2) (Fin 2) K) :
    F.transport g (X * sigmaLin (B : Matrix (Fin 2) (Fin 2) K)) =
      F.transport g X * sigmaLin (B : Matrix (Fin 2) (Fin 2) K) := by
  have h1 := Frame.embGrp_conj h2 hg (rmulEquiv (Frame.sigmaSL B))
  rw [← Frame.swap_La_eq_embGrp, hcent B, mul_inv_cancel_right, Frame.swap_La_eq_embGrp] at h1
  have h3 := F.embGrp_injective h1
  have h4 : Frame.transportEquiv h2 hg * rmulEquiv (Frame.sigmaSL B) =
      rmulEquiv (Frame.sigmaSL B) * Frame.transportEquiv h2 hg := by
    calc Frame.transportEquiv h2 hg * rmulEquiv (Frame.sigmaSL B)
        = (Frame.transportEquiv h2 hg * rmulEquiv (Frame.sigmaSL B) *
            (Frame.transportEquiv h2 hg)⁻¹) * Frame.transportEquiv h2 hg := by group
      _ = rmulEquiv (Frame.sigmaSL B) * Frame.transportEquiv h2 hg := by rw [h3]
  have := LinearEquiv.congr_fun h4 X
  simpa [rmulEquiv_apply, Frame.coe_sigmaSL, Frame.transportEquiv_apply] using this

end Transport

section WKill

variable {p : ℕ} [Fact p.Prime] [CharP K p] {g : V ≃ₗ[K] V}

theorem act_eq_self_of_commute (F : Frame Q) (h2 : (2 : K) ≠ 0)
    (hcentA : ∀ A : SL(2, K), g * F.La A = F.La A * g)
    (hcentB : ∀ B : SL(2, K), g * F.swap.La B = F.swap.La B * g) (hgp : g ^ p = 1) :
    ∀ y ∈ F.span, g y = y := by
  have hg : g * F.La (-1) = F.La (-1) * g := hcentA (-1)
  have hL : ∀ (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K),
      F.transport g ((A : Matrix (Fin 2) (Fin 2) K) * X) =
        (A : Matrix (Fin 2) (Fin 2) K) * F.transport g X :=
    fun A X => Frame.transport_commute_left h2 hg hcentA A X
  have hSX : ∀ X, F.transport g X = X * F.transport g 1 := eq_mulRight_of_commute_left hL
  have hCB : ∀ B : SL(2, K), (B : Matrix (Fin 2) (Fin 2) K) * F.transport g 1 =
      F.transport g 1 * (B : Matrix (Fin 2) (Fin 2) K) := by
    intro B'
    have h := transport_commute_right F h2 hg hcentB (Frame.sigmaSL B') 1
    rw [Frame.coe_sigmaSL, sigmaLin_sigmaLin, Matrix.one_mul] at h
    rw [hSX (B' : Matrix (Fin 2) (Fin 2) K)] at h
    exact h
  let t₁ : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let t₂ : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨c₀, c₁, c₂, c₃, hCe⟩ := exists_eq_of_fin_two (F.transport g 1)
  have e1 := hCB t₁
  have e2 := hCB t₂
  rw [hCe] at e1 e2
  have hc2 : c₂ = 0 := by
    have := congrFun (congrFun e1 0) 0
    simp [t₁, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hc3 : c₃ = c₀ := by
    have := congrFun (congrFun e1 0) 1
    simp [t₁, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hc1 : c₁ = 0 := by
    have := congrFun (congrFun e2 0) 0
    simp [t₂, Matrix.mul_apply, Fin.sum_univ_two] at this
    exact this
  have hSc : ∀ X, F.transport g X = c₀ • X := by
    intro X
    rw [hSX X, hCe, hc1, hc2, hc3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hgy : ∀ y ∈ F.span, g y = c₀ • y := by
    intro y hy
    obtain ⟨X, rfl⟩ := hy
    rw [← Frame.incl_transport h2 hg X, hSc X, map_smul]
  have hgpow : ∀ n : ℕ, ∀ y ∈ F.span, (g ^ n) y = c₀ ^ n • y := by
    intro n
    induction n with
    | zero => intro y hy; simp
    | succ n ih =>
      intro y hy
      rw [pow_succ, LinearEquiv.mul_apply, hgy y hy, map_smul, ih y hy, smul_smul, pow_succ,
        mul_comm]
  have he₁ : F.incl 1 ∈ F.span := ⟨1, rfl⟩
  have he₁0 : F.incl 1 ≠ 0 := fun h => one_ne_zero (F.incl_injective (by simpa using h))
  have hcp : c₀ ^ p = 1 := by
    have h1 := hgpow p (F.incl 1) he₁
    rw [hgp] at h1
    have h3 : (c₀ ^ p - 1) • F.incl 1 = 0 := by
      rw [sub_smul, one_smul, ← h1]
      simp
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right he₁0)
  have hc1' : c₀ = 1 := by
    have : (c₀ - 1) ^ p = 0 := by rw [sub_pow_char, hcp, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp this)
  intro y hy
  rw [hgy y hy, hc1', one_smul]

end WKill

section Eigen

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_eigen_pair_perp (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (fr FC : Frame Q) {A₀ : SL(2, K)} (hA0 : A₀ ≠ 1) (hA0p : A₀ ^ p = 1)
    {w : V ≃ₗ[K] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hw2 : w * w = 1)
    (hwinv : w * FC.La A₀ * w⁻¹ = (FC.La A₀)⁻¹)
    (hcentA : ∀ A : SL(2, K), FC.La A₀ * fr.La A = fr.La A * FC.La A₀)
    (hcentB : ∀ B : SL(2, K), FC.La A₀ * fr.swap.La B = fr.swap.La B * FC.La A₀) :
    ∃ up um : V, fr.coords up = 0 ∧ fr.coords um = 0 ∧ up ≠ 0 ∧ um ≠ 0 ∧ w up = up ∧
      w um = -um ∧ Q up = 0 ∧ Q um = 0 := by
  classical
  obtain ⟨hN2, hN0⟩ := nilpotent_of_pow_char hA0p hA0
  set N : Matrix (Fin 2) (Fin 2) K := (A₀ : Matrix (Fin 2) (Fin 2) K) - 1 with hN
  set L : V →ₗ[K] V := opOf FC N with hL
  have hg : ∀ y, FC.La A₀ y = y + L y := fun y => La_apply_eq_opOf FC A₀ y
  have hLL : ∀ y, L (L y) = 0 := opOf_opOf FC hN2
  have hginv : ∀ z, (FC.La A₀)⁻¹ z = z - L z := by
    intro z
    have h1 : FC.La A₀ (z - L z) = z := by
      rw [hg, map_sub, hLL, sub_zero]
      abel
    have := LinearEquiv.inv_apply_apply' (FC.La A₀) (z - L z)
    rw [h1] at this
    exact this
  have hwL : ∀ y, w (L y) = -L (w y) := by
    intro y
    have h1 := LinearEquiv.congr_fun hwinv (w y)
    simp only [LinearEquiv.mul_apply] at h1
    have h2' : w⁻¹ (w y) = y := LinearEquiv.inv_apply_apply' w y
    rw [h2', hg, map_add, hginv] at h1
    have : w y + w (L y) = w y - L (w y) := h1
    have := add_left_cancel (a := w y) (this.trans (by abel : w y - L (w y) = w y + -L (w y)))
    exact this
  have hgp : (FC.La A₀) ^ p = 1 := by rw [← map_pow, hA0p, map_one]
  have hspan : ∀ y ∈ fr.span, L y = 0 := by
    intro y hy
    have hfix := act_eq_self_of_commute fr h2 hcentA hcentB (g := FC.La A₀) hgp y hy
    have := hg y
    rw [hfix] at this
    exact (add_eq_left.mp this.symm)
  have hker : ∀ y, L y = 0 → ∀ z, polar Q y (L z) = 0 := fun y hy z =>
    polar_ker_opOf FC hN2 hN0 y hy z
  obtain ⟨up, um, hup, hum, hup0, hum0, hwup, hwum, hQup, hQum⟩ :=
    exists_singular_eigenvectors h2 hQ hwO hw2 hwL (Q_opOf FC hN2) hker (opOf_ne_zero FC hN0)
  have hperp : ∀ v ∈ LinearMap.range L, fr.coords v = 0 := by
    intro v hv
    obtain ⟨z, rfl⟩ := hv
    refine (Frame.mem_perp_iff fr).mp ((Frame.mem_perp_iff_forall_incl fr).mpr fun Y => ?_)
    rw [polar_comm]
    exact hker _ (hspan _ ⟨Y, rfl⟩) z
  exact ⟨up, um, hperp _ hup, hperp _ hum, hup0, hum0, hwup, hwum, hQup, hQum⟩

end Eigen

end CFSG.ClassicalInvolution.RouteD.TWS7
