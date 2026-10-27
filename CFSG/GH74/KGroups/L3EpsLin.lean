module

public import CFSG.GH74.KGroups.L3EpsTest
public import CFSG.GH74.KGroups.L3EpsAbs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification
open scoped MatrixGroups

section Theta

variable {K : Type} [Field K]

@[expose] noncomputable def theta (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ) : MulAut SL(3, K) :=
  CatalogueBHigherLinearAction.slConjugation 3 K A * CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
    CatalogueBGraphForm.slGraphAut 3 K ^ ε

theorem descendAut_theta (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ) :
    descendAut 3 K (theta A σ ε) = conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε := by
  rw [theta, map_mul, map_mul, map_pow]
  rfl

theorem coe_theta_zero (A : GL (Fin 3) K) (σ : K ≃+* K) (g : SL(3, K)) :
    ((theta A σ 0 g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map σ *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [theta, pow_zero, mul_one, MulAut.mul_apply]
  exact CatalogueBHigherLinearAction.slConjugation_matrix 3 K A _

theorem coe_theta_one (A : GL (Fin 3) K) (σ : K ≃+* K) (g : SL(3, K)) :
    ((theta A σ 1 g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) *
        (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ).map σ *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [theta, pow_one, MulAut.mul_apply]
  exact CatalogueBHigherLinearAction.slConjugation_matrix 3 K A _

theorem trace_conj_gl (A : GL (Fin 3) K) (M : Matrix (Fin 3) (Fin 3) K) :
    ((A : Matrix (Fin 3) (Fin 3) K) * M * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace =
      M.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem trace_theta_zero (A : GL (Fin 3) K) (σ : K ≃+* K) (g : SL(3, K)) :
    ((theta A σ 0 g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace =
      σ ((g : Matrix (Fin 3) (Fin 3) K).trace) := by
  rw [coe_theta_zero, trace_conj_gl]
  exact (AddMonoidHom.map_trace (σ : K →+* K).toAddMonoidHom _).symm

theorem trace_theta_one (A : GL (Fin 3) K) (σ : K ≃+* K) (g : SL(3, K)) :
    ((theta A σ 1 g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace =
      σ (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace) := by
  rw [coe_theta_one, trace_conj_gl, ← Matrix.trace_transpose]
  exact (AddMonoidHom.map_trace (σ : K →+* K).toAddMonoidHom _).symm

end Theta

section Center

variable {K : Type} [Field K]

theorem center_projectiveSL_three_eq_bot : Subgroup.center (projectiveSL 3 K) = ⊥ := by
  have hsimple : IsSimpleGroup (projectiveSL 3 K) := by
    have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by omega)
      (Or.inl le_rfl)).2.1
    exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm.isSimpleGroup
  have hperf : Group.IsPerfect (projectiveSL 3 K) := by
    have := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 3) (by omega) (Or.inl le_rfl)
    exact Group.IsPerfect.ofSurjective
      (f := (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).toMonoidHom)
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projectiveSL 3 K)) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top (projectiveSL 3 K)).2 h
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

end Center

section Core

variable {K : Type} [Field K]

theorem scalars_pow_three {s : SL(3, K)} (hs : s ∈ scalars 3 K) : s ^ 3 = 1 := by
  obtain ⟨c, hc, hsc⟩ := mem_scalars.1 hs
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hsc, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
    ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]

theorem eq_of_proj_eq {a b : SL(3, K)} {j : ℕ} (ha : a ^ 2 ^ j = 1) (hb : b ^ 2 ^ j = 1)
    (hab : proj 3 K a = proj 3 K b) : a = b :=
  eq_of_pow_eq_one_of_central (proj 3 K) (scalars 3 K) (scalars_le_center 3 K)
    (fun _ hs => scalars_pow_three hs) (fun _ _ h => proj_eq_proj_iff.1 h) ha hb hab

theorem trace_conj_sl (x g : SL(3, K)) :
    (((x⁻¹ * g * x : SL(3, K))) : Matrix (Fin 3) (Fin 3) K).trace =
      (g : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mul]

theorem trace_cond [Finite K] {S : Subgroup (projectiveSL 3 K)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (projectiveSL 3 K), IsPGroup 2 T → S ≤ T → T ≤ S)
    {φ : MulAut (projectiveSL 3 K)} (hφS : ∀ s ∈ S, φ s = s) {A : GL (Fin 3) K} {σ : K ≃+* K}
    {ε : ℕ} (hφ : φ = conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) {g : SL(3, K)} {j : ℕ}
    (hg : g ^ 2 ^ j = 1) :
    (ε = 0 → σ ((g : Matrix (Fin 3) (Fin 3) K).trace) = (g : Matrix (Fin 3) (Fin 3) K).trace) ∧
      (ε = 1 → σ (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace) =
        (g : Matrix (Fin 3) (Fin 3) K).trace) := by
  have hproj : (proj 3 K g) ^ 2 ^ j = 1 := by rw [← map_pow, hg, map_one]
  obtain ⟨x, hx⟩ := exists_conj_mem_of_isPGroup hS hmax hproj
  obtain ⟨x', rfl⟩ := proj_surjective 3 K x
  set g' : SL(3, K) := x'⁻¹ * g * x' with hg'
  have hg'S : proj 3 K g' ∈ S := by rw [hg', map_mul, map_mul, map_inv]; exact hx
  have hg'pow : g' ^ 2 ^ j = 1 := by
    have : g' = MulAut.conj x'⁻¹ g := by rw [hg', MulAut.conj_apply, inv_inv]
    rw [this, ← map_pow, hg, map_one]
  have hφ' : φ = descendAut 3 K (theta A σ ε) := by rw [descendAut_theta]; exact hφ
  have hΘ : proj 3 K (theta A σ ε g') = proj 3 K g' := by
    rw [← descendAut_proj, ← hφ']
    exact hφS _ hg'S
  have hΘpow : (theta A σ ε g') ^ 2 ^ j = 1 := by rw [← map_pow, hg'pow, map_one]
  have heq : theta A σ ε g' = g' := eq_of_proj_eq hΘpow hg'pow hΘ
  have hinv : ((g'⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace =
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace := by
    have : g'⁻¹ = x'⁻¹ * g⁻¹ * x' := by rw [hg']; group
    rw [this, trace_conj_sl]
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · subst h0
    have := congrArg (fun h : SL(3, K) => (h : Matrix (Fin 3) (Fin 3) K).trace) heq
    simp only [trace_theta_zero, hg', trace_conj_sl] at this
    exact this
  · subst h1
    have := congrArg (fun h : SL(3, K) => (h : Matrix (Fin 3) (Fin 3) K).trace) heq
    simp only [trace_theta_one] at this
    rw [hinv, hg', trace_conj_sl] at this
    exact this

end Core

section FieldPart

variable {K : Type} [Field K]

theorem conj_field_pow (A : GL (Fin 3) K) (σ : K ≃+* K) (m : ℕ) :
    ∃ B : GL (Fin 3) K,
      (conjAut 3 K A * fieldAut 3 K σ) ^ m = conjAut 3 K B * fieldAut 3 K (σ ^ m) := by
  induction m with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * GeneralLinearGroup.map ((σ ^ m : K ≃+* K) : K →+* K) A, ?_⟩
    rw [pow_succ, hB, conjAut_mul_fieldAut_mul B A (σ ^ m) σ, ← pow_succ]

theorem sq_eq_conj_field (A : GL (Fin 3) K) (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1) :
    ∃ B : GL (Fin 3) K,
      (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) ^ 2 =
        conjAut 3 K B * fieldAut 3 K (σ ^ 2) := by
  interval_cases ε
  · obtain ⟨B, hB⟩ := conj_field_pow A σ 2
    exact ⟨B, by rw [pow_zero, mul_one]; exact hB⟩
  · obtain ⟨-, -, -, hδδ, hδc, hδf, -⟩ := standard_automorphism_transport (K := K) (n := 3)
    refine ⟨A * GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose A), ?_⟩
    have e : dualAut 3 K * (conjAut 3 K A * fieldAut 3 K σ) * dualAut 3 K =
        conjAut 3 K (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 K σ := by
      calc dualAut 3 K * (conjAut 3 K A * fieldAut 3 K σ) * dualAut 3 K
          = dualAut 3 K * conjAut 3 K A * 1 * fieldAut 3 K σ * dualAut 3 K := by
            simp only [mul_one, mul_assoc]
        _ = dualAut 3 K * conjAut 3 K A * (dualAut 3 K * dualAut 3 K) * fieldAut 3 K σ *
              dualAut 3 K := by rw [hδδ]
        _ = (dualAut 3 K * conjAut 3 K A * dualAut 3 K) *
              (dualAut 3 K * fieldAut 3 K σ * dualAut 3 K) := by simp only [mul_assoc]
        _ = _ := by rw [hδc A, hδf σ]
    rw [pow_one, sq]
    calc conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K *
          (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K)
        = conjAut 3 K A * fieldAut 3 K σ *
            (dualAut 3 K * (conjAut 3 K A * fieldAut 3 K σ) * dualAut 3 K) := by
          simp only [mul_assoc]
      _ = conjAut 3 K A * fieldAut 3 K σ *
            (conjAut 3 K (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 K σ) := by rw [e]
      _ = _ := by
          rw [conjAut_mul_fieldAut_mul, sq]

theorem sigma_two_pow [Finite K] (A : GL (Fin 3) K) (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1) {k : ℕ}
    (h : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) ^ 2 ^ k = 1) : σ ^ 2 ^ (k + 1) = 1 := by
  obtain ⟨B, hB⟩ := sq_eq_conj_field A σ hε
  have h2 : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ, pow_mul, h, one_pow]
  have h3 : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) ^ 2 ^ (k + 1) =
      ((conjAut 3 K B * fieldAut 3 K (σ ^ 2)) ^ 2 ^ k) := by
    rw [pow_succ', pow_mul, hB]
  rw [h3] at h2
  obtain ⟨B', hB'⟩ := conj_field_pow B (σ ^ 2) (2 ^ k)
  rw [hB'] at h2
  have := (eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (by norm_num) B' _ h2).1
  rw [← pow_mul, ← pow_succ'] at this
  exact this

end FieldPart

section MainLin

variable {K : Type} [Field K] [Finite K]

theorem conj_pow_inner (A : GL (Fin 3) K) {k : ℕ} (h : conjAut 3 K A ^ 2 ^ k = 1) :
    ∃ x : SL(3, K), conjAut 3 K A = MulAut.conj (proj 3 K x) := by
  have h' : conjAut 3 K (A ^ 2 ^ k) * fieldAut 3 K 1 = 1 := by rw [map_pow, map_one, mul_one]; exact h
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (by norm_num) _ 1 h'
  set d : Kˣ := Matrix.GeneralLinearGroup.det A with hd
  have hdet : ∀ u : Kˣ, Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u) = u ^ 3 := by
    intro u
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal]
    simp
  have hdc : d ^ 2 ^ k = c ^ 3 := by
    rw [hd, ← map_pow, ← hc, hdet]
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * 3 + b * (2 ^ k : ℕ) = 1 := by
    have : IsCoprime ((3 : ℕ) : ℤ) ((2 ^ k : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_right k (by norm_num)
    obtain ⟨a, b, hab⟩ := this
    exact ⟨a, b, by push_cast at hab ⊢; linarith⟩
  have hu : (d ^ a * c ^ b) ^ 3 = d := by
    have h1 : d ^ (a * 3 + b * ((2 ^ k : ℕ) : ℤ)) = d := by rw [hab, zpow_one]
    have hcc : (c ^ 3) ^ b = (c ^ b) ^ 3 := by
      rw [← _root_.zpow_natCast c 3, ← _root_.zpow_natCast (c ^ b) 3, ← _root_.zpow_mul,
        ← _root_.zpow_mul, mul_comm]
    have h2 : d ^ (a * 3 + b * ((2 ^ k : ℕ) : ℤ)) = (d ^ a) ^ 3 * (c ^ b) ^ 3 := by
      rw [_root_.zpow_add, _root_.zpow_mul d a 3, _root_.zpow_mul' d b ((2 ^ k : ℕ) : ℤ),
        _root_.zpow_natCast, hdc, hcc]
      simp
    rw [mul_pow, ← h2, h1]
  set u : Kˣ := d ^ a * c ^ b with hudef
  set A' : GL (Fin 3) K := A * GeneralLinearGroup.scalar (Fin 3) u⁻¹ with hA'
  have hA'det : (A' : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have : Matrix.GeneralLinearGroup.det A' = 1 := by
      rw [hA', map_mul, hdet, inv_pow, hu, ← hd, mul_inv_cancel]
    have h1 := congrArg (fun v : Kˣ => (v : K)) this
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1
  let x : SL(3, K) := ⟨(A' : Matrix (Fin 3) (Fin 3) K), hA'det⟩
  refine ⟨x, ?_⟩
  have hx : Matrix.SpecialLinearGroup.toGL x = A' := Units.ext rfl
  rw [← conjAut_toGL, hx, hA', map_mul, conjAut_scalar, mul_one]

theorem lin_two_aut_inner (hK2 : ringChar K ≠ 2) {S : Subgroup (projectiveSL 3 K)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (projectiveSL 3 K), IsPGroup 2 T → S ≤ T → T ≤ S)
    {φ : MulAut (projectiveSL 3 K)} {k : ℕ} (hφk : φ ^ 2 ^ k = 1) (hφS : ∀ s ∈ S, φ s = s) :
    ∃ x : SL(3, K), φ = MulAut.conj (proj 3 K x) := by
  obtain ⟨A, σ, ε, hε, hφ⟩ := (automorphism_generation (K := K) (n := 3) (by norm_num)).2 φ
  have hσk : σ ^ 2 ^ (k + 1) = 1 := sigma_two_pow A σ hε (hφ ▸ hφk)
  have hcond : ∀ {g : SL(3, K)} {j : ℕ}, g ^ 2 ^ j = 1 →
      (ε = 0 → σ ((g : Matrix (Fin 3) (Fin 3) K).trace) = (g : Matrix (Fin 3) (Fin 3) K).trace) ∧
        (ε = 1 → σ (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace) =
          (g : Matrix (Fin 3) (Fin 3) K).trace) :=
    fun hg => trace_cond hS hmax hφS hφ hg
  have hσε : σ = 1 ∧ ε = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with h0 | h1
    · refine ⟨?_, h0⟩
      by_contra hne
      obtain ⟨m, hm1, hm2⟩ := exists_pow_involution hne hσk
      obtain ⟨g, ⟨j, hg⟩, hgt, -⟩ := exists_trace_moved_lin hm1 hm2 hK2
      exact hgt (ringEquiv_pow_fix ((hcond hg).1 h0) m)
    · exfalso
      have hσ2 : σ * σ = 1 := by
        by_contra hne
        have h2 : σ ^ 2 ≠ 1 := by rwa [sq]
        have hk2 : (σ ^ 2) ^ 2 ^ k = 1 := by rw [← pow_mul, ← pow_succ']; exact hσk
        obtain ⟨m, hm1, hm2⟩ := exists_pow_involution h2 hk2
        obtain ⟨g, ⟨j, hg⟩, hgt, -⟩ := exists_trace_moved_lin hm1 hm2 hK2
        have h3 := (hcond hg).2 h1
        have hginv : (g⁻¹) ^ 2 ^ j = 1 := by rw [inv_pow, hg, inv_one]
        have h4 := (hcond hginv).2 h1
        rw [inv_inv] at h4
        have h5 : (σ ^ 2) ((g : Matrix (Fin 3) (Fin 3) K).trace) =
            (g : Matrix (Fin 3) (Fin 3) K).trace := by
          rw [sq, RingAut.mul_apply, h4, h3]
        exact hgt (ringEquiv_pow_fix h5 m)
      have hσ1 : σ = 1 := by
        by_contra hne
        obtain ⟨g, ⟨j, hg⟩, hgt, hginv⟩ := exists_trace_moved_lin hne hσ2 hK2
        have h3 := (hcond hg).2 h1
        rw [hginv] at h3
        exact hgt h3
      obtain ⟨g, ⟨j, hg⟩, hgt⟩ := exists_trace_ne_inv_lin (K := K) hK2
      have h3 := (hcond hg).2 h1
      rw [hσ1] at h3
      exact hgt (by simpa using h3)
  obtain ⟨hσ, hε0⟩ := hσε
  subst hσ hε0
  have hφc : φ = conjAut 3 K A := by rw [hφ, map_one, pow_zero, mul_one, mul_one]
  obtain ⟨x, hx⟩ := conj_pow_inner A (by rw [← hφc]; exact hφk)
  exact ⟨x, hφc.trans hx⟩

theorem lin_key (hK2 : ringChar K ≠ 2) {S : Subgroup (projectiveSL 3 K)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (projectiveSL 3 K), IsPGroup 2 T → S ≤ T → T ≤ S)
    {φ : MulAut (projectiveSL 3 K)} {k : ℕ} (hφk : φ ^ 2 ^ k = 1) (hφS : ∀ s ∈ S, φ s = s) :
    ∃ z ∈ S, (∀ s ∈ S, s * z = z * s) ∧ φ = MulAut.conj z := by
  obtain ⟨x, hx⟩ := lin_two_aut_inner hK2 hS hmax hφk hφS
  have h := mem_of_conj_fixes center_projectiveSL_three_eq_bot hS hmax (z := proj 3 K x) (k := k)
    (by rw [← hx]; exact hφk) (by intro s hs; rw [← hx]; exact hφS s hs)
  exact ⟨proj 3 K x, h.1, h.2, hx⟩

end MainLin

end CFSG.GH74.KGroups.L3Eps
