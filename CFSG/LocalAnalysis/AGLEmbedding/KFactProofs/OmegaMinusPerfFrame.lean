module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfField
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfExt

public section

namespace CFSG.AGLEmbedding.OmegaMinusPerf

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.AGLEmbedding.OmegaMinusCent
  CFSG.LinearAlgebra

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V}

theorem polar_sum_right {ι : Type*} (Q : QuadraticForm (ZMod 2) V) (u : V) (w : ι → V)
    (s : Finset ι) : polar Q u (∑ i ∈ s, w i) = ∑ i ∈ s, polar Q u (w i) := by
  have := map_sum (polarBilin Q u) w s
  simpa only [polarBilin_apply_apply] using this

theorem map_sum_of_orthogonal {ι : Type*} [DecidableEq ι] (Q : QuadraticForm (ZMod 2) V)
    (w : ι → V) (h : ∀ i j, i ≠ j → polar Q (w i) (w j) = 0) (s : Finset ι) :
    Q (∑ i ∈ s, w i) = ∑ i ∈ s, Q (w i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, QuadraticMap.map_add Q, ih, polar_sum_right]
    rw [Finset.sum_eq_zero fun i hi => h a i fun hai => ha (hai ▸ hi), add_zero]

structure Frame (Q : QuadraticForm (ZMod 2) V) (x : V ≃ₗ[ZMod 2] V) (k : ℕ) where
  P : Fin k → AnisoPair Q
  orth : ∀ i j, i ≠ j → (P i).Orth (P j)
  b_eq : ∀ i, (P i).b = x (P i).a
  x_b : ∀ i, x (P i).b = (P i).a + (P i).b

variable {k : ℕ} (F : Frame Q x k)

@[expose] noncomputable def Frame.psi : (Fin k → OmegaField) →ₗ[ZMod 2] V :=
  ∑ i : Fin k, ((omegaRe ∘ₗ (LinearMap.proj i : (Fin k → OmegaField) →ₗ[ZMod 2] OmegaField)
      ).smulRight (F.P i).a +
    (omegaIm ∘ₗ (LinearMap.proj i : (Fin k → OmegaField) →ₗ[ZMod 2] OmegaField)
      ).smulRight (F.P i).b)

theorem Frame.psi_apply (z : Fin k → OmegaField) :
    F.psi z = ∑ i, (omegaRe (z i) • (F.P i).a + omegaIm (z i) • (F.P i).b) := by
  simp [Frame.psi, LinearMap.sum_apply]

@[expose] noncomputable def Frame.coord : V →ₗ[ZMod 2] (Fin k → OmegaField) :=
  LinearMap.pi fun i =>
    Algebra.linearMap (ZMod 2) OmegaField ∘ₗ (polarBilin Q).flip (F.P i).b +
      omega • (Algebra.linearMap (ZMod 2) OmegaField ∘ₗ (polarBilin Q).flip (F.P i).a)

theorem Frame.coord_apply (v : V) (i : Fin k) :
    F.coord v i = algebraMap (ZMod 2) OmegaField (polar Q v (F.P i).b) +
      omega * algebraMap (ZMod 2) OmegaField (polar Q v (F.P i).a) := by
  simp [Frame.coord]

theorem Frame.polar_psi_b (z : Fin k → OmegaField) (i : Fin k) :
    polar Q (F.psi z) (F.P i).b = omegaRe (z i) := by
  rw [F.psi_apply, polar_comm, polar_sum_right, Finset.sum_eq_single i]
  · rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, (F.P i).polar_ba,
      (F.P i).polar_bb]
    simp
  · intro j _ hji
    have h := F.orth i j (Ne.symm hji)
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h.ba, h.bb]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem Frame.polar_psi_a (z : Fin k → OmegaField) (i : Fin k) :
    polar Q (F.psi z) (F.P i).a = omegaIm (z i) := by
  rw [F.psi_apply, polar_comm, polar_sum_right, Finset.sum_eq_single i]
  · rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, (F.P i).polar_aa,
      (F.P i).polar_ab]
    simp
  · intro j _ hji
    have h := F.orth i j (Ne.symm hji)
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h.aa, h.ab]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem Frame.coord_psi (z : Fin k → OmegaField) : F.coord (F.psi z) = z := by
  funext i
  rw [F.coord_apply, F.polar_psi_b, F.polar_psi_a]
  conv_rhs => rw [eq_re_im (z i)]
  ring

theorem Frame.coord_comp_psi : F.coord ∘ₗ F.psi = LinearMap.id :=
  LinearMap.ext F.coord_psi

theorem Frame.omegaRe_coord (v : V) (i : Fin k) :
    omegaRe (F.coord v i) = polar Q v (F.P i).b := by
  rw [F.coord_apply, mul_comm omega, omegaRe_mk]

theorem Frame.omegaIm_coord (v : V) (i : Fin k) :
    omegaIm (F.coord v i) = polar Q v (F.P i).a := by
  rw [F.coord_apply, mul_comm omega, omegaIm_mk]

theorem Frame.polar_add_psi_coord (v : V) (z : Fin k → OmegaField) :
    polar Q (v + F.psi (F.coord v)) (F.psi z) = 0 := by
  rw [F.psi_apply z, polar_sum_right]
  refine Finset.sum_eq_zero fun j _ => ?_
  have ha : polar Q (v + F.psi (F.coord v)) (F.P j).a = 0 := by
    rw [polar_add_left, F.polar_psi_a, F.omegaIm_coord]
    exact add_self_eq_zero'' _
  have hb : polar Q (v + F.psi (F.coord v)) (F.P j).b = 0 := by
    rw [polar_add_left, F.polar_psi_b, F.omegaRe_coord]
    exact add_self_eq_zero'' _
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, ha, hb]
  simp

theorem AnisoPair.map_smul_add (P : AnisoPair Q) (α β : ZMod 2) :
    Q (α • P.a + β • P.b) = α + β + α * β := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left_eq,
    polar_smul_right_eq, P.Q_a, P.Q_b, P.polar_ab]
  rcases zmod_two_cases' α with rfl | rfl <;> rcases zmod_two_cases' β with rfl | rfl <;> decide

theorem Frame.algebraMap_map_psi (z : Fin k → OmegaField) :
    algebraMap (ZMod 2) OmegaField (Q (F.psi z)) = ∑ i, z i ^ 3 := by
  rw [F.psi_apply, map_sum_of_orthogonal Q _ ?_ Finset.univ, map_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [AnisoPair.map_smul_add, ← cube_mk]
    congr 1
    exact (eq_re_im (z i)).symm
  · intro i j hij
    have h := F.orth i j hij
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h.aa,
      h.ab, h.ba, h.bb, mul_zero, add_zero]

theorem Frame.x_psi (z : Fin k → OmegaField) : x (F.psi z) = F.psi (omega • z) := by
  rw [F.psi_apply, F.psi_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_smul, map_smul, ← F.b_eq, F.x_b]
  simp only [Pi.smul_apply, smul_eq_mul, omegaRe_omega_mul, omegaIm_omega_mul, smul_add, add_smul]
  abel

theorem Frame.coord_x (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (v : V) :
    F.coord (x v) = omega • F.coord v := by
  funext i
  have hxx : x (x (F.P i).b) = (F.P i).a := by
    rw [F.x_b, map_add, ← F.b_eq, F.x_b]
    have := add_self_eq_zero' (F.P i).b
    calc (F.P i).b + ((F.P i).a + (F.P i).b) = (F.P i).a + ((F.P i).b + (F.P i).b) := by abel
      _ = (F.P i).a := by rw [this, add_zero]
  have h1 : polar Q (x v) (F.P i).b = polar Q v (F.P i).a := by
    rw [F.b_eq, polar_map_of_mem hx]
  have h2 : polar Q (x v) (F.P i).a = polar Q v (F.P i).a + polar Q v (F.P i).b := by
    conv_lhs => rw [← hxx, polar_map_of_mem hx, F.x_b, polar_add_right]
  rw [F.coord_apply, h1, h2, Pi.smul_apply, F.coord_apply, smul_eq_mul, map_add]
  linear_combination (-(algebraMap (ZMod 2) OmegaField (polar Q v (F.P i).a))) * omega_sq

open Matrix CFSG.LieType.Universal.Unitary

@[expose] noncomputable def actEquiv (g : GL (Fin k) OmegaField) :
    (Fin k → OmegaField) ≃ₗ[ZMod 2] (Fin k → OmegaField) :=
  LinearEquiv.ofLinearMap
    ((Matrix.mulVecLin (g : Matrix (Fin k) (Fin k) OmegaField)).restrictScalars (ZMod 2))
    ((Matrix.mulVecLin ((g⁻¹ : GL (Fin k) OmegaField) :
      Matrix (Fin k) (Fin k) OmegaField)).restrictScalars (ZMod 2))
    (LinearMap.ext fun a => by
      change (g : Matrix (Fin k) (Fin k) OmegaField) *ᵥ
        (((g⁻¹ : GL (Fin k) OmegaField) : Matrix (Fin k) (Fin k) OmegaField) *ᵥ a) = a
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec])
    (LinearMap.ext fun a => by
      change ((g⁻¹ : GL (Fin k) OmegaField) : Matrix (Fin k) (Fin k) OmegaField) *ᵥ
        ((g : Matrix (Fin k) (Fin k) OmegaField) *ᵥ a) = a
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec])

theorem actEquiv_apply (g : GL (Fin k) OmegaField) (a : Fin k → OmegaField) :
    actEquiv g a = (g : Matrix (Fin k) (Fin k) OmegaField) *ᵥ a :=
  rfl

theorem actEquiv_mul (g h : GL (Fin k) OmegaField) :
    actEquiv (g * h) = actEquiv g * actEquiv h := by
  apply LinearEquiv.ext
  intro a
  rw [actEquiv_apply, LinearEquiv.mul_apply, actEquiv_apply, actEquiv_apply, Units.val_mul,
    Matrix.mulVec_mulVec]

@[expose] noncomputable def actHom :
    GL (Fin k) OmegaField →* ((Fin k → OmegaField) ≃ₗ[ZMod 2] (Fin k → OmegaField)) :=
  MonoidHom.mk' actEquiv actEquiv_mul

@[expose] noncomputable def Frame.theta : SUid omegaSigma k →* (V ≃ₗ[ZMod 2] V) :=
  (extHom F.coord_comp_psi).comp (actHom.comp (SUid omegaSigma k).subtype)

theorem Frame.theta_apply (g : SUid omegaSigma k) :
    F.theta g = extEquiv F.coord_comp_psi (actEquiv (g : GL (Fin k) OmegaField)) :=
  rfl

@[expose] noncomputable def omegaSmul (k : ℕ) :
    (Fin k → OmegaField) ≃ₗ[ZMod 2] (Fin k → OmegaField) :=
  LinearEquiv.ofLinearMap
    ((omega • (LinearMap.id : (Fin k → OmegaField) →ₗ[OmegaField] (Fin k → OmegaField))
      ).restrictScalars (ZMod 2))
    ((omega ^ 2 • (LinearMap.id : (Fin k → OmegaField) →ₗ[OmegaField] (Fin k → OmegaField))
      ).restrictScalars (ZMod 2))
    (LinearMap.ext fun a => by
      change omega • (omega ^ 2 • a) = a
      rw [smul_smul, ← pow_succ', omega_pow_three, one_smul])
    (LinearMap.ext fun a => by
      change omega ^ 2 • (omega • a) = a
      rw [smul_smul, ← pow_succ, omega_pow_three, one_smul])

theorem omegaSmul_apply (a : Fin k → OmegaField) : omegaSmul k a = omega • a :=
  rfl

theorem Frame.theta_mem_orthogonalGroup (g : SUid omegaSigma k) :
    F.theta g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [Frame.theta_apply]
  refine extEquiv_mem_orthogonalGroup F.coord_comp_psi F.polar_add_psi_coord fun a => ?_
  apply (algebraMap (ZMod 2) OmegaField).injective
  rw [F.algebraMap_map_psi, F.algebraMap_map_psi, actEquiv_apply]
  exact sum_cube_mulVec g.2 a

theorem Frame.theta_commute (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (g : SUid omegaSigma k) : x * F.theta g = F.theta g * x := by
  rw [Frame.theta_apply]
  refine extEquiv_commute F.coord_comp_psi (τ := omegaSmul k) (fun a => F.x_psi a)
    (fun v => F.coord_x hx v) fun a => ?_
  rw [actEquiv_apply, actEquiv_apply, omegaSmul_apply, omegaSmul_apply]
  exact Matrix.mulVec_smul _ _ _

theorem omegaRe_one : omegaRe 1 = 1 := by
  simpa using omegaRe_mk 1 0

theorem omegaIm_one : omegaIm 1 = 0 := by
  simpa using omegaIm_mk 1 0

theorem Frame.psi_single (i : Fin k) : F.psi (Pi.single i 1) = (F.P i).a := by
  rw [F.psi_apply, Finset.sum_eq_single i]
  · simp [omegaRe_one, omegaIm_one]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

@[expose] noncomputable def diagElt (i₀ i₁ : Fin k) : Fin k → OmegaField := fun i =>
  if i = i₀ then omega else if i = i₁ then omega ^ 2 else 1

theorem diagElt_cube (i₀ i₁ i : Fin k) : diagElt i₀ i₁ i ^ 3 = 1 := by
  unfold diagElt
  split_ifs
  · exact omega_pow_three
  · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, omega_pow_three, one_pow]
  · exact one_pow 3

theorem diagElt_same (i₀ i₁ : Fin k) : diagElt i₀ i₁ i₀ = omega := by
  simp [diagElt]

theorem diagElt_second {i₀ i₁ : Fin k} (h : i₀ ≠ i₁) : diagElt i₀ i₁ i₁ = omega ^ 2 := by
  simp [diagElt, h.symm]

theorem prod_diagElt {i₀ i₁ : Fin k} (h : i₀ ≠ i₁) : ∏ i, diagElt i₀ i₁ i = 1 := by
  rw [Finset.prod_eq_mul i₀ i₁ h, diagElt_same, diagElt_second h, ← pow_succ']
  · exact omega_pow_three
  · intro c _ hc
    simp [diagElt, hc.1, hc.2]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] noncomputable def diagGL (i₀ i₁ : Fin k) : GL (Fin k) OmegaField where
  val := Matrix.diagonal (diagElt i₀ i₁)
  inv := Matrix.diagonal (fun i => diagElt i₀ i₁ i ^ 2)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one (n := Fin k) (α := OmegaField) using 2
    funext i
    rw [← pow_succ', diagElt_cube]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one (n := Fin k) (α := OmegaField) using 2
    funext i
    rw [← pow_succ, diagElt_cube]

theorem diagGL_val (i₀ i₁ : Fin k) :
    ((diagGL i₀ i₁ : GL (Fin k) OmegaField) : Matrix (Fin k) (Fin k) OmegaField) =
      Matrix.diagonal (diagElt i₀ i₁) :=
  rfl

theorem diagGL_mem {i₀ i₁ : Fin k} (h : i₀ ≠ i₁) : diagGL i₀ i₁ ∈ SUid omegaSigma k := by
  refine ⟨?_, ?_⟩
  · rw [diagGL_val, Matrix.det_diagonal, prod_diagElt h]
  · rw [diagGL_val, conjTr, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have : (fun i => omegaSigma (diagElt i₀ i₁ i) * diagElt i₀ i₁ i) = fun _ => 1 :=
      funext fun i => by
        rw [omegaSigma_apply, ← diagElt_cube i₀ i₁ i]
        ring
    rw [this]
    exact Matrix.diagonal_one

theorem diagGL_pow_three (i₀ i₁ : Fin k) : diagGL i₀ i₁ ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, diagGL_val, Matrix.diagonal_pow, Units.val_one]
  have : diagElt i₀ i₁ ^ 3 = 1 := funext fun i => diagElt_cube i₀ i₁ i
  rw [this]
  exact Matrix.diagonal_one

theorem Frame.theta_diagGL {i₀ i₁ : Fin k} (h : i₀ ≠ i₁) :
    F.theta ⟨diagGL i₀ i₁, diagGL_mem h⟩ ((F.P i₀).a) = x ((F.P i₀).a) := by
  rw [Frame.theta_apply, ← F.psi_single i₀, extEquiv_apply', F.coord_psi, add_self_eq_zero',
    zero_add, F.x_psi]
  congr 1
  rw [actEquiv_apply]
  change Matrix.diagonal (diagElt i₀ i₁) *ᵥ Pi.single i₀ 1 = omega • Pi.single i₀ 1
  rw [Matrix.diagonal_mulVec_single]
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [diagElt_same]
  · simp [hj]

theorem exists_perfect_of_frame (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {k : ℕ}
    (F : Frame Q x k) (hk : 4 ≤ k) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      D ≤ Subgroup.centralizer {x} ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  have hperf := isPerfect_SUid_omega hk
  refine ⟨F.theta.range, ?_, ?_, Subgroup.isPerfect_iff.1 (Group.IsPerfect.range F.theta), ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact F.theta_mem_orthogonalGroup g
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact F.theta_commute hx g
  · have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    set g₀ : SUid omegaSigma k := ⟨diagGL ⟨0, by omega⟩ ⟨1, by omega⟩, diagGL_mem h01⟩ with hg₀
    have hcube : F.theta g₀ ^ 3 = 1 := by
      rw [← map_pow]
      have : g₀ ^ 3 = 1 := Subtype.ext (diagGL_pow_three _ _)
      rw [this, map_one]
    have hne : F.theta g₀ ≠ 1 := by
      intro h1
      have h2 := F.theta_diagGL h01
      rw [← hg₀, h1, ← F.b_eq] at h2
      exact (F.P _).a_ne_b h2
    have hord : orderOf (F.theta g₀) = 3 := orderOf_eq_prime hcube hne
    have := Subgroup.orderOf_dvd_natCard F.theta.range (⟨g₀, rfl⟩ : F.theta g₀ ∈ F.theta.range)
    rwa [hord] at this

end CFSG.AGLEmbedding.OmegaMinusPerf
