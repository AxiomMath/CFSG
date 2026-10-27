module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometry

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Matrix
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry

@[expose] noncomputable def matLin (n : ℕ) (A : Matrix (Fin n) (Fin n) F9) :
    (Fin n → F9) →ₗ[ZMod 3] (Fin n → F9) :=
  (Matrix.mulVecLin A).restrictScalars (ZMod 3)

theorem matLin_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) F9) (x : Fin n → F9) :
    matLin n A x = A *ᵥ x := rfl

@[expose] noncomputable def glEquiv (n : ℕ) (A : GL (Fin n) F9) :
    (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9) :=
  LinearEquiv.ofLinear (matLin n (A : Matrix (Fin n) (Fin n) F9))
    (matLin n ((A⁻¹ : GL (Fin n) F9) : Matrix (Fin n) (Fin n) F9))
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, matLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.one_mulVec, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, matLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mulVec, LinearMap.id_apply])

theorem glEquiv_apply {n : ℕ} (A : GL (Fin n) F9) (x : Fin n → F9) :
    glEquiv n A x = (A : Matrix (Fin n) (Fin n) F9) *ᵥ x := rfl

@[expose] noncomputable def glToLin (n : ℕ) :
    GL (Fin n) F9 →* ((Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) where
  toFun := glEquiv n
  map_one' := LinearEquiv.ext fun x => by
    simp [glEquiv_apply]
  map_mul' A B := LinearEquiv.ext fun x => by
    simp [glEquiv_apply, Matrix.mulVec_mulVec]

theorem glToLin_apply {n : ℕ} (A : GL (Fin n) F9) (x : Fin n → F9) :
    glToLin n A x = (A : Matrix (Fin n) (Fin n) F9) *ᵥ x := rfl

theorem uid_isometry {n : ℕ} (A : Uid σ9 n) (x : Fin n → F9) :
    hermForm n (glToLin n (A : GL (Fin n) F9) x) = hermForm n x := by
  rw [glToLin_apply, hermForm_eq_re, hermForm_eq_re]
  exact congrArg QuadraticAlgebra.re (A.2 x x)

@[expose] noncomputable def uidToOrth (n : ℕ) : Uid σ9 n →* OGroup (hermForm n) :=
  ((glToLin n).comp (Uid σ9 n).subtype).codRestrict
    (TauCeti.QuadraticMap.orthogonalGroup (hermForm n))
    fun A => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => uid_isometry A x

theorem coe_uidToOrth {n : ℕ} (A : Uid σ9 n) (x : Fin n → F9) :
    ((uidToOrth n A : OGroup (hermForm n)) : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) x =
      ((A : GL (Fin n) F9) : Matrix (Fin n) (Fin n) F9) *ᵥ x := rfl

theorem uidToOrth_injective (n : ℕ) : Function.Injective (uidToOrth n) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  have := congrArg (fun g : OGroup (hermForm n) =>
    (g : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) x) h
  simpa only [coe_uidToOrth] using this

theorem uidToOrth_comm_omega {n : ℕ} (A : Uid σ9 n) :
    uidToOrth n A * omegaOrth n = omegaOrth n * uidToOrth n A := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change ((A : GL (Fin n) F9) : Matrix (Fin n) (Fin n) F9) *ᵥ (omega9 • x) =
    omega9 • (((A : GL (Fin n) F9) : Matrix (Fin n) (Fin n) F9) *ᵥ x)
  exact Matrix.mulVec_smul _ _ _

theorem smul_map_of_comm {n : ℕ} (g : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9))
    (hω : ∀ x, g (omega9 • x) = omega9 • g x) (a : F9) (x : Fin n → F9) :
    g (a • x) = a • g x := by
  have ha : a = a.re • (1 : F9) + a.im • omega9 :=
    (QuadraticAlgebra.re_smul_add_im_smul a).symm
  conv_lhs => rw [ha]
  conv_rhs => rw [ha]
  simp only [add_smul, smul_assoc, one_smul, map_add, map_smul, hω]

theorem exists_matrix_of_smul {n : ℕ} (g : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9))
    (hsm : ∀ (a : F9) x, g (a • x) = a • g x) :
    ∃ M : Matrix (Fin n) (Fin n) F9, ∀ x, g x = M *ᵥ x := by
  refine ⟨Matrix.of fun i j => g (Pi.single j 1) i, fun x => ?_⟩
  funext i
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (Pi.single j (x j) : Fin n → F9) = x j • Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  rw [h, hsm]
  simp [mul_comm]

theorem polar_orth {n : ℕ} (h : OGroup (hermForm n)) (x y : Fin n → F9) :
    QuadraticMap.polar (hermForm n) ((h : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) x)
      ((h : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) y) = QuadraticMap.polar (hermForm n) x y := by
  have hq := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h.2
  simp only [QuadraticMap.polar, ← map_add, hq]

theorem exists_uid_of_comm {n : ℕ} {g : OGroup (hermForm n)}
    (hg : g * omegaOrth n = omegaOrth n * g) : ∃ A : Uid σ9 n, uidToOrth n A = g := by
  have hω : ∀ h : OGroup (hermForm n), h * omegaOrth n = omegaOrth n * h → ∀ x,
      (h : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) (omega9 • x) =
        omega9 • (h : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) x := by
    intro h hh x
    exact congrArg (fun k : OGroup (hermForm n) =>
      (k : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) x) hh
  have hginv : g⁻¹ * omegaOrth n = omegaOrth n * g⁻¹ := by
    calc g⁻¹ * omegaOrth n = g⁻¹ * (omegaOrth n * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * omegaOrth n) * g⁻¹ := by rw [hg]
      _ = omegaOrth n * g⁻¹ := by group
  obtain ⟨M, hM⟩ := exists_matrix_of_smul (g : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9))
    (smul_map_of_comm _ (hω g hg))
  obtain ⟨M', hM'⟩ := exists_matrix_of_smul ((g⁻¹ : OGroup (hermForm n)) :
    (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) (smul_map_of_comm _ (hω _ hginv))
  have h1 : M * M' = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, ← hM', ← hM, Matrix.one_mulVec]
    exact congrArg (fun k : OGroup (hermForm n) =>
      (k : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) x) (mul_inv_cancel g)
  have h2 : M' * M = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, ← hM, ← hM', Matrix.one_mulVec]
    exact congrArg (fun k : OGroup (hermForm n) =>
      (k : (Fin n → F9) ≃ₗ[ZMod 3] (Fin n → F9)) x) (inv_mul_cancel g)
  let A : GL (Fin n) F9 := ⟨M, M', h1, h2⟩
  have hAU : A ∈ Uid σ9 n := by
    intro x y
    change herm σ9 (M *ᵥ x) (M *ᵥ y) = herm σ9 x y
    rw [← hM, ← hM, herm9_eq, herm9_eq, polar_orth g, ← hω g hg, polar_orth g]
  refine ⟨⟨A, hAU⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact (hM x).symm

end CFSG.OddStandard.SmallF3.Omega
