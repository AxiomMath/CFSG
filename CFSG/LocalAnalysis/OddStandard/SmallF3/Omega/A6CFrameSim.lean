module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CFrameRep
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CMatLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {n : ℕ} {c : ZMod 3}

private lemma a6cFrameRep_eq_toMatrixAlgEquiv (fr : NFrame Q (Fin n) c) (γ : simGroup Q) :
    a6cFrameRep fr γ = LinearMap.toMatrixAlgEquiv fr.b (γ : V →ₗ[ZMod 3] V) := by
  ext i j
  rw [a6cFrameRep_apply, LinearMap.toMatrixAlgEquiv_apply]
  rfl

private lemma toLinAlgEquiv_equivFun (fr : NFrame Q (Fin n) c)
    (M : Matrix (Fin n) (Fin n) (ZMod 3)) (x : V) :
    fr.b.equivFun (Matrix.toLinAlgEquiv fr.b M x) = M *ᵥ fr.b.equivFun x := by
  rw [Matrix.toLinAlgEquiv_apply]
  simpa only [Module.Basis.equivFun_apply] using
    (Module.Basis.repr_sum_self fr.b (M *ᵥ fr.b.equivFun x))

private lemma equivFun_self_eq_single {e : Module.Basis (Fin n) (ZMod 3) V} (i : Fin n) :
    e.equivFun (e i) = Pi.single i (1 : ZMod 3) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_eq_pi_single]

private lemma sum_sq_eq_dotProduct (v : Fin n → ZMod 3) :
    (∑ i, (v i) ^ 2) = v ⬝ᵥ v := by
  change ∑ i, (v i) ^ 2 = ∑ i, v i * v i
  exact Finset.sum_congr rfl (fun i _ => by rw [sq])

private lemma sum_sq_mulVec (M : Matrix (Fin n) (Fin n) (ZMod 3)) (v : Fin n → ZMod 3) :
    ∑ i, (M *ᵥ v) i ^ 2 = v ⬝ᵥ ((Mᵀ * M) *ᵥ v) := by
  rw [sum_sq_eq_dotProduct (M *ᵥ v),
    ← Matrix.dotProduct_transpose_mulVec (A := M) (x := v) (y := M *ᵥ v),
    Matrix.mulVec_mulVec]

private lemma frame_polar_eq (fr : NFrame Q (Fin n) c) :
    ∀ x y : V, QuadraticMap.polar Q x y =
      fr.b.equivFun x ⬝ᵥ ((2 * c) • 1) *ᵥ fr.b.equivFun y := by
  set Bc : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3) :=
    LinearMap.BilinForm.comp (QuadraticMap.polarBilin Q)
      (fr.b.equivFun.symm : (Fin n → ZMod 3) →ₗ[ZMod 3] V)
      (fr.b.equivFun.symm : (Fin n → ZMod 3) →ₗ[ZMod 3] V) with hBc
  have hsingle : ∀ i : Fin n, fr.b.equivFun (fr.b i) = Pi.single i (1 : ZMod 3) :=
    fun i => equivFun_self_eq_single i
  have hsymm : ∀ x : V,
      (fr.b.equivFun.symm : (Fin n → ZMod 3) →ₗ[ZMod 3] V) (fr.b.equivFun x) = x := by
    intro x
    exact LinearEquiv.symm_apply_apply fr.b.equivFun x
  have hs : ∀ i : Fin n,
      (fr.b.equivFun.symm : (Fin n → ZMod 3) →ₗ[ZMod 3] V) (Pi.single i (1 : ZMod 3))
        = fr.b i := by
    intro i
    rw [← hsingle i]
    exact hsymm (fr.b i)
  have hmat : LinearMap.BilinForm.toMatrix' Bc = (2 * c) • 1 := by
    rw [hBc]
    ext i j
    rw [LinearMap.BilinForm.toMatrix'_apply, LinearMap.BilinForm.comp_apply,
      QuadraticMap.polarBilin_apply_apply, hs i, hs j]
    by_cases hij : i = j
    · subst hij
      rw [QuadraticMap.polar_self, fr.norm]
      simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    · rw [fr.orth i j hij]
      simp [Matrix.smul_apply, Matrix.one_apply, hij]
  have hB : Bc = Matrix.toBilin' ((2 * c) • 1) := by
    rw [← Matrix.toBilin'_toMatrix' Bc, hmat]
  intro x y
  have h1 : QuadraticMap.polar Q x y = Bc (fr.b.equivFun x) (fr.b.equivFun y) := by
    rw [hBc, LinearMap.BilinForm.comp_apply, QuadraticMap.polarBilin_apply_apply,
      hsymm x, hsymm y]
  rw [h1, hB, Matrix.toBilin'_apply']

private lemma mul_transpose_mul_eq_smul (e : Module.Basis (Fin n) (ZMod 3) V)
    (J : Matrix (Fin n) (Fin n) (ZMod 3)) (μ : ZMod 3) (f : V →ₗ[ZMod 3] V)
    (M : Matrix (Fin n) (Fin n) (ZMod 3))
    (hpol : ∀ x y : V, QuadraticMap.polar Q x y = e.equivFun x ⬝ᵥ J *ᵥ e.equivFun y)
    (hM : ∀ x : V, e.equivFun (f x) = M *ᵥ e.equivFun x)
    (hsim : ∀ x y : V, QuadraticMap.polar Q (f x) (f y) = μ * QuadraticMap.polar Q x y) :
    Mᵀ * J * M = μ • J := by
  have hsingle : ∀ i : Fin n, e.equivFun (e i) = Pi.single i (1 : ZMod 3) :=
    fun i => equivFun_self_eq_single i
  have hentry : ∀ N : Matrix (Fin n) (Fin n) (ZMod 3), ∀ i j,
      N i j = Pi.single i (1 : ZMod 3) ⬝ᵥ N *ᵥ Pi.single j (1 : ZMod 3) := by
    intro N i j
    rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]
    rfl
  ext i j
  have h1 : (Mᵀ * J * M) i j =
      (M *ᵥ Pi.single i 1) ⬝ᵥ J *ᵥ (M *ᵥ Pi.single j 1) := by
    rw [hentry (Mᵀ * J * M) i j, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (Pi.single i 1) Mᵀ, Matrix.vecMul_transpose]
  rw [h1]
  have hi : M *ᵥ Pi.single i (1 : ZMod 3) = e.equivFun (f (e i)) := by
    rw [← hsingle i, hM (e i)]
  have hj : M *ᵥ Pi.single j (1 : ZMod 3) = e.equivFun (f (e j)) := by
    rw [← hsingle j, hM (e j)]
  rw [hi, hj, ← hpol (f (e i)) (f (e j)), hsim, hpol (e i) (e j), hsingle i, hsingle j,
    ← hentry J i j, Matrix.smul_apply, smul_eq_mul]

private lemma exists_unit_of_simMat {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 3)}
    (hM : A6CSimMat M) :
    ∃ ε : (ZMod 3)ˣ, M * Mᵀ = (ε : ZMod 3) • 1 ∧ Mᵀ * M = (ε : ZMod 3) • 1 := by
  rw [A6CSimMat.eq_def] at hM
  rcases hM with h | h
  · refine ⟨1, by simpa using h, ?_⟩
    simpa using (mul_eq_one_comm.mp h)
  · refine ⟨-1, by simpa using h, ?_⟩
    have h2 : M * (-Mᵀ) = 1 := by rw [Matrix.mul_neg, h, neg_neg]
    have h3 : (-Mᵀ) * M = 1 := mul_eq_one_comm.mp h2
    rw [Matrix.neg_mul] at h3
    have h4 : Mᵀ * M = -1 := neg_eq_iff_eq_neg.mp h3
    simpa using h4

theorem a6cFrameRep_sim (fr : NFrame Q (Fin n) c) (hc : c ≠ 0) (γ : simGroup Q) :
    A6CSimMat (a6cFrameRep fr γ) := by
  obtain ⟨lam, hlam⟩ := γ.2
  set M : Matrix (Fin n) (Fin n) (ZMod 3) := a6cFrameRep fr γ with hMdef
  have hM : ∀ x : V, fr.b.equivFun ((γ : V →ₗ[ZMod 3] V) x) = M *ᵥ fr.b.equivFun x := by
    intro x
    have hto : (γ : V →ₗ[ZMod 3] V) = Matrix.toLinAlgEquiv fr.b M := by
      rw [hMdef, a6cFrameRep_eq_toMatrixAlgEquiv, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
    rw [hto]
    exact toLinAlgEquiv_equivFun fr M x
  have hsim : ∀ x y : V,
      QuadraticMap.polar Q ((γ : V ≃ₗ[ZMod 3] V) x) ((γ : V ≃ₗ[ZMod 3] V) y) =
        (lam : ZMod 3) * QuadraticMap.polar Q x y := by
    intro x y
    simp only [QuadraticMap.polar]
    rw [← map_add, hlam, hlam, hlam]
    ring
  have hgram := mul_transpose_mul_eq_smul fr.b ((2 * c) • 1) (lam : ZMod 3)
    ((γ : V →ₗ[ZMod 3] V)) M (frame_polar_eq fr) hM hsim
  have hcancel : (2 * c) ≠ 0 := mul_ne_zero (by decide) hc
  have hMM : Mᵀ * M = (lam : ZMod 3) • 1 := by
    have h' : (2 * c) • (Mᵀ * M) = (2 * c) • ((lam : ZMod 3) • 1) := by
      calc (2 * c) • (Mᵀ * M)
          = Mᵀ * ((2 * c) • 1) * M := by
            rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        _ = (lam : ZMod 3) • ((2 * c) • 1) := hgram
        _ = (2 * c) • ((lam : ZMod 3) • 1) := by
            rw [smul_smul, smul_smul, mul_comm (lam : ZMod 3) (2 * c)]
    exact (IsUnit.smul_left_cancel (isUnit_iff_ne_zero.mpr hcancel)).mp h'
  rcases aux_unit_eq_one_or_neg_one lam with hcase | hcase
  · have hMM1 : Mᵀ * M = 1 := by
      rw [hcase] at hMM
      simpa using hMM
    exact Or.inl (mul_eq_one_comm.mp hMM1)
  · have hMM1 : Mᵀ * M = -1 := by
      rw [hcase] at hMM
      simpa using hMM
    have h2 : (-Mᵀ) * M = 1 := by rw [Matrix.neg_mul, hMM1, neg_neg]
    have h3 : M * (-Mᵀ) = 1 := mul_eq_one_comm.mp h2
    rw [Matrix.mul_neg] at h3
    exact Or.inr (neg_eq_iff_eq_neg.mp h3)

theorem a6cFrameRep_surj (fr : NFrame Q (Fin n) c) (hc : c ≠ 0)
    {M : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M) :
    ∃ γ : simGroup Q, a6cFrameRep fr γ = M := by
  obtain ⟨ε, hε, hε'⟩ := exists_unit_of_simMat hM
  have hinv : ((↑(ε⁻¹) : ZMod 3)) * (↑ε : ZMod 3) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hM1 : M * ((↑(ε⁻¹) : ZMod 3) • Mᵀ) = 1 := by
    rw [Matrix.mul_smul, hε, smul_smul, hinv, one_smul]
  have hM2 : ((↑(ε⁻¹) : ZMod 3) • Mᵀ) * M = 1 := mul_eq_one_comm.mp hM1
  let fL : V →ₗ[ZMod 3] V := Matrix.toLinAlgEquiv fr.b M
  let gL : V →ₗ[ZMod 3] V := Matrix.toLinAlgEquiv fr.b ((↑(ε⁻¹) : ZMod 3) • Mᵀ)
  have hfg : fL.comp gL = LinearMap.id := by
    show (Matrix.toLinAlgEquiv fr.b M).comp
      (Matrix.toLinAlgEquiv fr.b ((↑(ε⁻¹) : ZMod 3) • Mᵀ)) = LinearMap.id
    rw [← Matrix.toLinAlgEquiv_mul, hM1, Matrix.toLinAlgEquiv_one]
  have hgf : gL.comp fL = LinearMap.id := by
    show (Matrix.toLinAlgEquiv fr.b ((↑(ε⁻¹) : ZMod 3) • Mᵀ)).comp
      (Matrix.toLinAlgEquiv fr.b M) = LinearMap.id
    rw [← Matrix.toLinAlgEquiv_mul, hM2, Matrix.toLinAlgEquiv_one]
  let σ : V ≃ₗ[ZMod 3] V := LinearEquiv.ofLinearMap fL gL hfg hgf
  have hσ : IsSimilitude Q σ ε := by
    intro x
    change Q (Matrix.toLinAlgEquiv fr.b M x) = (↑ε : ZMod 3) * Q x
    have hv : fr.b.equivFun (Matrix.toLinAlgEquiv fr.b M x) = M *ᵥ fr.b.equivFun x :=
      toLinAlgEquiv_equivFun fr M x
    have hS : (∑ i, (fr.b.equivFun (Matrix.toLinAlgEquiv fr.b M x) i) ^ 2) =
        (↑ε : ZMod 3) * (∑ i, (fr.b.equivFun x i) ^ 2) := by
      rw [hv, sum_sq_mulVec, hε', Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul]
      congr 1
      exact (sum_sq_eq_dotProduct (fr.b.equivFun x)).symm
    have h1 := fr.map_eq (Matrix.toLinAlgEquiv fr.b M x)
    have h2 := fr.map_eq x
    rw [h1, h2]
    simp_rw [← Module.Basis.equivFun_apply]
    rw [hS]
    ring
  refine ⟨⟨σ, ⟨ε, hσ⟩⟩, ?_⟩
  have hcoe : ((⟨σ, ⟨ε, hσ⟩⟩ : simGroup Q) : V →ₗ[ZMod 3] V) =
      Matrix.toLinAlgEquiv fr.b M := rfl
  rw [a6cFrameRep_eq_toMatrixAlgEquiv, hcoe, LinearMap.toMatrixAlgEquiv_toLinAlgEquiv]

end CFSG.OddStandard.SmallF3.Omega
