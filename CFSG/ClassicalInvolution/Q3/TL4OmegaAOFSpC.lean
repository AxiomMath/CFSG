module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpB
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFGBlock
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpG

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SpL

open Matrix CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Q3.TL4.Gauss
open CFSG.LocalAnalysis.ComponentInitial (SymplecticTorusWeyl.mem_statedSp_iff)
open scoped MatrixGroups

section GLEquiv

variable {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]

variable (F ι) in
@[expose] noncomputable def glEquiv : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv F _)

theorem glEquiv_apply (g : GL ι F) (v : ι → F) :
    glEquiv F ι g v = (g : Matrix ι ι F) *ᵥ v := by
  simp [glEquiv]

theorem glEquiv_symm_mulVec (g : (ι → F) ≃ₗ[F] (ι → F)) (v : ι → F) :
    (((glEquiv F ι).symm g : GL ι F) : Matrix ι ι F) *ᵥ v = g v := by
  rw [← glEquiv_apply, MulEquiv.apply_symm_apply]

end GLEquiv

section Conj

variable {K M W : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup W] [Module K W]

@[expose] def conjPhi (φ : M ≃ₗ[K] W) : (M ≃ₗ[K] M) →* (W ≃ₗ[K] W) where
  toFun g := φ.symm.trans (g.trans φ)
  map_one' := LinearEquiv.ext fun w => by simp
  map_mul' g h := LinearEquiv.ext fun w => by simp

end Conj

theorem omega_glLin {F : Type} [Field F] {A : GL (Fin 2 ⊕ Fin 2) F}
    (hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F * A =
      (-1 : F) • formJ 2 F) (u v : Fin 2 ⊕ Fin 2 → F) :
    omega F 2 (glLin A u) (glLin A v) = -omega F 2 u v := by
  rw [glLin_apply, glLin_apply, omega_mulVec hA, neg_one_mul]

section Theta

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)]
  [Module (GaussField F) (Fin 2 ⊕ Fin 2 → F)]
  [IsScalarTower F (GaussField F) (Fin 2 ⊕ Fin 2 → F)] {A : GL (Fin 2 ⊕ Fin 2) F}

theorem exists_beta_eq_one
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = glLin A v)
    (hωa : ∀ u v, omega F 2 (glLin A u) (glLin A v) = -omega F 2 u v) :
    ∃ e f : Fin 2 ⊕ Fin 2 → F, spBilin (omega F 2) hω hωa e f = 1 := by
  classical
  set e : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1
  have he : e ≠ 0 := fun h => by
    have := congrFun h (Sum.inl 0)
    simp [e] at this
  obtain ⟨w, hw⟩ : ∃ w, omega F 2 e w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact he (omega_nondegenerate.1 e hc)
  have hβ : spBilin (omega F 2) hω hωa e w ≠ 0 := fun h => hw (by
    have := congrArg QuadraticAlgebra.re h
    simpa [spBilin_apply] using this)
  refine ⟨e, (spBilin (omega F 2) hω hωa e w)⁻¹ • w, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hβ]

theorem finrank_gauss_four :
    Module.finrank (GaussField F) (Fin 2 ⊕ Fin 2 → F) = 2 := by
  have := finiteDimensional_gauss F (Fin 2 ⊕ Fin 2 → F)
  have h := Module.finrank_mul_finrank F (GaussField F) (Fin 2 ⊕ Fin 2 → F)
  rw [QuadraticAlgebra.finrank_eq_two, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin] at h
  omega

@[expose] noncomputable def phiEquiv
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = glLin A v)
    (hωa : ∀ u v, omega F 2 (glLin A u) (glLin A v) = -omega F 2 u v)
    {e f : Fin 2 ⊕ Fin 2 → F} (hef : spBilin (omega F 2) hω hωa e f = 1) :
    (Fin 2 → GaussField F) ≃ₗ[GaussField F] (Fin 2 ⊕ Fin 2 → F) :=
  have hinj := phiLin_injective (spBilin_skew hω hωa omega_skew)
    (spBilin_self (Q3MFOD.two_ne_zero_of_card_three Fact.out) hω hωa omega_skew) hef
  LinearEquiv.ofBijective (phiLin e f) ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun, finrank_gauss_four])).mp hinj⟩

theorem beta_phiEquiv (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = glLin A v)
    (hωa : ∀ u v, omega F 2 (glLin A u) (glLin A v) = -omega F 2 u v)
    {e f : Fin 2 ⊕ Fin 2 → F} (hef : spBilin (omega F 2) hω hωa e f = 1)
    (x y : Fin 2 → GaussField F) :
    spBilin (omega F 2) hω hωa (phiEquiv hω hωa hef x) (phiEquiv hω hωa hef y) =
      x 0 * y 1 - x 1 * y 0 :=
  beta_phiLin (spBilin_skew hω hωa omega_skew)
    (spBilin_self (Q3MFOD.two_ne_zero_of_card_three Fact.out) hω hωa omega_skew) hef x y

@[expose] noncomputable def theta
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = glLin A v)
    (hωa : ∀ u v, omega F 2 (glLin A u) (glLin A v) = -omega F 2 u v)
    {e f : Fin 2 ⊕ Fin 2 → F} (hef : spBilin (omega F 2) hω hωa e f = 1) :
    SL(2, GaussField F) →* GL (Fin 2 ⊕ Fin 2) F :=
  (glEquiv F (Fin 2 ⊕ Fin 2)).symm.toMonoidHom.comp ((res F).comp
    ((conjPhi (phiEquiv hω hωa hef)).comp Matrix.SpecialLinearGroup.toLin'))

theorem theta_mulVec (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = glLin A v)
    (hωa : ∀ u v, omega F 2 (glLin A u) (glLin A v) = -omega F 2 u v)
    {e f : Fin 2 ⊕ Fin 2 → F} (hef : spBilin (omega F 2) hω hωa e f = 1)
    (X : SL(2, GaussField F)) (v : Fin 2 ⊕ Fin 2 → F) :
    ((theta hω hωa hef X : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      phiEquiv hω hωa hef ((X : Matrix (Fin 2) (Fin 2) (GaussField F)) *ᵥ
        (phiEquiv hω hωa hef).symm v) := by
  rw [theta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, glEquiv_symm_mulVec]
  rfl

end Theta

end CFSG.ClassicalInvolution.Q3.TL4.SpL
