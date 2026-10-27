module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowSData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesMatrix

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic Polynomial

section Det

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module k V]

theorem det_linearConjGL (ψ : (Fin n → k) ≃ₗ[k] V) (f : V ≃ₗ[k] V) :
    ((linearConjGL ψ f : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det =
      LinearMap.det (f : V →ₗ[k] V) := by
  change (CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun k (Fin n))
    (linearConj ψ f)).val.det = _
  rw [CatalogueBAlternatingIsometry.basisMatrixEquiv_val, LinearMap.det_toMatrix]
  have h := LinearMap.det_conj (f : V →ₗ[k] V) ψ.symm
  rw [LinearEquiv.symm_symm] at h
  rw [← h]
  rfl

end Det

section Row

variable {k : Type} [Field k] {m : ℕ} (ν : kˣ)
  (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin m → k))

theorem det_rowSPi (g : GL (Fin 2) (extension (ν : k))) :
    ((rowSPi ν Ψ g : GL (Fin m) k) : Matrix (Fin m) (Fin m) k).det =
      Algebra.norm k (g : Matrix (Fin 2) (Fin 2) (extension (ν : k))).det := by
  rw [rowSPi, MonoidHom.comp_apply, det_linearConjGL]
  have h : ((glRestrict (k := k) 2 g : (Fin 2 → extension (ν : k)) ≃ₗ[k] _) :
      (Fin 2 → extension (ν : k)) →ₗ[k] (Fin 2 → extension (ν : k))) =
      (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) (extension (ν : k)))).restrictScalars k :=
    LinearMap.ext fun v => rfl
  rw [h, LinearMap.det_restrictScalars, LinearMap.det_toLin']

omit [Field k] in
theorem rowSPi_mulVec_apply {k : Type} [Field k] {m : ℕ} (ν : kˣ)
    (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin m → k))
    (g : GL (Fin 2) (extension (ν : k))) (x : Fin 2 → extension (ν : k)) :
    ((rowSPi ν Ψ g : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ Ψ x =
      Ψ ((g : Matrix (Fin 2) (Fin 2) (extension (ν : k))) *ᵥ x) := by
  rw [rowSPi_mulVec, LinearEquiv.symm_apply_apply]

theorem rowSPi_injective : Function.Injective (rowSPi ν Ψ) := by
  intro g h hgh
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  have := congrArg (fun A : GL (Fin m) k => (A : Matrix (Fin m) (Fin m) k) *ᵥ Ψ x) hgh
  simp only [rowSPi_mulVec_apply] at this
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Ψ.injective this

theorem rowSPi_scalar (c : kˣ) :
    rowSPi ν Ψ (GeneralLinearGroup.scalar (Fin 2)
      (Units.map (algebraMap k (extension (ν : k))).toMonoidHom c)) =
      GeneralLinearGroup.scalar (Fin m) c := by
  apply eq_of_mulVec_eq
  intro v
  rw [rowSPi_mulVec, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    scalar_apply, scalar_apply]
  have hE : (diagonal fun _ => ((Units.map (algebraMap k (extension (ν : k))).toMonoidHom c :
      (extension (ν : k))ˣ) : extension (ν : k))) *ᵥ Ψ.symm v = (c : k) • Ψ.symm v := by
    ext i
    simp [mulVec_diagonal, Algebra.smul_def]
  have hk : (diagonal fun _ => (c : k)) *ᵥ v = (c : k) • v := by
    ext i
    simp [mulVec_diagonal]
  rw [hE, map_smul, LinearEquiv.apply_symm_apply, hk]

theorem rowSU_sq : rowSU ν Ψ ^ 2 = GeneralLinearGroup.scalar (Fin m) ν := by
  rw [rowSU, ← map_pow, ← map_pow, ← rowSPi_scalar]
  congr 2
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_rootUnit, extension_root_square]
  rfl

end Row

section Linear

variable {k : Type} [Field k] (ν : kˣ)

theorem smul_of_root_smul (f : (Fin 2 → extension (ν : k)) →ₗ[k] (Fin 2 → extension (ν : k)))
    (hf : ∀ x, f (AdjoinRoot.root (quadraticPolynomial (ν : k)) • x) =
      AdjoinRoot.root (quadraticPolynomial (ν : k)) • f x)
    (e : extension (ν : k)) (x : Fin 2 → extension (ν : k)) : f (e • x) = e • f x := by
  induction e using AdjoinRoot.induction_on with
  | ih p =>
    rw [← AdjoinRoot.aeval_eq]
    induction p using Polynomial.induction_on generalizing x with
    | C a =>
      rw [aeval_C, algebraMap_smul, algebraMap_smul, map_smul]
    | add p q hp hq => rw [map_add, add_smul, add_smul, map_add, hp, hq]
    | monomial j a ih =>
      have h1 : aeval (AdjoinRoot.root (quadraticPolynomial (ν : k))) (C a * X ^ (j + 1)) =
          aeval (AdjoinRoot.root (quadraticPolynomial (ν : k))) (C a * X ^ j) *
            AdjoinRoot.root (quadraticPolynomial (ν : k)) := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      rw [h1, mul_smul, ih, hf, mul_smul]

theorem smul_of_root_smul_neg
    (f : (Fin 2 → extension (ν : k)) →ₗ[k] (Fin 2 → extension (ν : k)))
    (hf : ∀ x, f (AdjoinRoot.root (quadraticPolynomial (ν : k)) • x) =
      -(AdjoinRoot.root (quadraticPolynomial (ν : k)) • f x))
    (e : extension (ν : k)) (x : Fin 2 → extension (ν : k)) :
    f (e • x) = extensionConj ν e • f x := by
  induction e using AdjoinRoot.induction_on with
  | ih p =>
    rw [← AdjoinRoot.aeval_eq]
    induction p using Polynomial.induction_on generalizing x with
    | C a =>
      rw [aeval_C, AlgEquiv.commutes, algebraMap_smul, algebraMap_smul, map_smul]
    | add p q hp hq =>
      rw [map_add, add_smul, map_add, hp, hq, map_add (extensionConj ν), add_smul]
    | monomial j a ih =>
      have h1 : aeval (AdjoinRoot.root (quadraticPolynomial (ν : k))) (C a * X ^ (j + 1)) =
          aeval (AdjoinRoot.root (quadraticPolynomial (ν : k))) (C a * X ^ j) *
            AdjoinRoot.root (quadraticPolynomial (ν : k)) := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      rw [h1, mul_smul, ih, hf, map_mul (extensionConj ν), extensionConj_root]
      simp only [smul_neg, mul_neg, neg_smul, mul_smul]

end Linear

section Kappa

variable {k : Type} [Field k] {m : ℕ} (ν : kˣ)
  (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin m → k))

theorem rowSKappa_mulVec_apply (x : Fin 2 → extension (ν : k)) :
    ((rowSKappa ν Ψ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ Ψ x =
      Ψ (fun i => extensionConj ν (x i)) := by
  rw [rowSKappa, linearConjGL_mulVec, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  rfl

theorem rowSKappa_mul_self : rowSKappa ν Ψ * rowSKappa ν Ψ = 1 := by
  apply eq_of_mulVec_eq
  intro v
  obtain ⟨x, rfl⟩ := Ψ.surjective v
  rw [Units.val_mul, ← mulVec_mulVec, rowSKappa_mulVec_apply, rowSKappa_mulVec_apply,
    Units.val_one, one_mulVec]
  simp only [extensionConj_extensionConj]

theorem det_rowSKappa : ((rowSKappa ν Ψ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k).det = 1 := by
  rw [rowSKappa, det_linearConjGL]
  set γ : extension (ν : k) →ₗ[k] extension (ν : k) := (extensionConj ν).toLinearMap with hγ
  have h1 : ((rowSKappa₀ ν : (Fin 2 → extension (ν : k)) ≃ₗ[k] _) :
      (Fin 2 → extension (ν : k)) →ₗ[k] (Fin 2 → extension (ν : k))) =
      LinearMap.pi (fun i => γ.comp (LinearMap.proj i)) := LinearMap.ext fun x => rfl
  have h2 : γ.comp γ = LinearMap.id := LinearMap.ext fun x => extensionConj_extensionConj ν x
  have h3 : LinearMap.det γ ^ 2 = 1 := by
    rw [sq, ← LinearMap.det_comp, h2, LinearMap.det_id]
  rw [h1, LinearMap.det_pi, Fin.prod_univ_two, ← sq, h3]

theorem rowSKappa_mul_rowSU :
    rowSKappa ν Ψ * rowSU ν Ψ =
      GeneralLinearGroup.scalar (Fin m) (-1) * rowSU ν Ψ * rowSKappa ν Ψ := by
  apply eq_of_mulVec_eq
  intro v
  obtain ⟨x, rfl⟩ := Ψ.surjective v
  rw [Units.val_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec,
    ← mulVec_mulVec, rowSKappa_mulVec_apply, rowSU, rowSPi_mulVec_apply, rowSPi_mulVec_apply,
    rowSKappa_mulVec_apply, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    scalar_apply, scalar_apply]
  have h1 : (diagonal fun _ => ((-1 : kˣ) : k)) *ᵥ
      Ψ ((diagonal fun _ => ((rootUnit ν : (extension (ν : k))ˣ) : extension (ν : k))) *ᵥ
        fun i => extensionConj ν (x i)) =
      Ψ (fun i => -(AdjoinRoot.root (quadraticPolynomial (ν : k)) *
        extensionConj ν (x i))) := by
    have : (diagonal fun _ => ((-1 : kˣ) : k)) *ᵥ (Ψ (fun i =>
        AdjoinRoot.root (quadraticPolynomial (ν : k)) * extensionConj ν (x i))) =
        (-1 : k) • Ψ (fun i => AdjoinRoot.root (quadraticPolynomial (ν : k)) *
          extensionConj ν (x i)) := by
      ext i
      simp [mulVec_diagonal]
    have h2 : (diagonal fun _ => ((rootUnit ν : (extension (ν : k))ˣ) : extension (ν : k))) *ᵥ
        (fun i => extensionConj ν (x i)) = fun i => AdjoinRoot.root (quadraticPolynomial (ν : k)) *
          extensionConj ν (x i) := by
      ext i
      simp [mulVec_diagonal, coe_rootUnit]
    rw [h2, this, ← map_smul]
    congr 1
    ext i
    simp
  rw [h1]
  congr 1
  ext i
  simp only [mulVec_diagonal, coe_rootUnit, map_mul, extensionConj_root, neg_mul]

theorem rowSKappa_conj_rowSPi (g : GL (Fin 2) (extension (ν : k))) :
    rowSKappa ν Ψ * rowSPi ν Ψ g * rowSKappa ν Ψ =
      rowSPi ν Ψ (GeneralLinearGroup.map ((extensionConj ν : extension (ν : k) ≃ₐ[k] _) :
        extension (ν : k) →+* extension (ν : k)) g) := by
  apply eq_of_mulVec_eq
  intro v
  obtain ⟨x, rfl⟩ := Ψ.surjective v
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, rowSKappa_mulVec_apply,
    rowSPi_mulVec_apply, rowSKappa_mulVec_apply, rowSPi_mulVec_apply]
  congr 1
  ext i
  simp only [mulVec, dotProduct, map_sum, map_mul, extensionConj_extensionConj]
  rfl

theorem conjAut_rowSKappa_mem_centralizer :
    conjAut m k (rowSKappa ν Ψ) ∈ centralizer {conjAut m k (rowSU ν Ψ)} := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, rowSKappa_mul_rowSU]
  simp only [map_mul, conjAut_scalar, one_mul]

end Kappa

section Classify

variable {k : Type} [Field k] {m : ℕ} (ν : kˣ) [Fact (¬ IsSquare (ν : k))]
  (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin m → k))

theorem exists_rowSPi_of_commute {X : GL (Fin m) k} (hX : X * rowSU ν Ψ = rowSU ν Ψ * X) :
    ∃ g : GL (Fin 2) (extension (ν : k)), X = rowSPi ν Ψ g := by
  set t := AdjoinRoot.root (quadraticPolynomial (ν : k)) with ht
  set f : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 2 → extension (ν : k)) :=
    (Ψ.trans (CatalogueBProjectiveCoordinates.matrixActionEquiv X)).trans Ψ.symm with hfdef
  have hfapp : ∀ x, f x = Ψ.symm ((X : Matrix (Fin m) (Fin m) k) *ᵥ Ψ x) := fun x => rfl
  have hU : ∀ x, ((rowSU ν Ψ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ Ψ x = Ψ (t • x) := by
    intro x
    rw [rowSU, rowSPi_mulVec_apply, GeneralLinearGroup.coe_scalar, scalar_apply]
    congr 1
    ext i
    simp [mulVec_diagonal, ht, coe_rootUnit]
  have hft : ∀ x, (f : (Fin 2 → extension (ν : k)) →ₗ[k] _) (t • x) = t • f x := by
    intro x
    change f (t • x) = t • f x
    rw [hfapp, hfapp, ← hU, mulVec_mulVec, ← Units.val_mul, hX, Units.val_mul, ← mulVec_mulVec]
    have : ((X : Matrix (Fin m) (Fin m) k) *ᵥ Ψ x) = Ψ (Ψ.symm ((X : Matrix (Fin m) (Fin m) k) *ᵥ
        Ψ x)) := (LinearEquiv.apply_symm_apply _ _).symm
    rw [this, hU, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  have hsmul := smul_of_root_smul ν (f : (Fin 2 → extension (ν : k)) →ₗ[k] _) hft
  set F : (Fin 2 → extension (ν : k)) ≃ₗ[extension (ν : k)] (Fin 2 → extension (ν : k)) :=
    { toFun := f
      invFun := f.symm
      map_add' := f.map_add
      map_smul' := fun e x => hsmul e x
      left_inv := f.left_inv
      right_inv := f.right_inv } with hF
  refine ⟨CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun (extension (ν : k)) (Fin 2))
    F, ?_⟩
  apply eq_of_mulVec_eq
  intro v
  rw [rowSPi_mulVec]
  have h := CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec
    (Pi.basisFun (extension (ν : k)) (Fin 2)) F (Ψ.symm v)
  rw [Pi.basisFun_equivFun] at h
  simp only [LinearEquiv.refl_apply] at h
  change _ = Ψ ((CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun (extension (ν : k)) (Fin 2)) F).val *ᵥ Ψ.symm v)
  rw [h]
  change _ = Ψ (f (Ψ.symm v))
  rw [hfapp, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem rowSPi_commute_rowSU (g : GL (Fin 2) (extension (ν : k))) :
    rowSPi ν Ψ g * rowSU ν Ψ = rowSU ν Ψ * rowSPi ν Ψ g := by
  rw [rowSU, ← map_mul, ← map_mul, GeneralLinearGroup.scalar_commute]

theorem exists_rowSPi_of_anticommute {X : GL (Fin m) k}
    (hX : X * rowSU ν Ψ = GeneralLinearGroup.scalar (Fin m) (-1) * rowSU ν Ψ * X) :
    ∃ g : GL (Fin 2) (extension (ν : k)), X = rowSPi ν Ψ g * rowSKappa ν Ψ := by
  have hc : ∀ Y : GL (Fin m) k, GeneralLinearGroup.scalar (Fin m) (-1) * Y =
      Y * GeneralLinearGroup.scalar (Fin m) (-1) := fun Y =>
    GeneralLinearGroup.scalar_commute (-1) Y
  have hXK : X * rowSKappa ν Ψ * rowSU ν Ψ = rowSU ν Ψ * (X * rowSKappa ν Ψ) := by
    have hss : GeneralLinearGroup.scalar (Fin m) (-1 : kˣ) *
        GeneralLinearGroup.scalar (Fin m) (-1) = 1 := by
      rw [← map_mul, neg_one_mul, neg_neg, map_one]
    calc X * rowSKappa ν Ψ * rowSU ν Ψ = X * (rowSKappa ν Ψ * rowSU ν Ψ) := mul_assoc _ _ _
      _ = X * (GeneralLinearGroup.scalar (Fin m) (-1) * rowSU ν Ψ * rowSKappa ν Ψ) := by
          rw [rowSKappa_mul_rowSU]
      _ = (X * GeneralLinearGroup.scalar (Fin m) (-1)) * rowSU ν Ψ * rowSKappa ν Ψ := by
          group
      _ = GeneralLinearGroup.scalar (Fin m) (-1) * (X * rowSU ν Ψ) * rowSKappa ν Ψ := by
          rw [← hc X]; group
      _ = rowSU ν Ψ * (X * rowSKappa ν Ψ) := by
          rw [hX, ← mul_assoc, ← mul_assoc, hss, one_mul]; group
  obtain ⟨g, hg⟩ := exists_rowSPi_of_commute ν Ψ hXK
  refine ⟨g, ?_⟩
  rw [← hg, mul_assoc, rowSKappa_mul_self, mul_one]

end Classify

end CFSG.ComponentClassification.OddSelector
