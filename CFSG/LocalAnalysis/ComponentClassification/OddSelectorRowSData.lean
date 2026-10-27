module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticField
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic Polynomial

section Extension

variable {k : Type} [Field k] (ν : kˣ)

@[expose] def rootUnit : (extension (ν : k))ˣ where
  val := AdjoinRoot.root (quadraticPolynomial (ν : k))
  inv := algebraMap k (extension (ν : k)) ((ν⁻¹ : kˣ) : k) *
    AdjoinRoot.root (quadraticPolynomial (ν : k))
  val_inv := by
    rw [mul_left_comm, ← sq, extension_root_square, ← map_mul, Units.inv_mul, map_one]
  inv_val := by
    rw [mul_assoc, ← sq, extension_root_square, ← map_mul, Units.inv_mul, map_one]

theorem coe_rootUnit :
    ((rootUnit ν : (extension (ν : k))ˣ) : extension (ν : k)) =
      AdjoinRoot.root (quadraticPolynomial (ν : k)) := rfl

theorem aeval_neg_root :
    aeval (-AdjoinRoot.root (quadraticPolynomial (ν : k))) (quadraticPolynomial (ν : k)) = 0 := by
  have h := extension_root_square (ν : k)
  have e : aeval (-AdjoinRoot.root (quadraticPolynomial (ν : k))) (quadraticPolynomial (ν : k)) =
      (-AdjoinRoot.root (quadraticPolynomial (ν : k))) ^ 2 -
        algebraMap k (extension (ν : k)) (ν : k) := by
    change aeval (-AdjoinRoot.root (quadraticPolynomial (ν : k))) (X ^ 2 - C (ν : k)) = _
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C]
  rw [e, neg_sq]
  exact sub_eq_zero.mpr h

@[expose] def extensionConjHom : extension (ν : k) →ₐ[k] extension (ν : k) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId k _) _ (aeval_neg_root ν)

theorem extensionConjHom_root :
    extensionConjHom ν (AdjoinRoot.root (quadraticPolynomial (ν : k))) =
      -AdjoinRoot.root (quadraticPolynomial (ν : k)) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem extensionConjHom_comp :
    (extensionConjHom ν).comp (extensionConjHom ν) = AlgHom.id k (extension (ν : k)) := by
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply, extensionConjHom_root, map_neg, extensionConjHom_root, neg_neg,
    AlgHom.id_apply]

@[expose] def extensionConj : extension (ν : k) ≃ₐ[k] extension (ν : k) :=
  AlgEquiv.ofAlgHom (extensionConjHom ν) (extensionConjHom ν) (extensionConjHom_comp ν)
    (extensionConjHom_comp ν)

theorem extensionConj_root :
    extensionConj ν (AdjoinRoot.root (quadraticPolynomial (ν : k))) =
      -AdjoinRoot.root (quadraticPolynomial (ν : k)) :=
  extensionConjHom_root ν

theorem extensionConj_extensionConj (x : extension (ν : k)) :
    extensionConj ν (extensionConj ν x) = x :=
  congrArg (fun f : extension (ν : k) →ₐ[k] extension (ν : k) => f x) (extensionConjHom_comp ν)

end Extension

section Action

variable {k : Type} [Field k] {E : Type} [CommRing E] [Algebra k E]

@[expose] def glRestrict (n : ℕ) : GL (Fin n) E →* ((Fin n → E) ≃ₗ[k] (Fin n → E)) where
  toFun g :=
    { toFun := fun v => (g : Matrix (Fin n) (Fin n) E) *ᵥ v
      invFun := fun v => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v
      map_add' := fun v w => Matrix.mulVec_add _ v w
      map_smul' := fun c v => by
        rw [RingHom.id_apply, Matrix.mulVec_smul]
      left_inv := fun v => by
        simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      right_inv := fun v => by
        simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec] }
  map_one' := LinearEquiv.ext fun v => by
    change ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v = v
    rw [Units.val_one, Matrix.one_mulVec]
  map_mul' g h := LinearEquiv.ext fun v => by
    change ((g * h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v =
      (g : Matrix (Fin n) (Fin n) E) *ᵥ ((h : Matrix (Fin n) (Fin n) E) *ᵥ v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem glRestrict_apply (n : ℕ) (g : GL (Fin n) E) (v : Fin n → E) :
    glRestrict (k := k) n g v = (g : Matrix (Fin n) (Fin n) E) *ᵥ v := rfl

end Action

section Row

variable {k : Type} [Field k] {m : ℕ} (ν : kˣ)
  (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin m → k))

@[expose] def rowSPi : GL (Fin 2) (extension (ν : k)) →* GL (Fin m) k :=
  (linearConjGL Ψ.symm).comp (glRestrict 2)

theorem rowSPi_mulVec (g : GL (Fin 2) (extension (ν : k))) (v : Fin m → k) :
    ((rowSPi ν Ψ g : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ v =
      Ψ ((g : Matrix (Fin 2) (Fin 2) (extension (ν : k))) *ᵥ Ψ.symm v) := by
  rw [rowSPi, MonoidHom.comp_apply, linearConjGL_mulVec, LinearEquiv.symm_symm]
  rfl

@[expose] def rowSU : GL (Fin m) k :=
  rowSPi ν Ψ (GeneralLinearGroup.scalar (Fin 2) (rootUnit ν))

@[expose] def rowSKappa₀ :
    (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 2 → extension (ν : k)) :=
  LinearEquiv.piCongrRight fun _ => (extensionConj ν).toLinearEquiv

@[expose] def rowSKappa : GL (Fin m) k := linearConjGL Ψ.symm (rowSKappa₀ ν)

@[expose] def normFourthPowers : Subgroup (GL (Fin 2) (extension (ν : k))) :=
  ((powMonoidHom 4 : kˣ →* kˣ).range).comap
    ((Units.map (Algebra.norm k : extension (ν : k) →* k)).comp GeneralLinearGroup.det)

theorem mem_normFourthPowers (g : GL (Fin 2) (extension (ν : k))) :
    g ∈ normFourthPowers ν ↔ ∃ c : kˣ,
      Algebra.norm k (g : Matrix (Fin 2) (Fin 2) (extension (ν : k))).det = (c : k) ^ 4 := by
  change (∃ c : kˣ, c ^ 4 = Units.map (Algebra.norm k : extension (ν : k) →* k)
    (GeneralLinearGroup.det g)) ↔ _
  refine exists_congr fun c => ?_
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.coe_map]
  change _ = Algebra.norm k ((GeneralLinearGroup.det g : (extension (ν : k))ˣ) :
    extension (ν : k)) ↔ _
  rw [GeneralLinearGroup.val_det_apply, eq_comm]

@[expose] def rowST : Subgroup (MulAut (projectiveSL m k)) :=
  (normFourthPowers ν).map ((conjAut m k).comp (rowSPi ν Ψ))

@[expose] def rowSJ : Subgroup (MulAut (projectiveSL m k)) :=
  ((conjAut m k).comp ((rowSPi ν Ψ).comp SpecialLinearGroup.toGL)).range

end Row

@[expose] def SelectorRowS {A : Type} [Group A] (m : ℕ) (k : Type) [Field k]
    (ρ : A →* MulAut (projectiveSL m k)) (W : Subgroup A) (a : A) (L : Subgroup A) : Prop :=
  ∃ (ν : kˣ) (_ : ¬ IsSquare (ν : k)) (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin m → k))
    (C : GL (Fin m) k),
    Nat.card (extension (ν : k)) = Nat.card k ^ 2 ∧
    ρ a = conjAut m k C * conjAut m k (rowSU ν Ψ) * (conjAut m k C)⁻¹ ∧
    OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a} =
      (rowST ν Ψ ⊔ zpowers (conjAut m k (rowSKappa ν Ψ))).map
        (MulAut.conj (conjAut m k C)).toMonoidHom ∧
    rowST ν Ψ ⊓ zpowers (conjAut m k (rowSKappa ν Ψ)) = ⊥ ∧
    conjAut m k (rowSKappa ν Ψ) ∈
      normalizer (rowST ν Ψ : Set (MulAut (projectiveSL m k))) ∧
    orderOf (conjAut m k (rowSKappa ν Ψ)) = 2 ∧
    (∀ g ∈ normFourthPowers ν, conjAut m k (rowSPi ν Ψ g) = 1 ↔
      ∃ c : kˣ, g = GeneralLinearGroup.scalar (Fin 2)
        (Units.map (algebraMap k (extension (ν : k))).toMonoidHom c)) ∧
    (∀ X : Subgroup (MulAut (projectiveSL m k)),
      CFSG.Assembly.IsComponentOf X
          (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}) ↔
        X = (rowSJ ν Ψ).map (MulAut.conj (conjAut m k C)).toMonoidHom) ∧
    L.map ρ = (rowSJ ν Ψ).map (MulAut.conj (conjAut m k C)).toMonoidHom ∧
    (∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)),
      conjAut m k (rowSPi ν Ψ (SpecialLinearGroup.toGL g)) = 1 ↔ g = 1 ∨ g = -1) ∧
    centralizer {ρ a} =
      (centralizer {conjAut m k (rowSU ν Ψ)}).map (MulAut.conj (conjAut m k C)).toMonoidHom ∧
    (centralizer {conjAut m k (rowSU ν Ψ)} : Set (MulAut (projectiveSL m k))) =
      {β | ∃ (B : GL (Fin m) k) (τ : k ≃+* k) (ε : ℕ), ε ≤ 1 ∧
        (∃ c : kˣ, B * ((GeneralLinearGroup.inverseTranspose : MulAut (GL (Fin m) k)) ^ ε)
            (GeneralLinearGroup.map (τ : k →+* k) (rowSU ν Ψ)) * B⁻¹ =
          GeneralLinearGroup.scalar (Fin m) c * rowSU ν Ψ) ∧
        β = conjAut m k B * fieldAut m k τ * dualAut m k ^ ε} ∧
    (centralizer {a}).map ρ = ρ.range ⊓
      (centralizer {conjAut m k (rowSU ν Ψ)}).map (MulAut.conj (conjAut m k C)).toMonoidHom ∧
    (W ⊓ centralizer {a}).map ρ = OuterAutomorphisms.inner (projectiveSL m k) ⊓
      (centralizer {conjAut m k (rowSU ν Ψ)}).map (MulAut.conj (conjAut m k C)).toMonoidHom

end CFSG.ComponentClassification.OddSelector
