module

public import CFSG.HardMathSupport.Lang.E6Descent.RankB3Eichler
public import CFSG.Open.StatedDefs
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.HardMathSupport.Lang.E6Descent.RankB3

open Module Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.Open
  CFSG.Blueprint.EvenSource

open scoped commutatorElement

variable {F : Type} [Field F]

noncomputable def toGL (u : (V3 F →ₗ[F] V3 F)ˣ) : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) F :=
  Matrix.GeneralLinearGroup.toLin.symm u

theorem toLin_val_apply (A : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) F) (v : V3 F) :
    ((Matrix.GeneralLinearGroup.toLin A : (V3 F →ₗ[F] V3 F)ˣ) : V3 F →ₗ[F] V3 F) v =
      (A : Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) (Fin 3 ⊕ Fin 3 ⊕ Unit) F) *ᵥ v := by
  simp [Matrix.GeneralLinearGroup.toLin]

theorem toGL_mulVec (u : (V3 F →ₗ[F] V3 F)ˣ) (v : V3 F) :
    ((toGL u : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) F) : Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) _ F) *ᵥ v =
      (u : V3 F →ₗ[F] V3 F) v := by
  rw [← toLin_val_apply, toGL, MulEquiv.apply_symm_apply]

@[expose] noncomputable def eichHom (F : Type) [Field F] :
    Multiplicative (WS F) →* Module.End F (V3 F) where
  toFun x := eich (Multiplicative.toAdd x : WS F).1
  map_one' := LinearMap.ext fun v => by
    simp only [toAdd_one, ZeroMemClass.coe_zero, eich_zero]
    rfl
  map_mul' x y := LinearMap.ext fun v => by
    simp only [toAdd_mul, AddMemClass.coe_add]
    exact (eich_mul (mem_WS.1 (Multiplicative.toAdd x).2).1
      (mem_WS.1 (Multiplicative.toAdd y).2).1 v).symm

theorem eichHom_apply (x : Multiplicative (WS F)) (v : V3 F) :
    eichHom F x v = eich (Multiplicative.toAdd x : WS F).1 v := rfl

noncomputable def psi (F : Type) [Field F] :
    Multiplicative (WS F) →* GL (Fin 3 ⊕ Fin 3 ⊕ Unit) F :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin 3 ⊕ Fin 3 ⊕ Unit) (R := F)).symm.toMonoidHom.comp
    (eichHom F).toHomUnits

theorem psi_mulVec (x : Multiplicative (WS F)) (v : V3 F) :
    ((psi F x : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) F) : Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) _ F) *ᵥ v =
      eich (Multiplicative.toAdd x : WS F).1 v :=
  (toGL_mulVec ((eichHom F).toHomUnits x) v).trans (by simp [eichHom_apply])

theorem toAdd_cube (h3 : (3 : F) = 0) (x : Multiplicative (WS F)) : x * x * x = 1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  have h : ((Multiplicative.toAdd x : WS F) : V3 F) + ↑(Multiplicative.toAdd x) +
      ↑(Multiplicative.toAdd x) = (3 : F) • ((Multiplicative.toAdd x : WS F) : V3 F) := by
    module
  simp only [toAdd_mul, toAdd_one, AddMemClass.coe_add, ZeroMemClass.coe_zero]
  rw [h, h3, zero_smul]

theorem coe_Q3 (F : Type) [Field F] : ⇑(Q3 F) = StatedQuadOdd 3 F :=
  funext fun v => quadOdd_apply 3 F v

theorem psi_mem_orth (x : Multiplicative (WS F)) :
    psi F x ∈ matrixOrthogonal (StatedQuadOdd 3 F) := by
  intro v
  rw [psi_mulVec, ← coe_Q3]
  exact Q_eich (mem_WS.1 (Multiplicative.toAdd x).2).1 v

noncomputable def hUnit (F : Type) [Field F] : (V3 F →ₗ[F] V3 F)ˣ :=
  ⟨hV F, hV F, LinearMap.ext fun v => hV_hV v, LinearMap.ext fun v => hV_hV v⟩

noncomputable def hGL (F : Type) [Field F] : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) F := toGL (hUnit F)

theorem hGL_mem_orth : hGL F ∈ matrixOrthogonal (StatedQuadOdd 3 F) := by
  intro v
  rw [hGL, toGL_mulVec, ← coe_Q3]
  exact Q_hV v

theorem psi_conj (x : Multiplicative (WS F)) : hGL F * psi F x * (hGL F)⁻¹ = psi F x⁻¹ := by
  apply Matrix.GeneralLinearGroup.toLin.injective
  have e1 : Matrix.GeneralLinearGroup.toLin (psi F x) = (eichHom F).toHomUnits x := by
    simp [psi]
  have e2 : Matrix.GeneralLinearGroup.toLin (psi F x⁻¹) = (eichHom F).toHomUnits x⁻¹ := by
    simp [psi]
  have e3 : Matrix.GeneralLinearGroup.toLin (hGL F) = hUnit F := by
    simp [hGL, toGL]
  rw [map_mul, map_mul, map_inv, e1, e2, e3]
  apply Units.ext
  apply LinearMap.ext
  intro v
  have hinv : (((hUnit F)⁻¹ : (V3 F →ₗ[F] V3 F)ˣ) : V3 F →ₗ[F] V3 F) = hV F := rfl
  simp only [Units.val_mul, Module.End.mul_apply, hinv, MonoidHom.coe_toHomUnits, eichHom_apply,
    toAdd_inv]
  have h := hV_eich (mem_WS.2 (mem_WS.1 (Multiplicative.toAdd x).2)) (hV F v)
  rw [hV_hV] at h
  exact h

theorem statedOmega_eq_commutator' (Q₀ : (Fin 3 ⊕ Fin 3 ⊕ Unit → F) → F) :
    StatedOmega Q₀ = ⁅matrixOrthogonal Q₀, matrixOrthogonal Q₀⁆ := by
  have h : Subgroup.closure {A : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) F |
      ∀ v, Q₀ ((A : Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) (Fin 3 ⊕ Fin 3 ⊕ Unit) F) *ᵥ v) = Q₀ v} =
      matrixOrthogonal Q₀ :=
    Subgroup.closure_eq (matrixOrthogonal Q₀)
  rw [StatedOmega, h]

theorem psi_mem_omega (h3 : (3 : F) = 0) (x : Multiplicative (WS F)) :
    psi F x ∈ StatedOmega (StatedQuadOdd 3 F) := by
  rw [statedOmega_eq_commutator']
  have hc : ⁅hGL F, psi F x⁆ = psi F x := by
    rw [commutatorElement_def, psi_conj, ← map_inv, ← map_mul]
    congr 1
    rw [← _root_.mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right (toAdd_cube h3 x)
  rw [← hc]
  exact Subgroup.commutator_mem_commutator hGL_mem_orth (psi_mem_orth x)

theorem psi_scalar {x : Multiplicative (WS F)}
    (hx : psi F x ∈ StatedScalars (Fin 3 ⊕ Fin 3 ⊕ Unit) F) : x = 1 := by
  obtain ⟨c, hc⟩ := hx
  have hw' := mem_WS.1 (Multiplicative.toAdd x).2
  have key : ∀ v : V3 F, eich ((Multiplicative.toAdd x : WS F) : V3 F) v = (c : F) • v := by
    intro v
    rw [← psi_mulVec x v, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    funext i
    simp [Matrix.mulVec_diagonal]
  have hc1 : (c : F) = 1 := by
    have h1 := congrFun (key eV) (.inl 0)
    rw [eich_apply, polar_eV_left, hw'.1] at h1
    simpa [eV_e, eV_f] using h1.symm
  have h2 := key fV
  rw [eich_apply, hc1, one_smul, fV_f, one_smul] at h2
  have hw0 : ((Multiplicative.toAdd x : WS F) : V3 F) = 0 := by
    funext i
    have h2i := congrFun h2 i
    by_cases hi : i = .inl 0
    · subst hi; simpa using hw'.2
    · by_cases hj : i = .inr (.inl 0)
      · subst hj; simpa using hw'.1
      · simpa [fV_of_ne hj, eV_of_ne hi] using h2i
  apply Multiplicative.toAdd.injective
  exact Subtype.ext (by simpa using hw0)

theorem finrank_WS : finrank F (WS F) = 5 := by
  let g : V3 F →ₗ[F] F × F :=
    LinearMap.prod (LinearMap.proj (.inr (.inl 0))) (LinearMap.proj (.inl 0))
  have hker : LinearMap.ker g = WS F := by
    ext w
    simp [g, LinearMap.mem_ker, mem_WS]
  have hrange : LinearMap.range g = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro p
    refine ⟨p.1 • fV + p.2 • eV, ?_⟩
    simp [g, fV_f, eV_f, eV_e, fV_of_ne]
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [hker, hrange, finrank_top, Module.finrank_prod, Module.finrank_self] at h
  have h7 : finrank F (V3 F) = 7 := by
    simp [Module.finrank_fintype_fun_eq_card]
  omega

theorem card_WS (hF : Nat.card F = 3) : Nat.card (WS F) = 3 ^ 5 := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  have := Fintype.ofFinite (WS F)
  have h := Module.card_eq_pow_finrank (K := F) (V := WS F)
  rw [Nat.card_eq_fintype_card, h, finrank_WS, ← Nat.card_eq_fintype_card, hF]

end CFSG.HardMathSupport.Lang.E6Descent.RankB3
