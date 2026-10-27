module

public import CFSG.FeitThompson.Representations.ClassSumsIntegerStructureConstants
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.CentralElementsSeparatedIrreducibles
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

noncomputable section

variable {G : Type*} [Group G]

instance finiteDimensional_classFun [Finite G] : FiniteDimensional ℂ (classFun G) := by
  have : Fintype G := Fintype.ofFinite G
  exact FiniteDimensional.finiteDimensional_submodule _

instance finite_coe_Irr [Finite G] : Finite (Irr G) := finite_Irr.to_subtype

def classFun.equivConjClasses (G : Type*) [Group G] :
    classFun G ≃ₗ[ℂ] (ConjClasses G → ℂ) where
  toFun f K := (f : G → ℂ) (classRep K)
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun c := ⟨fun g => c (ConjClasses.mk g), mem_classFun.2 fun _ _ h => by
    rw [ConjClasses.mk_eq_mk_iff_isConj.2 h]⟩
  left_inv f := Subtype.ext (funext fun g =>
    classFun.apply_eq_of_isConj f.2 (isConj_classRep_mk g))
  right_inv c := funext fun K => by simp

@[simp]
theorem classFun.equivConjClasses_apply (f : classFun G) (K : ConjClasses G) :
    classFun.equivConjClasses G f K = (f : G → ℂ) (classRep K) := (rfl)

@[simp]
theorem classFun.coe_equivConjClasses_symm_apply (c : ConjClasses G → ℂ) (g : G) :
    (((classFun.equivConjClasses G).symm c : classFun G) : G → ℂ) g = c (ConjClasses.mk g) :=
  (rfl)

theorem finrank_classFun (G : Type*) [Group G] [Finite G] :
    finrank ℂ (classFun G) = Nat.card (ConjClasses G) := by
  have := Fintype.ofFinite (ConjClasses G)
  rw [(classFun.equivConjClasses G).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

def Irr.toClassFun (χ : Irr G) : classFun G := ⟨(χ : G → ℂ), Irr_subset_classFun χ.2⟩

@[simp]
theorem Irr.coe_toClassFun (χ : Irr G) : (Irr.toClassFun χ : G → ℂ) = (χ : G → ℂ) := (rfl)

theorem linearIndependent_Irr [Finite G] :
    LinearIndependent ℂ (fun χ : Irr G => (χ : G → ℂ)) := by
  rw [Irr_eq_irrChar]
  exact linearIndependent_irrChar

theorem linearIndependent_Irr_toClassFun [Finite G] :
    LinearIndependent ℂ (Irr.toClassFun (G := G)) :=
  LinearIndependent.of_comp (classFun G).subtype linearIndependent_Irr

theorem card_conjClasses_le_card_Irr [Finite G] :
    Nat.card (ConjClasses G) ≤ Nat.card (Irr G) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (irrChar ℂ G) := finite_irrChar.fintype
  have h1 : finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) = Nat.card (ConjClasses G) :=
    Module.finrank_eq_nat_card_basis (classSumBasis ℂ)
  have h2 : finrank ℂ (irrChar ℂ G → ℂ) = Nat.card (irrChar ℂ G) := by
    rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  have h3 := LinearMap.finrank_le_finrank_of_injective (f := centralScalarPi G)
    injective_centralScalarPi
  rw [h1, h2] at h3
  rwa [Irr_eq_irrChar]

theorem card_Irr_eq_card_conjClasses [Finite G] :
    Nat.card (Irr G) = Nat.card (ConjClasses G) := by
  have : Fintype (Irr G) := Fintype.ofFinite _
  refine le_antisymm ?_ card_conjClasses_le_card_Irr
  have h := (linearIndependent_Irr_toClassFun (G := G)).fintype_card_le_finrank
  rw [finrank_classFun] at h
  rwa [Nat.card_eq_fintype_card]

theorem card_Irr_eq_finrank_classFun [Finite G] :
    Nat.card (Irr G) = finrank ℂ (classFun G) := by
  rw [card_Irr_eq_card_conjClasses, finrank_classFun]

theorem span_range_Irr_toClassFun [Finite G] :
    Submodule.span ℂ (Set.range (Irr.toClassFun (G := G))) = ⊤ := by
  have : Fintype (Irr G) := Fintype.ofFinite _
  refine linearIndependent_Irr_toClassFun.span_eq_top_of_card_eq_finrank' ?_
  rw [← Nat.card_eq_fintype_card, card_Irr_eq_finrank_classFun]

def classFun.basisIrr (G : Type*) [Group G] [Finite G] :
    Module.Basis (Irr G) ℂ (classFun G) :=
  Module.Basis.mk linearIndependent_Irr_toClassFun span_range_Irr_toClassFun.ge

@[simp]
theorem classFun.basisIrr_apply [Finite G] (χ : Irr G) :
    classFun.basisIrr G χ = Irr.toClassFun χ := by
  rw [classFun.basisIrr, Module.Basis.mk_apply]

theorem cfInner_coe_Irr [Fintype G] (χ ψ : Irr G) :
    cfInner ((χ : Irr G) : G → ℂ) ((ψ : Irr G) : G → ℂ) = if χ = ψ then 1 else 0 := by
  classical
  rw [cfInner_eq_ite_of_mem_Irr χ.2 ψ.2]
  simp [Subtype.ext_iff]

theorem cfInner_basisIrr [Fintype G] (χ ψ : Irr G) :
    cfInner (classFun.basisIrr G χ : G → ℂ) (classFun.basisIrr G ψ : G → ℂ) =
      if χ = ψ then 1 else 0 := by
  rw [classFun.basisIrr_apply, classFun.basisIrr_apply, Irr.coe_toClassFun, Irr.coe_toClassFun,
    cfInner_coe_Irr]

theorem classFun.coe_eq_sum_repr [Finite G] [Fintype (Irr G)] (f : classFun G) :
    (f : G → ℂ) = ∑ χ : Irr G, (classFun.basisIrr G).repr f χ • ((χ : Irr G) : G → ℂ) := by
  have h := congrArg (fun x : classFun G => (x : G → ℂ)) ((classFun.basisIrr G).sum_repr f)
  simpa [Submodule.coe_sum] using h.symm

theorem classFun.basisIrr_repr_apply [Fintype G] (f : classFun G) (χ : Irr G) :
    (classFun.basisIrr G).repr f χ = cfInner (f : G → ℂ) (χ : G → ℂ) := by
  have : Fintype (Irr G) := Fintype.ofFinite _
  rw [classFun.coe_eq_sum_repr f, cfInner_sum_left]
  simp only [cfInner_smul_left, cfInner_coe_Irr, mul_ite, mul_one, mul_zero]
  simp

theorem classFun.coe_eq_sum_cfInner_smul [Fintype G] [Fintype (Irr G)] (f : classFun G) :
    (f : G → ℂ) = ∑ χ : Irr G, cfInner (f : G → ℂ) (χ : G → ℂ) • ((χ : Irr G) : G → ℂ) :=
  (classFun.coe_eq_sum_repr f).trans <|
    Finset.sum_congr rfl fun χ _ => by rw [classFun.basisIrr_repr_apply]

end

end CFSG.FeitThompson
