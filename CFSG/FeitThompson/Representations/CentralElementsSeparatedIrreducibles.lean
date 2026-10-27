module

public import CFSG.FeitThompson.Representations.CentralCharacterHomomorphism
public import Mathlib.Analysis.Complex.Polynomial.Basic
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.ComplexCompleteReducibility
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

noncomputable section

variable {G : Type*} [Group G]

section AlgebraHom

variable {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem coe_asAlgebraHom_toRepresentation {ρ : Representation k G V} (μ : Subrepresentation ρ)
    (x : MonoidAlgebra k G) (v : μ.toSubmodule) :
    (μ.toRepresentation.asAlgebraHom x v : V) = ρ.asAlgebraHom x (v : V) := by
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]; rfl
  | add x y hx hy => simp [hx, hy]
  | smul r x hx => simp [hx]

theorem equiv_asAlgebraHom {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (x : MonoidAlgebra k G) (v : V) :
    e.toLinearEquiv (ρ.asAlgebraHom x v) = σ.asAlgebraHom x (e.toLinearEquiv v) := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simp [Representation.equiv_apply_apply]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, map_add]
    rw [hx, hy]
  | smul r x hx =>
    simp only [map_smul, LinearMap.smul_apply, map_smul]
    rw [hx]

theorem centralCharacter_eq_of_equiv [IsAlgClosed k] [FiniteDimensional k V]
    [FiniteDimensional k W] {ρ : Representation k G V} {σ : Representation k G W}
    [ρ.IsIrreducible] [σ.IsIrreducible] (e : ρ.Equiv σ) :
    Representation.centralCharacter ρ = Representation.centralCharacter σ := by
  have hV : Nontrivial V := nontrivial_of_isIrreducible ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine AlgHom.ext fun z => ?_
  have h1 : σ.asAlgebraHom (z : MonoidAlgebra k G) (e.toLinearEquiv v)
      = Representation.centralCharacter ρ z • e.toLinearEquiv v := by
    rw [← equiv_asAlgebraHom e, Representation.asAlgebraHom_center_apply, map_smul]
  have h2 := Representation.asAlgebraHom_center_apply σ z (e.toLinearEquiv v)
  rw [h1] at h2
  have hne : e.toLinearEquiv v ≠ 0 := by
    simpa using (e.toLinearEquiv.map_ne_zero_iff).2 hv
  have h3 := sub_eq_zero.2 h2
  rw [← sub_smul] at h3
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hne)

end AlgebraHom

section Conj

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def conjRepresentation (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W :=
  ((e.conjAlgEquiv ℂ : Module.End ℂ V ≃ₐ[ℂ] Module.End ℂ W) :
    Module.End ℂ V →* Module.End ℂ W).comp ρ

def conjRepresentationEquiv (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) :
    ρ.Equiv (conjRepresentation ρ e) :=
  Representation.Equiv.mk e fun g => by
    ext v
    simp [conjRepresentation, LinearEquiv.conjAlgEquiv_apply_apply]

theorem character_conjRepresentation [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (e : V ≃ₗ[ℂ] W) : (conjRepresentation ρ e).character = ρ.character :=
  (Representation.char_iso (conjRepresentationEquiv ρ e)).symm

theorem character_mem_irrChar_of_isIrreducible [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : ρ.character ∈ irrChar ℂ G := by
  classical
  set e : V ≃ₗ[ℂ] (Fin (finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  have hirr := Representation.isIrreducible_of_equiv (conjRepresentationEquiv ρ e) h
  have hmem := character_mem_irrChar (conjRepresentation ρ e) hirr
  rwa [character_conjRepresentation] at hmem

end Conj

def irrRep {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) : FDRep ℂ G := (mem_irrChar.1 hχ).choose

instance irrRep_isIrreducible {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) :
    Representation.IsIrreducible (irrRep hχ).ρ := (mem_irrChar.1 hχ).choose_spec.1

@[simp]
theorem character_irrRep {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) :
    Representation.character (irrRep hχ).ρ = χ := (mem_irrChar.1 hχ).choose_spec.2

def centralScalar {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] ℂ :=
  Representation.centralCharacter (irrRep hχ).ρ

@[simp]
theorem centralScalar_one {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) : centralScalar hχ 1 = 1 := map_one _

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem centralCharacter_eq_centralScalar [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G)
    (h : ρ.character = χ) : Representation.centralCharacter ρ = centralScalar hχ := by
  obtain ⟨e⟩ := (nonempty_equiv_iff_character_eq ρ (irrRep hχ).ρ).2 (by rw [h, character_irrRep])
  exact centralCharacter_eq_of_equiv e

theorem asAlgebraHom_center_apply_eq_centralScalar_smul [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G)
    (h : ρ.character = χ) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (v : V) :
    ρ.asAlgebraHom (z : MonoidAlgebra ℂ G) v = centralScalar hχ z • v := by
  rw [Representation.asAlgebraHom_center_apply, centralCharacter_eq_centralScalar ρ hχ h]

def centralScalarPi (G : Type*) [Group G] :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₗ[ℂ] (irrChar ℂ G → ℂ) :=
  LinearMap.pi fun χ => (centralScalar χ.2).toLinearMap

@[simp]
theorem centralScalarPi_apply (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (χ : irrChar ℂ G) : centralScalarPi G z χ = centralScalar χ.2 z := (rfl)

theorem injective_centralScalarPi [Finite G] : Function.Injective (centralScalarPi G) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have hz' : ∀ χ : irrChar ℂ G, centralScalar χ.2 z = 0 := fun χ => by
    rw [← centralScalarPi_apply z χ, hz]; rfl
  set ρ := Representation.leftRegular ℂ G with hρ
  obtain ⟨n, σ, hInt, hirr⟩ := exists_directSum_isInternal_isIrreducible ρ
  have hker : ∀ i, (σ i).toSubmodule ≤ LinearMap.ker (ρ.asAlgebraHom (z : MonoidAlgebra ℂ G)) := by
    intro i v hv
    have hirri := hirr i
    have hχ := character_mem_irrChar_of_isIrreducible (σ i).toRepresentation (hirr i)
    have h1 := asAlgebraHom_center_apply_eq_centralScalar_smul (σ i).toRepresentation hχ rfl z
      ⟨v, hv⟩
    rw [hz' ⟨_, hχ⟩] at h1
    have h2 := coe_asAlgebraHom_toRepresentation (σ i) (z : MonoidAlgebra ℂ G) ⟨v, hv⟩
    rw [h1] at h2
    simp only [zero_smul, ZeroMemClass.coe_zero] at h2
    exact LinearMap.mem_ker.2 h2.symm
  have htop : LinearMap.ker (ρ.asAlgebraHom (z : MonoidAlgebra ℂ G)) = ⊤ :=
    top_le_iff.1 (hInt.submodule_iSup_eq_top ▸ iSup_le hker)
  have h0 : ρ.asAlgebraHom (z : MonoidAlgebra ℂ G) = 0 := LinearMap.ker_eq_top.1 htop
  have h1 := congrArg (fun f => f (1 : MonoidAlgebra ℂ G)) h0
  simp only [LinearMap.zero_apply, hρ] at h1
  rw [show Representation.leftRegular ℂ G = Representation.ofMulAction ℂ G G from rfl,
    Representation.asAlgebraHom_ofMulAction_smul_eq_mul, mul_one] at h1
  exact Subtype.ext h1

end

end CFSG.FeitThompson
