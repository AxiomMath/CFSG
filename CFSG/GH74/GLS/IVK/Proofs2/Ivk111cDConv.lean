module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped MonoidAlgebra

section Conv

variable {F G X : Type} [Field F] [Group G] [AddCommGroup X] [Module F X]
  {ρ : Representation F G X}

theorem toRep_asAlgebraHom (σ : Subrepresentation ρ) (r : F[G]) (y : ↥σ.toSubmodule) :
    ((σ.toRepresentation.asAlgebraHom r y : ↥σ.toSubmodule) : X) = ρ.asAlgebraHom r (y : X) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | single g a =>
    simp only [Representation.asAlgebraHom_single]
    rfl

@[expose] noncomputable def submoduleEquivRep (N : Submodule F[G] ρ.asModule) :
    ↥N ≃ₗ[F[G]] (Subrepresentation.ofSubmodule' N).toRepresentation.asModule where
  toFun x := (Subrepresentation.ofSubmodule' N).toRepresentation.asModuleEquiv.symm
    ⟨ρ.asModuleEquiv (x : ρ.asModule), x.2⟩
  map_add' x y := rfl
  map_smul' r x := by
    apply (Subrepresentation.ofSubmodule' N).toRepresentation.asModuleEquiv.injective
    apply Subtype.ext
    rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply, toRep_asAlgebraHom, ← Representation.asModuleEquiv_map_smul]
    rfl
  invFun y := ⟨ρ.asModuleEquiv.symm
    ((Subrepresentation.ofSubmodule' N).toRepresentation.asModuleEquiv y : X), 
    ((Subrepresentation.ofSubmodule' N).toRepresentation.asModuleEquiv y).2⟩
  left_inv x := rfl
  right_inv y := rfl

end Conv

end CFSG.GH74.GLS.Stage4.Rest
