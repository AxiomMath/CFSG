module
public import Mathlib.RepresentationTheory.Semisimple
public import CFSG.FeitThompson.Representations.AveragedPositiveHermitianForm

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Representation

noncomputable section

variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]

def pushSubrepresentation {ρ : Representation k G W} (σ : Subrepresentation ρ)
    (τ : Subrepresentation σ.toRepresentation) : Subrepresentation ρ where
  toSubmodule := τ.toSubmodule.map σ.toSubmodule.subtype
  apply_mem_toSubmodule := by
    rintro g v ⟨w, hw, rfl⟩
    exact ⟨σ.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩

def pullSubrepresentation {ρ : Representation k G W} (σ μ : Subrepresentation ρ) :
    Subrepresentation σ.toRepresentation where
  toSubmodule := μ.toSubmodule.comap σ.toSubmodule.subtype
  apply_mem_toSubmodule := fun g _ hw => μ.apply_mem_toSubmodule g hw

@[simp]
theorem toSubmodule_pushSubrepresentation {ρ : Representation k G W} (σ : Subrepresentation ρ)
    (τ : Subrepresentation σ.toRepresentation) :
    (pushSubrepresentation σ τ).toSubmodule = τ.toSubmodule.map σ.toSubmodule.subtype := (rfl)

@[simp]
theorem toSubmodule_pullSubrepresentation {ρ : Representation k G W}
    (σ μ : Subrepresentation ρ) :
    (pullSubrepresentation σ μ).toSubmodule = μ.toSubmodule.comap σ.toSubmodule.subtype := (rfl)

theorem pushSubrepresentation_le {ρ : Representation k G W} (σ : Subrepresentation ρ)
    (τ : Subrepresentation σ.toRepresentation) : pushSubrepresentation σ τ ≤ σ :=
  show (pushSubrepresentation σ τ).toSubmodule ≤ σ.toSubmodule from
    (toSubmodule_pushSubrepresentation σ τ) ▸ Submodule.map_subtype_le _ _

def subrepresentationIicOrderIso {ρ : Representation k G W} (σ : Subrepresentation ρ) :
    Subrepresentation σ.toRepresentation ≃o Set.Iic σ where
  toFun τ := ⟨pushSubrepresentation σ τ, pushSubrepresentation_le σ τ⟩
  invFun μ := pullSubrepresentation σ μ.1
  left_inv τ := Subrepresentation.toSubmodule_injective <| by
    simp only [toSubmodule_pullSubrepresentation, toSubmodule_pushSubrepresentation]
    exact Submodule.comap_map_eq_self (by simp)
  right_inv μ := Subtype.ext <| Subrepresentation.toSubmodule_injective <| by
    simp only [toSubmodule_pushSubrepresentation, toSubmodule_pullSubrepresentation]
    exact Submodule.map_comap_eq_self (by
      simpa [Submodule.range_subtype] using (show (μ.1).toSubmodule ≤ σ.toSubmodule from μ.2))
  map_rel_iff' {τ₁ τ₂} :=
    show pushSubrepresentation σ τ₁ ≤ pushSubrepresentation σ τ₂ ↔ τ₁ ≤ τ₂ from
      Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype _) _ _

theorem isAtom_iff_isIrreducible {ρ : Representation k G W} (σ : Subrepresentation ρ) :
    IsAtom σ ↔ σ.toRepresentation.IsIrreducible := by
  rw [← Set.isSimpleOrder_Iic_iff_isAtom, ← (subrepresentationIicOrderIso σ).isSimpleOrder_iff]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem exists_invariant_isCompl_complex [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (W : Submodule ℂ V) (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) :
    ∃ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) ∧ IsCompl W U := by
  obtain ⟨c, hc⟩ := exists_invariant_innerProductSpaceCore ρ
  let _ : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ c
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore (𝕜 := ℂ) (F := V) (instCoreOfCore ℂ V)
  have hinner : ∀ (g : G) (x y : V), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y := hc
  refine ⟨Wᗮ, ?_, W.isCompl_orthogonal⟩
  intro g v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  calc inner ℂ u (ρ g v) = inner ℂ (ρ g (ρ g⁻¹ u)) (ρ g v) := by simp
    _ = inner ℂ (ρ g⁻¹ u) v := hinner g _ _
    _ = 0 := hv _ (hW g⁻¹ u hu)

theorem isSemisimpleRepresentation_complex [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : ρ.IsSemisimpleRepresentation := by
  refine ⟨fun σ => ?_⟩
  obtain ⟨U, hU, hcompl⟩ := exists_invariant_isCompl_complex ρ σ.toSubmodule
    (fun g v hv => σ.apply_mem_toSubmodule g hv)
  refine ⟨⟨U, fun g v hv => hU g v hv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective <|
      (Subrepresentation.toSubmodule_inf _ _).trans hcompl.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective <|
      (Subrepresentation.toSubmodule_sup _ _).trans hcompl.sup_eq_top

theorem exists_directSum_isInternal_isIrreducible [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ (n : ℕ) (σ : Fin n → Subrepresentation ρ),
      DirectSum.IsInternal (fun i => (σ i).toSubmodule) ∧
        ∀ i, (σ i).toRepresentation.IsIrreducible := by
  have _ : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ _ _
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1
      (isSemisimpleRepresentation_complex ρ)
  have hatoms : sSup {a : Submodule (MonoidAlgebra ℂ G) ρ.asModule | IsAtom a} = ⊤ := by
    simpa [isSimpleModule_iff_isAtom.symm] using
      @IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G) _ ρ.asModule _ _ hss
  obtain ⟨s, hind, hsup, hat⟩ := exists_sSupIndep_of_sSup_atoms_eq_top hatoms
  have h1 : iSupIndep ((↑) : s → Submodule (MonoidAlgebra ℂ G) ρ.asModule) :=
    (sSupIndep_iff s).1 hind
  have hfin : Finite s := by
    have h2 := Submodule.finite_ne_bot_of_iSupIndep h1
    have heq : {i : s | (i : Submodule (MonoidAlgebra ℂ G) ρ.asModule) ≠ ⊥} = Set.univ := by
      ext i; simp [(hat i.2).1]
    rw [heq] at h2
    exact Set.finite_univ_iff.1 h2
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  have hInternal : DirectSum.IsInternal
      fun i : Fin n => (e.symm i : Submodule (MonoidAlgebra ℂ G) ρ.asModule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (h1.comp e.symm.injective) <| by
      rw [← hsup, sSup_eq_iSup']
      exact e.symm.iSup_comp (g := fun i : s => (i : Submodule (MonoidAlgebra ℂ G) ρ.asModule))
  refine ⟨n, fun i => Subrepresentation.ofSubmodule' (e.symm i), hInternal, fun i => ?_⟩
  rw [← isAtom_iff_isIrreducible]
  have h3 := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).isAtom_iff
    (Subrepresentation.ofSubmodule' (e.symm i : Submodule (MonoidAlgebra ℂ G) ρ.asModule))
  rw [Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
    show (Subrepresentation.ofSubmodule'
        (e.symm i : Submodule (MonoidAlgebra ℂ G) ρ.asModule)).asSubmodule
      = (e.symm i : Submodule (MonoidAlgebra ℂ G) ρ.asModule) from
      Submodule.toSubMulAction_inj.mp rfl] at h3
  exact h3.1 (hat (e.symm i).2)

end

end CFSG.FeitThompson
