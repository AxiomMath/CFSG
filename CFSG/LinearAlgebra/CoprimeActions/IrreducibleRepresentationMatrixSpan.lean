module


public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.LinearAlgebra.CoprimeActions.IrreducibleRepresentationMatrixSpan

open scoped MonoidAlgebra

theorem span_eq_top {F : Type*} [Field F] [IsAlgClosed F]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    {E : Type*} [Group E] (σ : Representation F E W) (hσ : σ.IsIrreducible) :
    Submodule.span F (Set.range σ) = ⊤ := by
  classical
  haveI : IsSimpleModule F[E] σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).1 hσ
  haveI : IsScalarTower F F[E] σ.asModule :=
    ⟨fun c a m => by
      show σ.asAlgebraHom (c • a) m = c • σ.asAlgebraHom a m
      rw [map_smul]; rfl⟩
  have hS := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := F[E])
    (V := σ.asModule) F
  haveI : Module.Finite (Module.End F[E] σ.asModule) σ.asModule :=
    Module.Finite.of_restrictScalars_finite F _ _
  have hsurj := Module.Finite.toModuleEnd_moduleEnd_surjective (R := F[E]) (M := σ.asModule)
  rw [eq_top_iff]
  intro T _
  let f : Module.End (Module.End F[E] σ.asModule) σ.asModule :=
    { toFun := fun m => T m
      map_add' := fun x y => T.map_add x y
      map_smul' := by
        intro e m
        obtain ⟨c, rfl⟩ := hS.2 e
        show T ((algebraMap F (Module.End F[E] σ.asModule) c) m) =
          (algebraMap F (Module.End F[E] σ.asModule) c) (T m)
        have h1 : ∀ x : σ.asModule, (algebraMap F (Module.End F[E] σ.asModule) c) x = c • x :=
          fun x => rfl
        rw [h1]
        exact T.map_smul c m }
  obtain ⟨r, hr⟩ := hsurj f
  have hT : T = σ.asAlgebraHom r := by
    ext m
    exact (congrArg (fun g => g m) hr).symm
  have key : ∀ r : F[E], σ.asAlgebraHom r ∈ Submodule.span F (Set.range σ) := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      rw [Representation.asAlgebraHom_of]
      exact Submodule.subset_span ⟨g, rfl⟩
    | add a b ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | smul c a ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ ha
  rw [hT]
  exact key r

end CFSG.LinearAlgebra.CoprimeActions.IrreducibleRepresentationMatrixSpan
