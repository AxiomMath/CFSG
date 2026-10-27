module


public import Mathlib.RepresentationTheory.Irreducible

public section

open scoped MonoidAlgebra

namespace CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreducibleFiniteCenterCyclic

open Representation

theorem cyclic_center {F G V : Type*} [Field F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hfaith : Function.Injective ρ) (hirr : ρ.IsIrreducible) :
    IsCyclic (Subgroup.center G) := by
  classical
  haveI : IsSimpleModule F[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  let E := Module.End F[G] ρ.asModule
  let c : Subgroup.center G → E := fun g =>
    (IntertwiningMap.equivAlgEnd (A := F) (ρ := ρ)) (IntertwiningMap.centralMul ρ g.1
      (Submonoid.mem_center_iff.mpr fun h => (Subgroup.mem_center_iff.mp g.2 h)))
  have hs : ∀ (g : G) (m : ρ.asModule), MonoidAlgebra.of F G g • m = ρ g m := by
    intro g m
    show ρ.asAlgebraHom (MonoidAlgebra.of F G g) m = _
    rw [Representation.asAlgebraHom_of]
  have hc_apply : ∀ g m, c g m = ρ g.1 m := fun g m => rfl
  have hcen : ∀ g, c g ∈ Subring.center E := by
    intro g
    rw [Subring.mem_center_iff]
    intro φ
    ext m
    have h1 : c g m = MonoidAlgebra.of F G g.1 • m := (hc_apply g m).trans (hs _ _).symm
    show φ (c g m) = c g (φ m)
    rw [h1, hc_apply, ← hs, map_smul]
  let f : Subgroup.center G →* Subring.center E :=
    { toFun := fun g => ⟨c g, hcen g⟩
      map_one' := by
        ext m
        show ρ 1 m = m
        rw [map_one]; rfl
      map_mul' := by
        intro g h
        ext m
        show ρ (g.1 * h.1) m = ρ g.1 (ρ h.1 m)
        rw [map_mul]; rfl }
  refine isCyclic_of_injective_ringHom f ?_
  intro g h hgh
  have : ∀ m, ρ g.1 m = ρ h.1 m := by
    intro m
    have := congrArg (fun r : Subring.center E => (r : E) m) hgh
    exact this
  exact Subtype.ext (hfaith (LinearMap.ext this))

end CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreducibleFiniteCenterCyclic
