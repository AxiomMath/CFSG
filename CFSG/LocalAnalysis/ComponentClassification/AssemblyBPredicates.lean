module

public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.ComponentClassification.AssemblyBPredicates

theorem oddCore_eq_open (G : Type*) [Group G] :
    Assembly.oddCore G = Open.componentClassificationOddCore G := rfl

theorem oddCore_eq_native (G : Type*) [Group G] :
    Assembly.oddCore G = CFSG.oddCore G := rfl

theorem oddCore_eq_piCore (G : Type*) [Group G] :
    Assembly.oddCore G = CFSG.piCore {p : Nat.Primes | p.val ≠ 2} G := by
  rw [oddCore_eq_native]
  exact CFSG.oddCore_eq_piCore G

theorem isSubnormal_iff_open {G : Type*} [Group G] (lower upper : Subgroup G) :
    Assembly.IsSubnormal lower upper ↔ Open.IsSubnormal lower upper :=
  Assembly.isSubnormal_iff_open

theorem isSubnormal_top_iff_mathlib {G : Type*} [Group G] (subgroup : Subgroup G) :
    Assembly.IsSubnormal subgroup ⊤ ↔ subgroup.IsSubnormal :=
  Assembly.IsSubnormal.top_iff

theorem isQuasisimple_iff_open (G : Type*) [Group G] :
    Assembly.IsQuasisimple G ↔ Open.IsQuasisimple G := Iff.rfl

theorem isQuasisimple_iff_native (G : Type*) [Group G] :
    Assembly.IsQuasisimple G ↔ CFSG.IsQuasisimple G := by
  constructor
  · intro hquasisimple
    exact ⟨⟨hquasisimple.1⟩, hquasisimple.2,
      Helpers.quasisimple_central_quotient_nonabelian G
        ((isQuasisimple_iff_open G).mp hquasisimple)⟩
  · rintro ⟨hperfect, hsimple, _⟩
    exact ⟨hperfect.commutator_eq_top, hsimple⟩

theorem isComponentOf_iff_open {G : Type*} [Group G] (component ambient : Subgroup G) :
    Assembly.IsComponentOf component ambient ↔ Open.IsComponentOf component ambient :=
  Assembly.isComponentOf_iff_open

theorem isComponentOf_top_iff_native {G : Type*} [Group G] (component : Subgroup G) :
    Assembly.IsComponentOf component ⊤ ↔ CFSG.IsComponent component :=
  (isComponentOf_iff_open component ⊤).trans (CFSG.isComponent_iff_open component).symm

theorem isComponentType_iff_open (G : Type*) [Group G] :
    Assembly.IsComponentType G ↔ Open.componentClassificationComponentType G := by
  constructor
  · rintro ⟨involution, hinvolution, component, hcomponent⟩
    exact ⟨involution, hinvolution, component,
      (isComponentOf_iff_open component ⊤).mp hcomponent⟩
  · rintro ⟨involution, hinvolution, component, hcomponent⟩
    exact ⟨involution, hinvolution, component,
      (isComponentOf_iff_open component ⊤).mpr hcomponent⟩

end CFSG.ComponentClassification.AssemblyBPredicates
