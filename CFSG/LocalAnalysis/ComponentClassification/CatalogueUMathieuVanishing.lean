module

public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.CatalogueU

open CFSG.Blueprint Subgroup

theorem centralizer_generalizedFitting_eq_bot_of_simple {X : Type*} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) :
    centralizer (CFSG.generalizedFitting X : Set X) = ⊥ := by
  set F := CFSG.generalizedFitting X
  have hle : centralizer (F : Set X) ≤ F := CFSG.centralizer_generalizedFitting_le X
  have hcenter : center F = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center F) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab
  refine eq_bot_iff.2 fun x hx => ?_
  have hxF := hle hx
  have hxZ : (⟨x, hxF⟩ : F) ∈ center F := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp hx g g.2)
  rw [hcenter, mem_bot] at hxZ
  exact (mem_bot).2 (congrArg Subtype.val hxZ)

theorem catalog_mathieu_almost_simple_odd_core_vanishing {X : Type*} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (hM : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.M11) ∨
      Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.M12) ∨
      Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.M22) ∨
      Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.M23) ∨
      Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.M24))
    (z : X) (hz : orderOf z = 2) : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  exact Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
    (CFSG.generalizedFitting X) hM (centralizer_generalizedFitting_eq_bot_of_simple hsimple hnab)
    z hz

end CFSG.ComponentClassification.CatalogueU
