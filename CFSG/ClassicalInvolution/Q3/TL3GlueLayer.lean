module

public import CFSG.ClassicalInvolution.Q3.TL3GlueR

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

section Components

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem isComponentOf_map_mulAut (α : MulAut X) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    IsComponentOf (K.map α.toMonoidHom) ⊤ := by
  have hK' := (CFSG.isComponent_iff_open K).mpr hK
  refine (CFSG.isComponent_iff_open _).mp ⟨?_, hK'.2.map α.surjective⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K.equivMapOfInjective α.toMonoidHom α.injective) hK'.1

theorem component_le_of_not_commute {H K : Subgroup X} (hH : IsSubnormal H ⊤) {ub : X}
    (hub : ub ∈ H) (hK : IsComponentOf K ⊤) (hKu : ∃ y ∈ K, y * ub ≠ ub * y) : K ≤ H := by
  have hH' : H.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff H).mp hH
  rcases CFSG.LocalCores.component_subnormal_subgroup ((CFSG.isComponent_iff_open K).mpr hK) hH'
    with h | h
  · exact h
  · exfalso
    obtain ⟨y, hy, hyu⟩ := hKu
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact hyu ((Subgroup.mem_centralizer_iff.mp (hcen hy)) ub hub).symm

end Components

namespace TightDatum

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  (d : TightDatum R S t)

theorem layerRigidAt_of_subnormal {ub : d.Dbar} {H : Subgroup d.Dbar} (hH : IsSubnormal H ⊤)
    (hub : ub ∈ H)
    (huniq : ∀ K₁ K₂ : Subgroup d.Dbar, IsComponentOf K₁ ⊤ → IsComponentOf K₂ ⊤ → K₁ ≤ H →
      K₂ ≤ H → (∃ y ∈ K₁, y * ub ≠ ub * y) → (∃ y ∈ K₂, y * ub ≠ ub * y) → K₁ = K₂)
    (hrigid : ∀ K : Subgroup d.Dbar, IsComponentOf K ⊤ → K ≤ H → (∃ y ∈ K, y * ub ≠ ub * y) →
      ∀ (α : MulAut d.Dbar) (k : ℕ), α ^ 3 ^ k = 1 → α ub = ub →
        (∀ c ∈ Subgroup.centralizer ({ub} : Set d.Dbar),
          c⁻¹ * α c ∈ Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar))) →
        K.map α.toMonoidHom = K → ∃ e ∈ K, ∀ y ∈ K, α y = e * y * e⁻¹) :
    d.LayerRigidAt ub := by
  refine ⟨fun K₁ K₂ h₁ h₂ hu₁ hu₂ => huniq K₁ K₂ h₁ h₂ (component_le_of_not_commute hH hub h₁ hu₁)
    (component_le_of_not_commute hH hub h₂ hu₂) hu₁ hu₂, ?_⟩
  intro K hK hKu α k hα hαu hC
  have hKH := component_le_of_not_commute hH hub hK hKu
  have hαK := isComponentOf_map_mulAut α hK
  have hαKu : ∃ y ∈ K.map α.toMonoidHom, y * ub ≠ ub * y := by
    obtain ⟨y, hy, hyu⟩ := hKu
    refine ⟨α y, ⟨y, hy, rfl⟩, fun h => hyu ?_⟩
    have : α (y * ub) = α (ub * y) := by rw [map_mul, map_mul, hαu]; exact h
    exact α.injective this
  have heq := huniq _ _ hαK hK (component_le_of_not_commute hH hub hαK hαKu) hKH hαKu hKu
  exact hrigid K hK hKH hKu α k hα hαu hC heq

end TightDatum

end CFSG.ClassicalInvolution.Q3
