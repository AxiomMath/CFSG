module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open SpChain

theorem even_symplectic_almost_simple_inner_and_field_exclusion {X : Type} [Group X]
    [Finite X] [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {r f : ℕ}
    (hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSp r 2 f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (θ : CFSG.generalizedFitting X ≃* StatedProj (StatedSp r K))
    (ρ : X →* MulAut (StatedProj (StatedSp r K)))
    (hρ : ∀ (x : X) (y z : CFSG.generalizedFitting X), (z : X) = x * y * x⁻¹ →
      ρ x (θ y) = θ z) :
    (∀ z : X, orderOf z = 2 → ρ z ∈ spSemilinearAutGroup r K →
      CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥) ∧
    (3 ≤ r → ∀ z : X, orderOf z = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥) ∧
    ∀ z : X, orderOf z = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) ≠ ⊥ →
      r = 2 ∧ ρ z ∉ spSemilinearAutGroup r K ∧ z ∉ CFSG.generalizedFitting X ∧
        CFSG.generalizedFitting X < ⊤ := by
  obtain ⟨hr2, hf1, -, hall⟩ :=
    even_symplectic_almost_simple_field_involution_exclusion hnonab hmodel
  obtain ⟨-, hρ5⟩ := hall K hK θ
  obtain ⟨hρinj, hmap, hvan, hE3, -⟩ := hρ5 ρ hρ
  have hIH : inner (StatedProj (StatedSp r K)) ≤ ρ.range := by
    rw [← hmap]
    exact Subgroup.map_le_range ρ _
  have hFI : ∀ z ∈ CFSG.generalizedFitting X, ρ z ∈ inner (StatedProj (StatedSp r K)) :=
    fun z hz => hmap ▸ ⟨z, hz, rfl⟩
  have hvanE : ∀ z : X, orderOf z = 2 → ρ z ∈ spSemilinearAutGroup r K →
      CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
    intro z hz hzE
    by_cases hzF : z ∈ CFSG.generalizedFitting X
    · rw [oddCore_centralizer_eq_bot_iff hρinj z]
      exact even_symplectic_inner_involution_full_centralizer_odd_core hr2 hf1 hK ρ.range hIH
        (hFI z hzF) (by rw [orderOf_injective ρ hρinj z, hz])
    · exact hvan z hz hzF hzE
  refine ⟨hvanE, fun hr3 z hz => hvanE z hz (hE3 hr3 z), fun z hz hne => ?_⟩
  have hzE : ρ z ∉ spSemilinearAutGroup r K := fun h => hne (hvanE z hz h)
  have hr : r = 2 := by
    by_contra hr
    exact hzE (hE3 (by omega) z)
  have hzF : z ∉ CFSG.generalizedFitting X := fun h =>
    hzE (inner_le_spSemilinearAutGroup (hFI z h))
  exact ⟨hr, hzE, hzF, lt_top_iff_ne_top.mpr fun htop => hzF (htop ▸ Subgroup.mem_top z)⟩

end CFSG.ComponentClassification.UnbalancedCatalog
