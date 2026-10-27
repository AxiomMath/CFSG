module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open SpChain

theorem even_symplectic_almost_simple_odd_core_vanishing {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {r f : ℕ}
    (hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSp r 2 f) :
    (∀ z : X, orderOf z = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥) ∧
    ¬ ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) ≠ ⊥ := by
  have hvan : ∀ z : X, orderOf z = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
    intro z hz
    by_contra hne
    obtain ⟨-, -, -, hne22⟩ := hmodel.1
    obtain ⟨-, hf1, ⟨K, _, _, hK, ⟨θ⟩⟩, hall⟩ :=
      even_symplectic_almost_simple_field_involution_exclusion hnonab hmodel
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hK
    obtain ⟨⟨ρ, hρ⟩, hρ5⟩ := hall K hK θ
    obtain ⟨hρinj, hmap, -⟩ := hρ5 ρ hρ
    obtain ⟨-, -, hcase⟩ :=
      even_symplectic_almost_simple_inner_and_field_exclusion hnonab hmodel K hK θ ρ hρ
    obtain ⟨rfl, hzE, hzF, -⟩ := hcase z hz hne
    have hρz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hρinj z, hz]
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hγall⟩ := even_symplectic_two_exterior_square_automorphism hf1 hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hEven, -⟩ := hγall γ hγ
    rcases Nat.even_or_odd f with hfe | hfo
    · exact hzE (hEven hfe (ρ z) hρz)
    · obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra h
        obtain rfl : m = 0 := by omega
        exact hne22 rfl
      have hzI : ρ z ∉ inner (StatedProj (StatedSp 2 K)) := by
        intro h
        rw [← hmap] at h
        obtain ⟨y, hy, hyz⟩ := h
        exact hzF (hρinj hyz ▸ hy)
      have hIH : inner (StatedProj (StatedSp 2 K)) ≤ ρ.range := by
        rw [← hmap]
        exact Subgroup.map_le_range ρ _
      obtain ⟨-, -, -, -, -, -, -, -, -, hodd⟩ :=
        even_symplectic_two_suzuki_full_centralizer_odd_core hm hK γ hγ
      exact hne ((oddCore_centralizer_eq_bot_iff hρinj z).mpr
        (hodd ρ.range hIH (ρ z) ⟨z, rfl⟩ hρz hzI))
  exact ⟨hvan, fun ⟨z, hz, hne⟩ => hne (hvan z hz)⟩

end CFSG.ComponentClassification.UnbalancedCatalog
