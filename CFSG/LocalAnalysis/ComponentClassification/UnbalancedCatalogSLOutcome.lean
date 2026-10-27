module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLGraphCoset

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank

open EvenLinearSL

theorem even_linear_almost_simple_unbalanced_outcome {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {n f : ℕ}
    (hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSL n 2 f)
    (hz : ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore ↥(centralizer {z}) ≠ ⊥) :
    CFSG.generalizedFitting X < ⊤ ∧
    (CFSG.Blueprint.OddLieType (CFSG.generalizedFitting X) ∨
      StatedClassicalModel (CFSG.generalizedFitting X) .PSL 3 2 2) ∧
    (3 ≤ n → (n = 3 ∧ f = 1) ∨ (n = 3 ∧ f = 2)) ∧
    (n = 3 → f = 1 → CFSG.Blueprint.LieModel (CFSG.generalizedFitting X) .PSL 2 7 1) := by
  obtain ⟨z, hz2, hzne⟩ := hz
  have hn2 : 2 ≤ n := hmodel.1.2.2.1
  have hf : 1 ≤ f := hmodel.1.2.1
  have h31 : n = 3 → f = 1 → CFSG.Blueprint.LieModel (CFSG.generalizedFitting X) .PSL 2 7 1 := by
    rintro rfl rfl
    exact PSL3_two_PSL2_seven_paired_isomorphism _ (Or.inl ⟨by decide, hmodel⟩)
  rcases Nat.lt_or_ge n 3 with hn | hn
  ·
    obtain rfl : n = 2 := by omega
    obtain ⟨-, -, hout⟩ := even_linear_two_almost_simple_unbalanced_outcome hnonab hmodel
    obtain ⟨hlt, -, -, -, -, -, -, hodd, -⟩ := hout z hz2 hzne
    exact ⟨hlt, Or.inl hodd, fun h => absurd h (by omega), h31⟩
  obtain ⟨⟨K, hKf, hcard, ⟨θ⟩⟩, hred⟩ :=
    even_linear_higher_almost_simple_graph_coset_reduction hnonab hn hf hmodel
  obtain ⟨-, hinj, himage, -, hcons⟩ := hred K hcard θ
  obtain ⟨-, -, hlt⟩ := hcons z hz2 hzne
  set ρ := conjModel θ with hρ
  have hinnH : inner (projectiveSL n K) ≤ ρ.range := by
    rw [← himage]
    exact map_le_range ρ _
  have hρz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hinj z, hz2]
  have hne' : CFSG.oddCore ↥(ρ.range ⊓ centralizer {ρ z}) ≠ ⊥ := fun h =>
    hzne (EvenCatalog.oddCore_eq_bot_of_mulEquiv (EvenCatalog.centralizerMapEquiv hinj z).symm h)
  obtain ⟨hexc, -⟩ := even_linear_all_involution_centralizer_exceptions hn hf hcard hinnH hρz hne'
  have hnf : (n = 3 ∧ f = 1) ∨ (n = 3 ∧ f = 2) := by
    rcases hexc with ⟨h3, h2⟩ | ⟨h3, h4⟩
    · refine Or.inl ⟨h3, Nat.pow_right_injective le_rfl ?_⟩
      change 2 ^ f = 2 ^ 1
      rw [← hcard, h2, pow_one]
    · refine Or.inr ⟨h3, Nat.pow_right_injective le_rfl ?_⟩
      change 2 ^ f = 2 ^ 2
      rw [← hcard, h4]
  refine ⟨hlt, ?_, fun _ => hnf, h31⟩
  rcases hnf with ⟨h3, h1⟩ | ⟨h3, h2⟩
  · left
    have hadm : StatedLieAdmissible .PSL 2 7 1 :=
      ⟨Nat.prime_seven, le_rfl, le_rfl, by decide, by decide⟩
    exact ⟨.PSL, 2, 7, 1, Nat.prime_seven, by norm_num, hadm, h31 h3 h1⟩
  · right
    subst h3
    subst h2
    exact hmodel

end CFSG.ComponentClassification.UnbalancedCatalog
