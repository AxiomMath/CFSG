module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageChain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneOddPairSetup
public import CFSG.LocalAnalysis.SeitzReduction.RankOneAffineEvenPair

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open CFSG.Blueprint

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Certificates

theorem smallRootRegularNormalInput : SmallRootRegularNormalInput := by
  intro D _ _ R X U P n h h3 hcat
  by_cases hn3 : n = 3
  · subst hn3
    obtain ⟨-, -, -, -, hout⟩ := gms_normal_root_degree_eight_completion h.1 h3
    rcases hout with ⟨E, hEN, hEn, hreg, -⟩ | ⟨-, β, hβ, -⟩
    · exact Or.inl ⟨E, hEN, hEn, hreg⟩
    · exact Or.inr ⟨rfl, β, hβ⟩
  · left
    obtain ⟨Q₀, hQ₀, hQ₀R⟩ :=
      Set.exists_ne_of_one_lt_ncard (s := gmsRootConjugates (U ⊔ R) R) (by omega) R
    set β : gmsRootConjugates (U ⊔ R) R := ⟨Q₀, hQ₀⟩
    have hβR : (β : Subgroup D) ≠ R := hQ₀R
    rcases Nat.even_or_odd (Nat.card (gmsPairStabilizer U R β)) with hev | hodd
    · obtain ⟨-, -, -, -, -, -, -, E, hEN, hEn, hreg, -⟩ :=
        gms_normal_root_even_pair_completion h.1 h3 β hβR hev
      exact ⟨E, hEN, hEn, hreg⟩
    · obtain ⟨-, hΔ, -, -, h2tr, -⟩ := gms_normal_root_partition_and_two_transitivity h.1 h3
      have hΔcard : Nat.card (gmsRootConjugates (U ⊔ R) R) = 2 ^ n := by
        rw [Nat.card_coe_set_eq]
        exact hΔ
      obtain ⟨hNRodd, hNRdvd⟩ := odd_card_gmsPermStabilizer_of_odd h.1 h3 β hβR hodd
      have h2 : ∀ a b c d : gmsRootConjugates (U ⊔ R) R, a ≠ b → c ≠ d →
          ∃ x ∈ (gmsRootConjugateAction (U ⊔ R) R).range, x a = c ∧ x b = d :=
        fun a b c d hab hcd => h2tr a b c d hab hcd
      rcases odd_stabilizer_two_transitive_catalog_of_dvd (gmsRootConjugateAction (U ⊔ R) R).range
          h2 (le_trans (by norm_num) h.three_le) hΔcard ⟨R, gms_R_mem⟩ hNRodd hNRdvd hcat with
        ⟨A, hAN, hAn, -, -, -, hreg⟩ | ⟨hn, -⟩
      · exact ⟨A, hAN, hAn, hreg⟩
      · exact absurd hn hn3

end Certificates

end CFSG.SeitzReduction.RankOne
