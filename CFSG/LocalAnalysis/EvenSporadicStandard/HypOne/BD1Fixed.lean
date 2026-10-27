module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.Monster.B.GSide.TwoDNativeOrderFinal

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.Monster.B.GSide CFSG.Monster.B CFSG.EvenSporadicStandard.HypOne
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8


theorem not_prime_card_omegaPlus : ¬ (Nat.card ↥OmegaPlus).Prime := by
  intro hp
  have hd : 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 ∣ Nat.card ↥OmegaPlus := dvd_natCard_OmegaPlus
  have h2 : 2 ∣ Nat.card ↥OmegaPlus := dvd_trans (by norm_num) hd
  rcases (Nat.dvd_prime hp).1 h2 with h | h
  · omega
  · rw [← h] at hd
    norm_num at hd


theorem fixes_T9S_of_few_conjugates
    (n : ↥(Subgroup.centralizer ({t2DS} : Set Shat)))
    (hn : Nat.card {y : ↥(Subgroup.centralizer ({t2DS} : Set Shat)) // IsConj n y} ≤ 4) :
    ∀ x ∈ T9S, (n : Shat) * x * (n : Shat)⁻¹ = x := by
  have hN6 := centralizer_t2DS_le_normalizer
  have hsurj := rhoPlus_surjective hN6
  have hs := isSimpleGroup_OmegaPlus
  have hfin : Finite ↥(Subgroup.centralizer ({t2DS} : Set Shat)) := inferInstance
  have hfinΩ : Finite ↥OmegaPlus := inferInstance
  have hcenΩ : Subgroup.center ↥OmegaPlus = ⊥ :=
    center_eq_bot_of_isSimpleGroup not_prime_card_omegaPlus
  have hΩcard : 24 < Nat.card ↥OmegaPlus := by
    have hd : 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 ∣ Nat.card ↥OmegaPlus := dvd_natCard_OmegaPlus
    have := Nat.le_of_dvd Nat.card_pos hd
    omega
  have hK₀idx : (Subgroup.centralizer ({n} : Set ↥(Subgroup.centralizer ({t2DS} : Set Shat)))).index
      ≤ 4 := by
    rw [index_centralizer_eq_card_conj]
    exact hn
  have hK'idx : ((Subgroup.centralizer ({n} : Set ↥(Subgroup.centralizer
      ({t2DS} : Set Shat)))).map (rhoPlus hN6)).index ≤ 4 :=
    le_trans (index_map_le_of_surjective (rhoPlus hN6) hsurj _) hK₀idx
  have hsub : ((Subgroup.centralizer ({n} : Set ↥(Subgroup.centralizer
      ({t2DS} : Set Shat)))).map (rhoPlus hN6)).subgroupOf OmegaPlus = ⊤ :=
    eq_top_of_index_le_four hΩcard _ (le_trans (relIndex_le_index_of_finite _ OmegaPlus) hK'idx)
  have hΩK' := Subgroup.subgroupOf_eq_top.1 hsub
  have h1 : rhoPlus hN6 n = 1 := by
    refine eq_one_of_commute_of_index_two OmegaPlus index_OmegaPlus_dvd_two hcenΩ
      center_orthogonalGroup_qPlus (rhoPlus hN6 n) fun w hw => ?_
    obtain ⟨k, hk, rfl⟩ := hΩK' hw
    have hkn : k * n = n * k := Subgroup.mem_centralizer_singleton_iff.1 hk
    have hρ := congrArg (rhoPlus hN6) hkn.symm
    rw [map_mul, map_mul] at hρ
    exact hρ
  exact (rhoPlus_eq_one_iff hN6 n).1 h1

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
