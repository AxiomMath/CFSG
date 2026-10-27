module

public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Separation
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Multiplier
public import CFSG.LocalAnalysis.OddStandard.SmallF3.BalancedCentre

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3Interfaces

theorem oddLieType_of_evenCentre
    (hH : ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd)
    (hGA : Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : StandardSetting G L)
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    (hQ : SmallF3LieQuotient (L ⧸ center L)) (hev : Even (Nat.card (center L))) :
    OddLieType G ∨ (LieModel (L ⧸ center L) .PSU 4 3 1 ∧ Nat.card (center L) = 2) := by
  by_cases hres : LieModel (L ⧸ center L) .PSU 4 3 1 ∧ Nat.card (center L) = 2
  · exact Or.inr hres
  · refine Or.inl ?_
    have hq : CFSG.IsQuasisimple L :=
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hS.standard.1
    have hperf : Group.IsPerfect L := hq.1
    have hM : ComponentClassification.HarrisLit.IsMTypeSchur 3 L :=
      isMTypeSchur_of_multiplier hS.standard hev
        (by
          have hQ' := hQ
          unfold SmallF3LieQuotient at hQ'
          rcases hQ' with h | h | h | h | h | h | h | h <;> exact ⟨_, _, _, h⟩)
        (by
          intro n r hn hr h
          rcases h with h | h
          · obtain ⟨rfl, rfl⟩ := eq_of_lieModel_psl hQ hn hr h
            have h4 : LieModel (L ⧸ center L) .PSL 4 3 1 := by
              simpa only [show (2 : ℕ) * 2 = 4 by norm_num] using h
            have hcenter : Nat.card (center L) = 2 :=
              card_center_eq_two_of_psl_four_three hGA hperf hev h4
            have hmult : Nat.card (Open.griessHopfMultiplier (L ⧸ center L)) = 2 :=
              card_griessHopfMultiplier_psl_four_three hGA h4
            rw [hcenter, hmult]
          · obtain ⟨rfl, rfl⟩ := eq_of_lieModel_psu hQ hn hr h
            have h4 : LieModel (L ⧸ center L) .PSU 4 3 1 := by
              simpa only [show (2 : ℕ) * 2 = 4 by norm_num] using h
            have hmult : Nat.card (Open.griessHopfMultiplier (L ⧸ center L)) = 36 :=
              card_griessHopfMultiplier_psu_four_three hGA h4
            have hcard36 : Nat.card (center L) ∣ 36 :=
              card_center_dvd_thirtySix_of_psu_four_three hGA hperf h4
            have h2grp : IsPGroup 2 (center L) := isPGroup_two_center_of_balanced hS hbal
            haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
            obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := center L)).1 h2grp
            have hle : k ≤ 2 := by
              have hdvd : 2 ^ k ∣ (36 : ℕ) := hk ▸ hcard36
              have h := (Nat.prime_two.pow_dvd_iff_le_factorization
                (by norm_num : (36 : ℕ) ≠ 0)).1 hdvd
              have hf : (36 : ℕ).factorization 2 = 2 := by decide +kernel
              omega
            have hk0 : k ≠ 0 := by
              rintro rfl
              rw [pow_zero] at hk
              exact Nat.not_even_one (hk ▸ hev)
            have hk1 : k ≠ 1 := by
              rintro rfl
              exact hres ⟨h4, by rw [hk]; norm_num⟩
            have hk2 : k = 2 := by omega
            rw [hk, hk2, hmult]
            decide +kernel)
    exact oddLieType_of_isMTypeSchur_of_simpleKProperOdd hH hS hev (p := 3)
      Nat.prime_three (by norm_num) hM

end CFSG.OddStandard.SmallF3
