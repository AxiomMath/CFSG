module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairBasic
public import CFSG.StronglyEmbedded.BenderUnitaryBorel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

universe u

theorem simpleBender_full_borel_structure
    {G : Type u} [Group G] [Finite G] (hmodel : IsSimpleBenderGroup G) :
    ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
      fusionBenderBorel G (2 ^ a) i := by
  rcases hmodel with ⟨⟨a, ha, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
    ⟨⟨a, ha, K, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩⟩
  · let : Finite (PSL2BinaryMatrixGroup a) := Finite.of_surjective e e.surjective
    exact ⟨a, 1, ha, by simp, (bender_psl2_borel_full a ha).map_mulEquiv e.symm⟩
  · let : Finite (SuzukiMatrixGroup m) := Finite.of_surjective e e.surjective
    exact ⟨2 * m + 1, 2, by omega, by simp,
      (bender_suzukiMatrixGroup_borel m hm).map_mulEquiv e.symm⟩
  · let := hfield
    let := hfinite
    let : Fintype K := Fintype.ofFinite K
    have heven : Even (2 ^ a) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    let : CharP K 2 := ringChar.of_eq (FiniteField.even_card_iff_char_two.mpr (by
      rw [← Nat.card_eq_fintype_card, hcard]
      exact Nat.mod_eq_zero_of_dvd
        (even_iff_two_dvd.mp (heven.pow_of_ne_zero (by norm_num)))))
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective e e.surjective
    exact ⟨a, 3, ha, by simp,
      (bender_projectiveSpecialUnitary_borel J a ha hcard hfixed hJ).map_mulEquiv e.symm⟩

theorem simpleBender_borel_rank_and_strong_embedding
    {G : Type u} [Group G] [Finite G] (hmodel : IsSimpleBenderGroup G)
    (B : Subgroup G) (hB : IsBorelSubgroup B) :
    TwoRankAtLeastTwo G ∧ fusionStronglyEmbedded B := by
  obtain ⟨a, i, ha, _, hdata⟩ := simpleBender_full_borel_structure hmodel
  obtain ⟨_, S, hBS⟩ := hB
  have hS := hdata S
  have hcard : 4 ≤ Nat.card (Subgroup.center (S : Subgroup G)) := by
    rw [hS.2.2.2.1]
    simpa only [show 2 ^ 2 = 4 from rfl] using
      Nat.pow_le_pow_right (n := 2) (by omega) ha
  refine ⟨rank_two_of_sylow_center S hcard hS.2.2.1, ?_⟩
  rw [hBS]
  exact hS.1

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
