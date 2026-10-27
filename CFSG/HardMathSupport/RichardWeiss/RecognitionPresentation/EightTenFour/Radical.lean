module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.C1Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

theorem normal_subgroupOf_inf_normalizer {H R : Subgroup G} (hRH : R ≤ H) :
    (R.subgroupOf (H ⊓ Subgroup.normalizer (R : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (le_inf hRH Subgroup.le_normalizer)).mpr inf_le_right

theorem isTwoRadicalIn_iff {H R : Subgroup G} :
    IsTwoRadicalIn H R ↔ R ≤ H ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧
      ∀ T : Subgroup G, T ≤ H ⊓ Subgroup.normalizer (R : Set G) → IsPGroup 2 T →
        (T.subgroupOf (H ⊓ Subgroup.normalizer (R : Set G))).Normal → T ≤ R := by
  constructor
  · rintro ⟨hRH, hne, hR⟩
    refine ⟨hRH, hne, ?_, fun T hT hT2 hTn => ?_⟩
    · rw [hR]; exact pCoreOf_isPGroup 2 _
    · rw [hR]; exact normal_pGroup_le_pCoreOf 2 T _ hT hTn hT2
  · rintro ⟨hRH, hne, hR2, hmax⟩
    refine ⟨hRH, hne, le_antisymm ?_ ?_⟩
    · exact normal_pGroup_le_pCoreOf 2 R _ (le_inf hRH Subgroup.le_normalizer)
        (normal_subgroupOf_inf_normalizer hRH) hR2
    · exact hmax _ (pCoreOf_le 2 _) (pCoreOf_isPGroup 2 _) (pCoreOf_normal 2 _)

theorem le_of_isPGroup_of_odd_index [Finite G] {H R : Subgroup G} (hRH : R ≤ H)
    (hR2 : IsPGroup 2 R)
    (hodd : ¬ 2 ∣ (R.subgroupOf (H ⊓ Subgroup.normalizer (R : Set G))).index)
    {T : Subgroup G} (hT : T ≤ H ⊓ Subgroup.normalizer (R : Set G)) (hT2 : IsPGroup 2 T) :
    T ≤ R := by
  set N : Subgroup G := H ⊓ Subgroup.normalizer (R : Set G) with hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR' : IsPGroup 2 (R.subgroupOf N) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe
    (le_inf hRH Subgroup.le_normalizer)).symm
  have hRn : (R.subgroupOf N).Normal := normal_subgroupOf_inf_normalizer hRH
  let P : Sylow 2 ↥N := hR'.toSylow hodd
  have hPn : P.Normal := hRn
  have hT' : IsPGroup 2 (T.subgroupOf N) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hT).symm
  obtain ⟨P', hTP'⟩ := hT'.exists_le_sylow
  have := Sylow.unique_of_normal P hPn
  have hPP : P' = P := Subsingleton.elim _ _
  have h1 : T.subgroupOf N ≤ R.subgroupOf N := by
    have := hTP'
    rw [hPP] at this
    exact this
  intro t ht
  exact h1 (show (⟨t, hT ht⟩ : ↥N) ∈ T.subgroupOf N from ht)

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
