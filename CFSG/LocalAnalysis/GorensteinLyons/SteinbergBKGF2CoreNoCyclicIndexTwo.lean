module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2WitnessCentralizerRank
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQCyclicIndexTwoCoreRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

namespace SteinbergBK

theorem pRank_two_le_of_sylow_le {G : Type*} [Group G] [Finite G] {S M : Subgroup G}
    (hSM : S ≤ M) (hS : IsSylowOf 2 S ⊤) : CFSG.pRank 2 G ≤ CFSG.pRank 2 M := by
  have := Fact.mk Nat.prime_two
  obtain ⟨-, hS2, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  rw [relIndex_top_right] at hidx
  have h1 := (CFSG.SectionRank.pRank_sylow (hS2.toSylow hidx)).1
  rw [IsPGroup.toSylow_coe] at h1
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 G, CFSG.SectionRank.pRank_eq_open_pRank_top 2 M,
    ← h1, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup M]
  exact CFSG.SectionRank.pRank_mono one_lt_two hSM

theorem three_le_pRank_two_of_gf2_witness
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) : 3 ≤ CFSG.pRank 2 G ∧ CFSG.pRank 2 G ≤ CFSG.pRank 2 M := by
  have := Fact.mk Nat.prime_two
  obtain ⟨⟨z, -, -, -, -, -, -, hSyl⟩, -, -, -, -, -, -, -, he3⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM rfl rfl
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 M))
  have hSM : IsSylowOf 2 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
  exact ⟨(he3 he).1, pRank_two_le_of_sylow_le (map_subtype_le _) (hSyl _ hSM).1⟩

end SteinbergBK

open SteinbergBK

theorem gf2_core_has_no_cyclic_index_two_subgroup
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) :
    ∀ A : Subgroup G, A ≤ Q → IsCyclic A → 2 < A.relIndex Q := by
  intro A hAQ hA
  by_contra hidx
  push Not at hidx
  have hcharM : CFSG.IsCharacteristicP 2 M := hchar M hM.1
  obtain ⟨h3, hle⟩ := three_le_pRank_two_of_gf2_witness hchar he hM hsym hB hBM
  set ι : CFSG.pCore 2 M →* G := M.subtype.comp (CFSG.pCore 2 M).subtype with hι
  have hιinj : Function.Injective ι := M.subtype_injective.comp (CFSG.pCore 2 M).subtype_injective
  have hιrange : ι.range = Q := by
    rw [hQ, hι, MonoidHom.range_comp, range_subtype]
    rfl
  set A' : Subgroup (CFSG.pCore 2 M) := A.comap ι with hA'
  have hA'map : A'.map ι = A := by
    rw [hA', map_comap_eq, hιrange, inf_eq_right.mpr hAQ]
  have hA'cyc : IsCyclic A' := by
    have e := A'.equivMapOfInjective ι hιinj
    rw [hA'map] at e
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hA'idx : A'.index ≤ 2 := by
    rw [hA', index_comap, hιrange]
    exact hidx
  have h2 := characteristic_two_cyclic_index_two_core_rank_bound hcharM A' hA'cyc hA'idx
  omega

end CFSG.LocalAnalysis.GorensteinLyons
