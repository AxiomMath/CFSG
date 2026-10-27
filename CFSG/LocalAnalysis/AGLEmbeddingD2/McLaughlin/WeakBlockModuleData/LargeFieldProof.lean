module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LargeField
public import CFSG.LocalAnalysis.AGLEmbedding.BlockOutNine
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem lieField_eq_two_of_indexTwo {i : TauCeti.LieTypeIndex} (h : IsClassicalOrG2IndexTwo i) :
    LieField i = 2 := by
  cases i <;> simp_all [IsClassicalOrG2IndexTwo, LieField]


theorem largeFieldParabolic_proved : LargeFieldParabolic := by
  intro Q _ _ Lb P hq d hd hq4 ⟨e⟩ hpar hnot
  by_contra hno
  push Not at hno
  obtain ⟨hPL, T, hT, hNP⟩ := hpar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowTwoOf (T.subgroupOf Lb) ⊤ := by
    have := L246C127.isSylowTwoOf_top_map_subgroupOf (MulEquiv.refl ↥Lb) hT
    simpa using this
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowTwoOf_top hT'
  have hNS : Subgroup.normalizer ((S : Subgroup ↥Lb) : Set ↥Lb) =
      (Lb ⊓ Subgroup.normalizer (T : Set Q)).subgroupOf Lb := by
    rw [hS]
    exact CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer Lb T hT.1
  have hNJ : Subgroup.normalizer ((S : Subgroup ↥Lb) : Set ↥Lb) ≤ P.subgroupOf Lb := by
    rw [hNS]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hNP (Subgroup.mem_subgroupOf.mp hx))
  have hJne : P.subgroupOf Lb ≠ Subgroup.normalizer ((S : Subgroup ↥Lb) : Set ↥Lb) := by
    intro hJ
    apply hnot
    have hPN : P ≤ Subgroup.normalizer (T : Set Q) := fun p hp => by
      have : (⟨p, hPL hp⟩ : ↥Lb) ∈ P.subgroupOf Lb := Subgroup.mem_subgroupOf.mpr hp
      rw [hJ, hNS] at this
      exact (Subgroup.mem_subgroupOf.mp this).2
    have hTP : T ≤ P := fun t ht => by
      have := hNP ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
      exact this
    have hTO : T ≤ pCoreOf 2 P := by
      refine normal_pGroup_le_pCoreOf 2 T P hTP ?_ hT.2.1
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTP]
      exact hPN
    refine ⟨(pCoreOf_le 2 P).trans hPL, pCoreOf_isPGroup 2 P, ?_⟩
    have hd := Subgroup.relIndex_dvd_of_le_left Lb hTO
    exact fun h2 => hT.2.2 (h2.trans hd)
  have hperf : ∀ U : Subgroup ↥Lb, U ≤ P.subgroupOf Lb → ⁅U, U⁆ = U →
      Nat.Coprime 3 (Nat.card U) := by
    intro U hU hUp
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
    have hV := hno (U.map Lb.subtype) (by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := hx
      exact Subgroup.mem_subgroupOf.mp (hU hu)) (by
      rw [← Subgroup.map_commutator, hUp])
    rwa [Subgroup.card_map_of_injective Lb.subtype_injective] at hV
  have hρ : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥Lb)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center ↥Lb)).ker ≤ Subgroup.center ↥Lb :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨h1, h2, h3, h4⟩ := map_overgroup_of_central hρ hker S hNJ hJne hperf
  have hcl := isClassicalOrG2IndexTwo_of_perfect_coprime d hd e
    (S.mapSurjective hρ) (P.subgroupOf Lb |>.map (QuotientGroup.mk' (Subgroup.center ↥Lb)))
    (by simpa using h2) (by simpa using h3) h4
  have := lieField_eq_two_of_indexTwo hcl
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
