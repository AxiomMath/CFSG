module

public import CFSG.Open.FusionDefs
public import CFSG.Open.RankThreeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GH74.Bender
import CFSG.GH74.Uniqueness.Bender.Lemma32

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup CFSG.GH74.Uniqueness

theorem false_of_bender_parabolic {A : Type} [Group A] [Finite A]
    (K K₀ U : Subgroup A) (hB : CFSG.Open.fusionIsBenderGroup ↥K)
    (hUK : CFSG.ABGLocalTools.IsSylowOf 2 U K) (hN : Subgroup.normalizer (U : Set A) ⊓ K ≤ K₀)
    (hK₀K : K₀ ≤ K) (hne : K₀ ≠ K)
    (hSyl : ∀ V : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 V K₀ →
      ¬ V ≤ CFSG.Open.rankThreePrimeCore 3 K₀) : False := by
  obtain ⟨_, _, _, hBT⟩ := Bender.isBenderGroup_iff_exists_benderType.mp
    (CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup hB)
  obtain ⟨Q, hQ⟩ := hUK.exists_sylow_eq_subgroupOf
  have hUN : U ≤ Subgroup.normalizer (U : Set A) := Subgroup.le_normalizer
  have hUK₀ : U ≤ K₀ := fun u hu =>
    hN (Subgroup.mem_inf.mpr ⟨hUN hu, hUK.le hu⟩)
  have hQJ : (Q : Subgroup K) ≤ K₀.subgroupOf K := by
    rw [hQ]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hUK₀ (Subgroup.mem_subgroupOf.mp hx))
  have hJne : K₀.subgroupOf K ≠ ⊤ := fun h =>
    hne (le_antisymm hK₀K (Subgroup.subgroupOf_eq_top.mp h))
  have hle := hBT.le_borel_of_sylow_le Q hQJ hJne
  have hNQ : Bender.borel (Q : Subgroup K) = (Subgroup.normalizer (U : Set A)).subgroupOf K := by
    unfold Bender.borel
    rw [hQ]
    exact (Subgroup.subgroupOf_normalizer_eq hUK.le).symm
  have hK₀N : K₀ ≤ Subgroup.normalizer (U : Set A) := by
    intro x hx
    have hy : (⟨x, hK₀K hx⟩ : ↥K) ∈ Bender.borel (Q : Subgroup K) :=
      hle (show (⟨x, hK₀K hx⟩ : ↥K) ∈ K₀.subgroupOf K from Subgroup.mem_subgroupOf.mpr hx)
    rw [hNQ] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  have hnormal : (U.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUK₀).mpr hK₀N
  have hsyl0 : CFSG.ABGLocalTools.IsSylowOf 2 U K₀ := hUK.of_le hUK₀ hK₀K
  have hcop : Nat.Coprime 3 (Nat.card U) := by
    rw [hUK.card_eq]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hmem : U ∈ {N : Subgroup A |
      N ≤ K₀ ∧ (N.subgroupOf K₀).Normal ∧ Nat.Coprime 3 (Nat.card N)} :=
    ⟨hUK₀, hnormal, hcop⟩
  exact hSyl U hsyl0 (le_sSup hmem)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
