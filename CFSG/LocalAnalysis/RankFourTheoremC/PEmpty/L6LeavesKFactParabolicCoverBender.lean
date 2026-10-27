module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
import CFSG.GH74.Bender
import CFSG.GH74.Uniqueness.Bender.Lemma32

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPCov

open CFSG.Open Subgroup CFSG.GH74.Uniqueness

theorem false_of_bender {A : Type} [Group A] [Finite A]
    {K K₀ : Subgroup A} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hB : fusionIsBenderGroup ↥K)
    (hpar : IsParabolicTwo A K K₀) (hne : K₀ ≠ K)
    (hSyl : ∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ →
      ¬ U ≤ rankThreePrimeCore p K₀) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK₀K, U, hU, hUN⟩ := hpar
  obtain ⟨n, i, e, hBT⟩ := Bender.isBenderGroup_iff_exists_benderType.mp
    (CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup hB)
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  have hUK : U ≤ K := hU.le
  have hUK₀ : U ≤ K₀ := fun u hu => hUN ⟨Subgroup.le_normalizer hu, hUK hu⟩
  have hQJ : (Q : Subgroup ↥K) ≤ K₀.subgroupOf K := by
    rw [hQ]
    exact fun u hu => hUK₀ hu
  have hJ : K₀.subgroupOf K ≠ ⊤ := fun h =>
    hne (le_antisymm hK₀K (Subgroup.subgroupOf_eq_top.mp h))
  have hle := hBT.le_borel_of_sylow_le Q hQJ hJ
  have hK₀N : K₀ ≤ normalizer (U : Set A) := by
    intro k hk
    have h1 : (⟨k, hK₀K hk⟩ : ↥K) ∈ Bender.borel (Q : Subgroup ↥K) := hle hk
    have h2 : (⟨k, hK₀K hk⟩ : ↥K) ∈ normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
      rw [← hQ]
      exact h1
    rw [← Subgroup.subgroupOf_normalizer_eq hUK] at h2
    exact h2
  have hUn : (U.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUK₀).mpr hK₀N
  have hUcop : Nat.Coprime p (Nat.card U) := by
    obtain ⟨m, hm⟩ := hU.isPGroup.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact hSyl U (hU.of_le hUK₀ hK₀K) (le_sSup ⟨hUK₀, hUn, hUcop⟩)

end KPCov

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
