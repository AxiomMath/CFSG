module

public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LieType.SeitzGeneration.OuterQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.SylowM27

open Subgroup CFSG.ABGLocalTools CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Suzuki


variable {X : Type} [Group X] [Finite X]

theorem false_of_card_inf_eq_one {K Q : Subgroup X} [hKn : K.Normal] (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hKcat : IsCatalogGroup K)
    (hKc : Subgroup.centralizer (K : Set X) = ⊥) (hsyl : IsSylowOf 3 (Q ⊓ K) K)
    (hQ : Nat.card Q = 3 ^ 3) (hQnab : ¬ IsMulCommutative Q) (hD : Nat.card ↥(Q ⊓ K) = 1) :
    False := by
  have h3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    have hcard := hsyl.card_eq
    rw [hD] at hcard
    have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3
    have h2 : 3 ^ 1 ≤ 3 ^ (Nat.card K).factorization 3 := Nat.pow_le_pow_right (by norm_num) h1
    rw [← hcard] at h2
    norm_num at h2
  have : IsSimpleGroup K := hKs
  obtain ⟨f, hf⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd K hKnab hKcat h3
  have hcyc : IsCyclic (Outer K) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} K 2 f hf).1.1
  have hinj : Function.Injective (MulAut.conjNormal (H := K)) := by
    refine (MonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff.mpr fun g hg => ?_)
    have hgc : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : MulAut.conjNormal g (⟨k, hk⟩ : K) = ⟨k, hk⟩ := by
        rw [MonoidHom.mem_ker.mp hg]
        rfl
      have h2 : g * k * g⁻¹ = k := by
        have := congrArg Subtype.val h1
        rwa [MulAut.conjNormal_apply] at this
      calc k * g = g * k * g⁻¹ * g := by rw [h2]
        _ = g * k := by group
    rw [hKc] at hgc
    exact hgc
  set E : Subgroup (MulAut K) := Q.map (MulAut.conjNormal (H := K)) with hE
  have hEcard : Nat.card E = 3 ^ 3 := by rw [hE, Subgroup.card_map_of_injective hinj, hQ]
  have hcop : Nat.Coprime (Nat.card E) (Nat.card K) := by
    rw [hEcard]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  obtain ⟨ψ, hψ⟩ := CFSG.LieType.SeitzGeneration.injective_outer_of_coprime_card hcop
  have hEcyc : IsCyclic E := isCyclic_of_injective ψ hψ
  have hQcyc : IsCyclic Q := (Q.equivMapOfInjective _ hinj).isCyclic.mpr hEcyc
  exact hQnab inferInstance

end Suzuki

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.SylowM27
