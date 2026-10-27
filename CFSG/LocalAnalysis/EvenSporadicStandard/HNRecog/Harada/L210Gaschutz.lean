module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup
open scoped Pointwise

private lemma card_sup_of_normal_inf_eq_bot {G : Type*} [Group G] {K D : Subgroup G} [K.Normal]
    (hKD : K ⊓ D = ⊥) : Nat.card ↥(K ⊔ D) = Nat.card K * Nat.card D := by
  have hKD' : K.subgroupOf (K ⊔ D) ⊓ D.subgroupOf (K ⊔ D) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have hxK : (x : G) ∈ K := hx.1
    have hxD : (x : G) ∈ D := hx.2
    have hxbot : (x : G) ∈ K ⊓ D := ⟨hxK, hxD⟩
    rw [hKD, Subgroup.mem_bot] at hxbot
    exact Subtype.ext hxbot
  have hmul : (↑(K.subgroupOf (K ⊔ D)) : Set ↥(K ⊔ D)) *
      (↑(D.subgroupOf (K ⊔ D)) : Set ↥(K ⊔ D)) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    have hx : (x : G) ∈ (K : Set G) * D := by
      rw [← Subgroup.normal_mul K D]; exact x.2
    obtain ⟨k, hkK, d, hdD, hkd⟩ := Set.mem_mul.mp hx
    refine Set.mem_mul.mpr
      ⟨⟨k, Subgroup.mem_sup_left hkK⟩, ?_, ⟨d, Subgroup.mem_sup_right hdD⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hkK
    · exact Subgroup.mem_subgroupOf.mpr hdD
    · exact Subtype.ext hkd
  have hcompl : (K.subgroupOf (K ⊔ D)).IsComplement' (D.subgroupOf (K ⊔ D)) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hKD') hmul
  have hcard := hcompl.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at hcard
  exact hcard.symm

theorem exists_complement_of_two_sylow_complement {Γ : Type*} [Group Γ] [Finite Γ]
    {K D : Subgroup Γ} [K.Normal] [IsMulCommutative K] (hK : IsPGroup 2 K) (hD : IsPGroup 2 D)
    (hKD : K ⊓ D = ⊥)
    (hcard : Nat.card K * Nat.card D = 2 ^ (Nat.card Γ).factorization 2) :
    ∃ C : Subgroup Γ, K ⊓ C = ⊥ ∧ K ⊔ C = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard_sup : Nat.card ↥(K ⊔ D) = 2 ^ (Nat.card Γ).factorization 2 :=
    (card_sup_of_normal_inf_eq_bot hKD).trans hcard
  let P : Sylow 2 Γ := Sylow.ofCard (K ⊔ D) hcard_sup
  obtain ⟨C, h1, h2⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement
      Nat.prime_two hK P (by rw [Sylow.coe_ofCard]; exact le_sup_left) hKD
      (by rw [Sylow.coe_ofCard])
  exact ⟨C, h1, h2⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
