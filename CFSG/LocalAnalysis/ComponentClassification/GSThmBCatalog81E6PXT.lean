module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PSp

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer P211

variable {X : Type} [Group X]

theorem exists_derivedSeries_le_of_isSolvable {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hs : Group.IsSolvable (H ⧸ N)) : ∃ n, derivedSeries H n ≤ N := by
  obtain ⟨n, hn⟩ := hs.solvable
  refine ⟨n, fun x hx => ?_⟩
  have h1 : (QuotientGroup.mk' N) x ∈ derivedSeries (H ⧸ N) n := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective N)]
    exact mem_map_of_mem _ hx
  rw [hn, mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).mp h1

theorem p211_two_adic [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {J D : Subgroup X} (hJt : IsSec8JType (J ⧸ pPrimeCore 2 J) p f) (hDJ : D ≤ J)
    (hDsyl : ∃ R : Sylow 2 ↥J, (R : Subgroup ↥J) = D.subgroupOf J)
    (hbound : ∀ R : Subgroup X, R ≤ generalizedFitting X → IsPGroup 2 R →
      Nat.card R ≤ 2 * Nat.card D ^ 2)
    {K : Subgroup X} (hKt : IsSec8Socle (K ⧸ pPrimeCore 2 K) p f) :
    3 ≤ padicValNat 2 ((p ^ f) ^ 2 - 1) ∧
      padicValNat 2 (Nat.card (K ⧸ pPrimeCore 2 K)) = 2 * padicValNat 2 ((p ^ f) ^ 2 - 1) ∧
      padicValNat 2 (Nat.card (generalizedFitting X)) ≤
        2 * padicValNat 2 ((p ^ f) ^ 2 - 1) + 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  set m := padicValNat 2 ((p ^ f) ^ 2 - 1) with hm
  have hD : Nat.card D = 2 ^ m := by
    obtain ⟨R, hR⟩ := hDsyl
    have h1 := R.card_eq_multiplicity
    rw [hR, Nat.factorization_def _ Nat.prime_two, v2_card_quot, card_sec8J hJt,
      show p ^ (2 * f) = (p ^ f) ^ 2 by ring, v2_ordA hqodd hq3] at h1
    rw [← h1]
    exact (Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv).symm
  refine ⟨three_le_v2 hqodd hq3, ?_, ?_⟩
  · rcases hKt with hL | ⟨rfl, rfl, ⟨eA⟩⟩
    · rw [GH74.card_of_lieModel_PSp (by norm_num) hp2 hL, v2_ordBC hqodd hq3]
    · rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hm,
        show (3 ^ 1) ^ 2 - 1 = 2 ^ 3 by norm_num, padicValNat.prime_pow,
        show Nat.factorial 8 / 2 = 2 ^ 6 * 315 by decide,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
      have h315 : padicValNat 2 315 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
      rw [h315]
  · obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(generalizedFitting X)) := inferInstance
    have hT := T.card_eq_multiplicity
    rw [Nat.factorization_def _ Nat.prime_two] at hT
    have hb2 := hbound ((T : Subgroup ↥(generalizedFitting X)).map
      (generalizedFitting X).subtype) (map_subtype_le _) (T.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective (generalizedFitting X).subtype_injective, hT, hD,
      ← pow_mul 2 m 2, ← pow_succ'] at hb2
    have := (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp hb2
    omega

theorem pow_dvd_card_of_v2 [Finite X] {K : Subgroup X} {v : ℕ}
    (hv : padicValNat 2 (Nat.card (K ⧸ pPrimeCore 2 K)) = v) : 2 ^ v ∣ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hv]
  exact pow_padicValNat_dvd.trans (Subgroup.card_quotient_dvd_card _)

end P211X

end CFSG.ComponentClassification.GSThmB
