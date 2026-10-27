module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Sylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {u : J}

theorem partCSylow_maxInNormalizer (T : Sylow 2 (quasiNormalizer u)) :
    CaseC3.MaxInNormalizer (partCSylow T) u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n hnX hnT ⟨k, hk⟩
  set n₀ : quasiNormalizer u := ⟨n, hnX⟩
  have hn₀ : n₀ ∈ Subgroup.normalizer ((T : Subgroup (quasiNormalizer u)) : Set _) := by
    refine mem_normalizer_of_conj_mem fun t ht => ?_
    obtain ⟨t', ht', ht'e⟩ := Subgroup.mem_map.mp
      ((Subgroup.mem_normalizer_iff.mp hnT _).mp (Subgroup.mem_map_of_mem _ ht))
    rw [show n₀ * t * n₀⁻¹ = t' from Subtype.ext ht'e.symm]
    exact ht'
  have hz2 : IsPGroup 2 (Subgroup.zpowers n₀) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (show n₀ ^ 2 ^ k = 1 from Subtype.ext (by simpa using hk)))
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hsup := IsPGroup.to_sup_of_normal_left' T.isPGroup' hz2
    (Subgroup.zpowers_le.mpr hn₀)
  have heq := T.is_maximal' hsup le_sup_left
  have hmem : n₀ ∈ (T : Subgroup (quasiNormalizer u)) := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n₀)
  exact Subgroup.mem_map_of_mem _ hmem

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
