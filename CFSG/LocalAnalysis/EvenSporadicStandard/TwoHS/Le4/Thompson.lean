module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.ThompsonIndexTwo

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_index_two_of_thompson_pow {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T)
    (hxU : x ∉ U)
    (hpow : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ T → g⁻¹ * x ^ (2 * k) * g ∈ U)
    (hconj : ∀ g : G, g⁻¹ * x * g ∉ U) : ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hQn : ∀ t ∈ T, ∀ q ∈ U, t * q * t⁻¹ ∈ U := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hUT hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ U := by
    refine ⟨x, hxT, fun t ht => ?_⟩
    by_cases htU : t ∈ U
    · exact ⟨0, by simpa using htU⟩
    · exact ⟨1, by simpa using inv_mul_mem_of_not_mem hUidx hxT ht hxU htU⟩
  have hc : ∀ g : G, g⁻¹ * x * g ∈ T → IsExtremalIn 2 T (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ U ∨ x⁻¹ * (g⁻¹ * x * g) ∈ U := by
    intro g hgT _
    by_cases hgU : g⁻¹ * x * g ∈ U
    · exact Or.inl hgU
    · exact Or.inr (inv_mul_mem_of_not_mem hUidx hxT hgT hxU hgU)
  rcases thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc hxT hxU hpow hc with
    ⟨N, hN, -, hNp, hxN⟩ | ⟨g, hg, -, -⟩
  · have := hN
    have : Group.IsNilpotent (G ⧸ N) := hNp.isNilpotent
    have hbt : (⊥ : Subgroup (G ⧸ N)) ≠ ⊤ := by
      intro h
      apply hxN
      have h1 : (QuotientGroup.mk x : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 h1)
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ N))).resolve_left hbt
    have hMidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hNp).1 hM
    refine ⟨M.comap (QuotientGroup.mk' N), (Subgroup.normal_of_index_eq_two hMidx).comap _, ?_⟩
    exact (Subgroup.index_comap_of_surjective M (f := QuotientGroup.mk' N)
      QuotientGroup.mk_surjective).trans hMidx
  · exact absurd hg (hconj g)

theorem false_of_thompson_pow [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {T U : Subgroup G} (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T)
    (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T) (hxU : x ∉ U)
    (hpow : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ T → g⁻¹ * x ^ (2 * k) * g ∈ U)
    (hconj : ∀ g : G, g⁻¹ * x * g ∉ U) : False :=
  not_exists_normal_index_two_of_nonabelian hnonab
    (exists_normal_index_two_of_thompson_pow hT hTidx hUT hUidx hxT hxU hpow hconj)

end CFSG.EvenSporadicStandard.TwoHS
