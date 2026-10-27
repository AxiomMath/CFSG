module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NormalizerGrowth

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open scoped Pointwise

theorem le_of_maximal {G : Type*} [Group G] [Finite G] (M H A U W : Subgroup G)
    (hUW : U ≤ W) (hU2 : IsPGroup 2 U) (hUidx : ¬ 2 ∣ (U.subgroupOf W).index)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hNU : Subgroup.normalizer (U : Set G) ≤ H)
    (hinv : ∀ X : Subgroup G, X ≤ H ⊓ M → IsPGroup 2 X → A ≤ Subgroup.normalizer (X : Set G) →
      X ≤ W)
    (S : Subgroup G) (hSM : S ≤ M) (hS2 : IsPGroup 2 S) (hUS : U ≤ S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) : S ≤ U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hSU
  have hlt : U < S := lt_of_le_of_ne hUS fun h => hSU (h ▸ le_rfl)
  obtain ⟨x, hxS, hxN, hxU⟩ := exists_mem_normalizer_of_lt hS2 hlt
  set K : Subgroup G := Subgroup.normalizer (U : Set G) with hK
  set U₁ : Subgroup G := S ⊓ K with hU₁
  have hUU₁ : U ≤ U₁ := le_inf hUS Subgroup.le_normalizer
  have hU₁2 : IsPGroup 2 U₁ := hS2.to_le inf_le_left
  have hxU₁ : x ∈ U₁ := ⟨hxS, hxN⟩
  have hAU₁ : A ≤ Subgroup.normalizer (U₁ : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := Subgroup.mem_normalizer_iff.mp (hAS ha) g
    have h2 : a ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (hAU ha)
    have h3 := Subgroup.mem_normalizer_iff.mp h2 g
    simp only [hU₁, Subgroup.mem_inf]
    rw [h1, h3]
  have hU₁HM : U₁ ≤ H ⊓ M := le_inf (inf_le_right.trans hNU) (inf_le_left.trans hSM)
  have hU₁W : U₁ ≤ W := hinv U₁ hU₁HM hU₁2 hAU₁
  have hU₁U : U₁ ≤ U := by
    have hsub : U.subgroupOf W ≤ U₁.subgroupOf W := fun y hy => hUU₁ hy
    have hrel := Subgroup.relIndex_mul_index hsub
    have hdvd : (U.subgroupOf W).relIndex (U₁.subgroupOf W) ∣ (U.subgroupOf W).index :=
      ⟨_, hrel.symm⟩
    have hrel2 : (U.subgroupOf W).relIndex (U₁.subgroupOf W) = U.relIndex U₁ :=
      Subgroup.relIndex_subgroupOf hU₁W
    rw [hrel2] at hdvd
    have hodd : ¬ 2 ∣ (U.subgroupOf U₁).index := fun h => hUidx (h.trans hdvd)
    obtain ⟨n, hn⟩ := hU₁2.index (U.subgroupOf U₁)
    have hn0 : n = 0 := by
      by_contra h
      exact hodd (hn ▸ dvd_pow_self 2 h)
    have h1 : (U.subgroupOf U₁).index = 1 := by rw [hn, hn0, pow_zero]
    have htop : U.subgroupOf U₁ = ⊤ := Subgroup.index_eq_one.mp h1
    intro y hy
    have : (⟨y, hy⟩ : ↥U₁) ∈ U.subgroupOf U₁ := by rw [htop]; trivial
    exact this
  exact hxU (hU₁U hxU₁)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
