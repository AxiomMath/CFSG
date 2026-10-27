module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Engine
public import CFSG.LieType.SeitzGeneration.RootPairOrthMinusChar2

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin
open RootPairOrth

private theorem minusTail_eq_zero_of_rootFree {K : Type} [Field K] (b c x y : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hQ : x ^ 2 + b * x * y + c * y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    have hx2 : x ^ 2 = 0 := by linear_combination hQ
    exact ⟨(pow_eq_zero_iff two_ne_zero).mp hx2, rfl⟩
  · obtain ⟨s, rfl⟩ : ∃ s, x = s * y := ⟨x / y, (div_mul_cancel₀ x hy).symm⟩
    have h1 : y ^ 2 * (s ^ 2 + b * s + c) = 0 := by linear_combination hQ
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hy
    · exact absurd h (hirr s)

theorem OmegaF2.tailAnisotropic_minus (n : ℕ) (K : Type) [Field K] (b c : K) (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OmegaF2.TailAnisotropic (minusCoord n K b c hn) := by
  intro v hv hQ
  have hsupp : ∀ a : Fin (2 * n), a ≠ minusIndexEquiv n (by omega) (Sum.inr (Sum.inr 0)) →
      a ≠ minusIndexEquiv n (by omega) (Sum.inr (Sum.inr 1)) → v a = 0 := by
    intro a h0 h1
    apply hv a
    by_contra hmem
    rcases minusCoord_tail n K b c hn hmem with h | h
    · exact h0 h
    · exact h1 h
  have hsum : ∑ i : Fin (n - 1), v (minusIndexEquiv n (by omega) (Sum.inl i)) *
      v (minusIndexEquiv n (by omega) (Sum.inr (Sum.inl i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : v (minusIndexEquiv n (by omega) (Sum.inl i)) = 0 :=
      hv _ ((mem_tailCoord_hyp _ _ _ _ _).mpr ⟨Sum.inl i, rfl⟩)
    rw [hi, zero_mul]
  rw [coordinateQuadMinus_apply, hsum, zero_add] at hQ
  obtain ⟨h0, h1⟩ := minusTail_eq_zero_of_rootFree b c _ _ hirr hQ
  funext a
  by_cases ha0 : a = minusIndexEquiv n (by omega) (Sum.inr (Sum.inr 0))
  · rw [ha0]
    exact h0
  · by_cases ha1 : a = minusIndexEquiv n (by omega) (Sum.inr (Sum.inr 1))
    · rw [ha1]
      exact h1
    · exact hsupp a ha0 ha1

theorem subfieldPairOmegaMinusF2_holds :
    SubfieldPairOmegaMinusF2 := by
  intro n p hn hp hp3 K _ _ k hk hK b c hirr
  haveI : CharP K 2 := OmegaF2.charP_two_of_subfield_card_two hk
  have hp2 : p ≠ 2 := by omega
  have hk1 : Nat.card k = 2 ^ 1 := by simpa using hk
  have hK1 : Nat.card K = 2 ^ (1 * p) := by simpa using hK
  have hdeg : Module.finrank k K = p := finrank_subfield_eq k Nat.prime_two (by omega) hk1 hK1
  have hK' : Nat.card K = Nat.card k ^ p := by rw [hK, hk]
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 hdeg b c hirr
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact OmegaF2.orthPair_of_hypCoord_F2 (minusCoord n K (b : K) (c : K) hn)
    (OmegaF2.tailAnisotropic_minus n K (b : K) (c : K) hn hirrK) hk
    (coordinateQuadMinus_isExtension k n (by omega) b c)
    (commutator_coordinateQuadMinus n K (b : K) (c : K) hn hirrK).symm
    (regular_coordinateQuadMinus n K (b : K) (c : K) hn hirrK).1 hp hp2 hdeg hK'
    (fun σ hσo hσk => subfieldSetup_minus k hσk hp hp2 hσo hn hdeg b c hirr) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

end CFSG.LieType.SeitzGeneration
