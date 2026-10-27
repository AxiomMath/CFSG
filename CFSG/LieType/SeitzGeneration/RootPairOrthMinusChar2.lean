module

public import CFSG.LieType.SeitzGeneration.RootPairOrthTail3
public import CFSG.LieType.SeitzGeneration.RootPairOrthMinus

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin

section Final

open RootPairOrth

theorem orthPairShape_minus_char2 {K : Type} [Field K] [Finite K]
    (k : Subfield K) {n e p : ℕ} (hn : 4 ≤ n) (he : 2 ≤ e) (hp : p.Prime) (hp3 : 3 < p)
    (hk : Nat.card k = 2 ^ e) (hK : Nat.card K = 2 ^ (e * p)) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
      (coordinateQuadMinus n K (by omega) (b : K) (c : K)) := by
  have hp2 : p ≠ 2 := by omega
  have hdeg : Module.finrank k K = p := finrank_subfield_eq k Nat.prime_two (by omega) hk hK
  have hK' : Nat.card K = Nat.card k ^ p := by rw [hK, hk, ← pow_mul]
  have hk3 : 3 ≤ Nat.card k := by
    rw [hk]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 hdeg b c hirr
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact orthPair_of_hypCoord_M3 (minusCoord n K (b : K) (c : K) hn)
    (coordinateQuadMinus_isExtension k n (by omega) b c)
    (commutator_coordinateQuadMinus n K (b : K) (c : K) hn hirrK).symm
    (regular_coordinateQuadMinus n K (b : K) (c : K) hn hirrK).1 hp hp2 hdeg hK' hk3
    (fun σ hσo hσk => subfieldSetup_minus k hσk hp hp2 hσo hn hdeg b c hirr) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

@[expose] def SubfieldPairOmegaMinusF2 : Prop :=
  ∀ (n p : ℕ) (hn : 4 ≤ n), p.Prime → 3 < p →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = 2 →
      Nat.card K = 2 ^ p → ∀ b c : k, (∀ s : k, s ^ 2 + b * s + c ≠ 0) →
        OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
          (coordinateQuadMinus n K (by omega) (b : K) (c : K))

theorem subfieldPairOmegaMinusChar2_of_F2
    (h : SubfieldPairOmegaMinusF2) : SubfieldPairOmegaMinusChar2 := by
  intro n e p hn he hp hp3 K _ _ k hk hK b c hirr
  by_cases he1 : e = 1
  · subst he1
    exact h n p hn hp hp3 K k (by simpa using hk) (by simpa using hK) b c hirr
  · exact orthPairShape_minus_char2 k hn (by omega) hp hp3 hk hK b c hirr

end Final

end CFSG.LieType.SeitzGeneration
