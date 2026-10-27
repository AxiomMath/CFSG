module

public import CFSG.LieType.SeitzGeneration.RootPairOrthPlucker
public import CFSG.LieType.SeitzGeneration.RootPairOrthPlus

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace RootPairOrth

section Plus

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def plusHyp (hn : 4 ≤ n) : HypCoord (coordinateQuadPlus n K) where
  hyp := Finset.univ
  star := plusStar n
  star_mem _ _ := Finset.mem_univ _
  star_star a _ := (plusSplit n K).star_star a
  star_ne a _ := (plusSplit n K).star_ne a
  Q_single a _ := (plusSplit n K).Q_single a
  polar_single a _ w := (plusSplit n K).polar_single a w
  card_hyp := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega

end Plus

end RootPairOrth

section Final

open RootPairOrth

theorem orthPairShape_plus_char2 {K : Type} [Field K] [Finite K]
    (k : Subfield K) {n e p : ℕ} (hn : 4 ≤ n) (he : 2 ≤ e) (hp : p.Prime) (hp3 : 3 < p)
    (hk : Nat.card k = 2 ^ e) (hK : Nat.card K = 2 ^ (e * p)) :
    OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  have hp2 : p ≠ 2 := by omega
  have hdeg : Module.finrank k K = p := finrank_subfield_eq k Nat.prime_two (by omega) hk hK
  have hK' : Nat.card K = Nat.card k ^ p := by rw [hK, hk, ← pow_mul]
  have hk3 : 3 ≤ Nat.card k := by
    rw [hk]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact orthPair_of_hyp_pl (plusHyp n K hn) (fun _ => Finset.mem_univ _)
    (coordinateQuadPlus_isExtension k n) (commutator_coordinateQuadPlus n K (by omega)).symm
    (regular_coordinateQuadPlus n K (by omega)).1 hp hp2 hdeg hK' hk3
    (fun σ hσo hσk => subfieldSetup_plus k hσk hp hp2 hσo (by omega)) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

@[expose] def SubfieldPairOmegaPlusF2 : Prop :=
  ∀ (n p : ℕ), 4 ≤ n → p.Prime → 3 < p →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = 2 →
      Nat.card K = 2 ^ p →
        OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K)

theorem subfieldPairOmegaPlusChar2_of_F2
    (h : SubfieldPairOmegaPlusF2) : SubfieldPairOmegaPlusChar2 := by
  intro n e p hn he hp hp3 K _ _ k hk hK
  by_cases he1 : e = 1
  · subst he1
    exact h n p hn hp hp3 K k (by simpa using hk) (by simpa using hK)
  · exact orthPairShape_plus_char2 k hn (by omega) hp hp3 hk hK

end Final

end CFSG.LieType.SeitzGeneration
