module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Plus
public import CFSG.LieType.SeitzGeneration.OmegaF2.Minus
public import CFSG.LieType.SeitzGeneration.RootPairOrthOdd

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin
open RootPairOrth

section Odd

variable {K : Type} [Field K] [Finite K]

private theorem degree_data {ℓ e p : ℕ} (k : Subfield K) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hp : p.Prime) (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) :
    Module.finrank k K = p ∧ Nat.card K = Nat.card k ^ p ∧ 3 ≤ Nat.card k ∧ (2 : K) ≠ 0 := by
  refine ⟨finrank_subfield_eq k hℓ he hk hK, by rw [hK, hk, ← pow_mul], ?_, ?_⟩
  · rw [hk]
    have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    calc 3 ≤ ℓ := h3
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ e := Nat.pow_le_pow_right hℓ.pos he
  · have hchar : ringChar K = ℓ := ringChar_eq_of_card_eq hℓ (Nat.mul_pos he hp.pos) hK
    rw [Ne, two_eq_zero_iff_ringChar_eq_two (by rw [hchar]; exact hℓ), hchar]
    exact hℓ2

theorem orthPairShape_odd_of_ne_two
    (k : Subfield K) {n ℓ e p : ℕ} (hn : 3 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) :
    OrthPairShape k (coordinateQuadOdd n k) (coordinateQuadOdd n K) := by
  obtain ⟨hdeg, hK', hk3, h2⟩ := degree_data k hℓ hℓ2 he hp hk hK
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact orthPair_of_hypCoord (oddCoord n K hn) (coordinateQuadOdd_isExtension k n)
    (commutator_coordinateQuadOdd n K h2 hn).symm (regular_coordinateQuadOdd n K h2 hn).1 h2
    (oddTailPairs n K hn k) hp hp2 hdeg hK' hk3
    (fun σ hσo hσk => subfieldSetup_odd k hσk hp hp2 hσo hn h2) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

theorem orthPairShape_plus_of_ne_two
    (k : Subfield K) {n ℓ e p : ℕ} (hn : 4 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) :
    OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  obtain ⟨hdeg, hK', hk3, h2⟩ := degree_data k hℓ hℓ2 he hp hk hK
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact orthPair_of_split (plusSplit n K) (coordinateQuadPlus_isExtension k n)
    (commutator_coordinateQuadPlus n K (by omega)).symm (by omega) h2 hp hp2 hdeg hK' hk3
    (fun σ hσo hσk => subfieldSetup_plus k hσk hp hp2 hσo (by omega)) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

theorem orthPairShape_minus_of_ne_two
    (k : Subfield K) {n ℓ e p : ℕ} (hn : 4 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p))
    (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
      (coordinateQuadMinus n K (by omega) (b : K) (c : K)) := by
  obtain ⟨hdeg, hK', hk3, h2⟩ := degree_data k hℓ hℓ2 he hp hk hK
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 hdeg b c hirr
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact orthPair_of_hypCoord_M (minusCoord n K (b : K) (c : K) hn)
    (coordinateQuadMinus_isExtension k n (by omega) b c)
    (commutator_coordinateQuadMinus n K (b : K) (c : K) hn hirrK).symm
    (regular_coordinateQuadMinus n K (b : K) (c : K) hn hirrK).1 h2
    (minusCoord_Q_tail n K (b : K) (c : K) hn hirrK) hp hp2 hdeg hK' hk3
    (fun σ hσo hσk => subfieldSetup_minus k hσk hp hp2 hσo hn hdeg b c hirr) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

end Odd

section Char2

variable {K : Type} [Field K] [Finite K]

private theorem degree_data_two {e p : ℕ} (k : Subfield K) (he : 2 ≤ e) (hp : p.Prime)
    (hk : Nat.card k = 2 ^ e) (hK : Nat.card K = 2 ^ (e * p)) :
    Module.finrank k K = p ∧ Nat.card K = Nat.card k ^ p ∧ 3 ≤ Nat.card k := by
  refine ⟨finrank_subfield_eq k Nat.prime_two (by omega) hk hK, by rw [hK, hk, ← pow_mul], ?_⟩
  rw [hk]
  calc 3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he

theorem orthPairShape_plus_char2_of_ne_two
    (k : Subfield K) {n e p : ℕ} (hn : 4 ≤ n) (he : 2 ≤ e) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : Nat.card k = 2 ^ e) (hK : Nat.card K = 2 ^ (e * p)) :
    OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  obtain ⟨hdeg, hK', hk3⟩ := degree_data_two k he hp hk hK
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact orthPair_of_hyp_pl (plusHyp n K hn) (fun _ => Finset.mem_univ _)
    (coordinateQuadPlus_isExtension k n) (commutator_coordinateQuadPlus n K (by omega)).symm
    (regular_coordinateQuadPlus n K (by omega)).1 hp hp2 hdeg hK' hk3
    (fun σ hσo hσk => subfieldSetup_plus k hσk hp hp2 hσo (by omega)) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

theorem orthPairShape_minus_char2_of_ne_two
    (k : Subfield K) {n e p : ℕ} (hn : 4 ≤ n) (he : 2 ≤ e) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : Nat.card k = 2 ^ e) (hK : Nat.card K = 2 ^ (e * p)) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
      (coordinateQuadMinus n K (by omega) (b : K) (c : K)) := by
  obtain ⟨hdeg, hK', hk3⟩ := degree_data_two k he hp hk hK
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

end Char2

section F2

variable {K : Type} [Field K] [Finite K]

theorem orthPairShape_plus_F2_of_ne_two
    (k : Subfield K) {n p : ℕ} (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ p) :
    OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  haveI : CharP K 2 := OmegaF2.charP_two_of_subfield_card_two hk
  have hk1 : Nat.card k = 2 ^ 1 := by simpa using hk
  have hK1 : Nat.card K = 2 ^ (1 * p) := by simpa using hK
  have hdeg : Module.finrank k K = p := finrank_subfield_eq k Nat.prime_two (by omega) hk1 hK1
  have hK' : Nat.card K = Nat.card k ^ p := by rw [hK, hk]
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact OmegaF2.orthPair_of_hypCoord_F2 (plusHyp n K hn) (OmegaF2.tailAnisotropic_plus n K hn) hk
    (coordinateQuadPlus_isExtension k n) (commutator_coordinateQuadPlus n K (by omega)).symm
    (regular_coordinateQuadPlus n K (by omega)).1 hp hp2 hdeg hK'
    (fun σ hσo hσk => subfieldSetup_plus k hσk hp hp2 hσo (by omega)) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

theorem orthPairShape_minus_F2_of_ne_two
    (k : Subfield K) {n p : ℕ} (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ p) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
      (coordinateQuadMinus n K (by omega) (b : K) (c : K)) := by
  haveI : CharP K 2 := OmegaF2.charP_two_of_subfield_card_two hk
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

end F2

@[expose] def SubfieldPairOmegaOddThree : Prop :=
  ∀ (n ℓ e : ℕ), 3 ≤ n → ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ e →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * 3) →
        OrthPairShape k (coordinateQuadOdd n k) (coordinateQuadOdd n K)

@[expose] def SubfieldPairOmegaPlusThree : Prop :=
  ∀ (n ℓ e : ℕ), 4 ≤ n → ℓ.Prime → ℓ ≠ 3 → 1 ≤ e →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * 3) →
        OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K)

@[expose] def SubfieldPairOmegaMinusThree : Prop :=
  ∀ (n ℓ e : ℕ) (hn : 4 ≤ n), ℓ.Prime → ℓ ≠ 3 → 1 ≤ e →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * 3) → ∀ b c : k, (∀ s : k, s ^ 2 + b * s + c ≠ 0) →
        OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
          (coordinateQuadMinus n K (by omega) (b : K) (c : K))

@[expose] def SubfieldPairOmegaThree : Prop :=
  SubfieldPairOmegaOddThree ∧ SubfieldPairOmegaPlusThree ∧ SubfieldPairOmegaMinusThree

theorem subfieldPairOmegaPlusF2Three_holds :
    ∀ (n : ℕ), 4 ≤ n →
      ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = 2 →
        Nat.card K = 2 ^ 3 →
          OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  intro n hn K _ _ k hk hK
  exact orthPairShape_plus_F2_of_ne_two k hn Nat.prime_three (by norm_num) hk hK

theorem subfieldPairOmegaMinusF2Three_holds :
    ∀ (n : ℕ) (hn : 4 ≤ n),
      ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = 2 →
        Nat.card K = 2 ^ 3 → ∀ b c : k, (∀ s : k, s ^ 2 + b * s + c ≠ 0) →
          OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
            (coordinateQuadMinus n K (by omega) (b : K) (c : K)) := by
  intro n hn K _ _ k hk hK b c hirr
  exact orthPairShape_minus_F2_of_ne_two k hn Nat.prime_three (by norm_num) hk hK b c hirr

theorem subfieldPairOmegaThree_of_F2
    :
    SubfieldPairOmegaThree := by
  have hP := subfieldPairOmegaPlusF2Three_holds
  have hM := subfieldPairOmegaMinusF2Three_holds
  refine ⟨?_, ?_, ?_⟩
  · intro n ℓ e hn hℓ hℓ2 _ he K _ _ k hk hK
    exact orthPairShape_odd_of_ne_two k hn hℓ hℓ2 he Nat.prime_three (by norm_num) hk hK
  · intro n ℓ e hn hℓ _ he K _ _ k hk hK
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      by_cases he1 : e = 1
      · subst he1
        exact hP n hn K k (by simpa using hk) (by simpa using hK)
      · exact orthPairShape_plus_char2_of_ne_two k hn (by omega) Nat.prime_three (by norm_num)
          hk hK
    · exact orthPairShape_plus_of_ne_two k hn hℓ hℓ2 he Nat.prime_three (by norm_num) hk hK
  · intro n ℓ e hn hℓ _ he K _ _ k hk hK b c hirr
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      by_cases he1 : e = 1
      · subst he1
        exact hM n hn K k (by simpa using hk) (by simpa using hK) b c hirr
      · exact orthPairShape_minus_char2_of_ne_two k hn (by omega) Nat.prime_three (by norm_num)
          hk hK b c hirr
    · exact orthPairShape_minus_of_ne_two k hn hℓ hℓ2 he Nat.prime_three (by norm_num) hk hK b c
        hirr

theorem subfieldPairOmegaThree_holds : SubfieldPairOmegaThree :=
  subfieldPairOmegaThree_of_F2

end CFSG.LieType.SeitzGeneration
