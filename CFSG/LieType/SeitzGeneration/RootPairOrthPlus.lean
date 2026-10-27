module

public import CFSG.LieType.SeitzGeneration.RootPairOrthModel
public import CFSG.LieType.SeitzGeneration.OuterOrthPair
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace RootPairOrth

section Split

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def plusStar (a : Fin (2 * n)) : Fin (2 * n) :=
  plusIndexEquiv n (Sum.swap ((plusIndexEquiv n).symm a))

@[expose] noncomputable def plusSplit : SplitCoord (coordinateQuadPlus n K) where
  star := plusStar n
  star_star a := by simp [plusStar]
  star_ne a h := by
    have h1 : (plusIndexEquiv n) (Sum.swap ((plusIndexEquiv n).symm a)) =
        (plusIndexEquiv n) ((plusIndexEquiv n).symm a) := by
      rw [Equiv.apply_symm_apply]; exact h
    have h2 := (plusIndexEquiv n).injective h1
    generalize (plusIndexEquiv n).symm a = x at h2
    cases x <;> simp at h2
  Q_single a := by
    rw [coordinateQuadPlus_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : plusIndexEquiv n (Sum.inl i) = a
    · have h2 : plusIndexEquiv n (Sum.inr i) ≠ a := fun h2 =>
        Sum.inl_ne_inr ((plusIndexEquiv n).injective (h1.trans h2.symm))
      simp [Pi.single_apply, h2]
    · simp [Pi.single_apply, h1]
  polar_single a w := by
    have hv : (fun i => (Pi.single a 1 : Fin (2 * n) → K) (plusIndexEquiv n i)) =
        Pi.single ((plusIndexEquiv n).symm a) 1 := by
      funext i
      simp [Pi.single_apply, Equiv.eq_symm_apply]
    rw [polar_comm]
    change polar (CFSG.LieType.Universal.Spin.quadPlus n K) (fun i => w (plusIndexEquiv n i))
      (fun i => (Pi.single a 1 : Fin (2 * n) → K) (plusIndexEquiv n i)) = _
    rw [hv]
    unfold plusStar
    generalize (plusIndexEquiv n).symm a = x
    cases x with
    | inl j => rw [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inl]; simp
    | inr j => rw [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inr]; simp

end Split

end RootPairOrth

section Final

open RootPairOrth

theorem orthPairShape_plus_of_odd {K : Type} [Field K] [Finite K]
    (k : Subfield K) {n ℓ e p : ℕ} (hn : 4 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hp : p.Prime) (hp3 : 3 < p) (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) :
    OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  have hp2 : p ≠ 2 := by omega
  have hdeg : Module.finrank k K = p := finrank_subfield_eq k hℓ he hk hK
  have hK' : Nat.card K = Nat.card k ^ p := by rw [hK, hk, ← pow_mul]
  have hk3 : 3 ≤ Nat.card k := by
    rw [hk]
    have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    calc 3 ≤ ℓ := h3
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ e := Nat.pow_le_pow_right hℓ.pos he
  have hchar : ringChar K = ℓ := ringChar_eq_of_card_eq hℓ (Nat.mul_pos he hp.pos) hK
  have h2 : (2 : K) ≠ 0 := by
    rw [Ne, two_eq_zero_iff_ringChar_eq_two (by rw [hchar]; exact hℓ), hchar]
    exact hℓ2
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact orthPair_of_split (plusSplit n K) (coordinateQuadPlus_isExtension k n)
    (commutator_coordinateQuadPlus n K (by omega)).symm (by omega) h2 hp hp2 hdeg hK' hk3
    (fun σ hσo hσk => subfieldSetup_plus k hσk hp hp2 hσo (by omega)) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

@[expose] def SubfieldPairOmegaPlusChar2 : Prop :=
  ∀ (n e p : ℕ), 4 ≤ n → 1 ≤ e → p.Prime → 3 < p →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = 2 ^ e →
      Nat.card K = 2 ^ (e * p) →
        OrthPairShape k (coordinateQuadPlus n k) (coordinateQuadPlus n K)

theorem subfieldPairOmegaPlus_of_char2
    (h : SubfieldPairOmegaPlusChar2) : SubfieldPairOmegaPlus := by
  intro n ℓ e p hn hℓ he hp hp3 _ K _ _ k hk hK
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    exact h n e p hn he hp hp3 K k hk hK
  · exact orthPairShape_plus_of_odd k hn hℓ hℓ2 he hp hp3 hk hK

end Final

end CFSG.LieType.SeitzGeneration
