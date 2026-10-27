module

public import CFSG.LieType.SeitzGeneration.RootPairOrthTail2
public import CFSG.LieType.SeitzGeneration.OuterOrthPair
public import CFSG.LieType.SeitzGeneration.RootPairOrthTailInst
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin

namespace RootPairOrth

section Minus

variable (n : ℕ) (K : Type) [Field K] (b c : K)

theorem quadMinus_hyp (x : Fin (n - 1) ⊕ Fin (n - 1)) :
    quadMinus n K b c (Pi.single (hypEmb (T := Fin 2) x) 1) = 0 := by
  rw [quadMinus_apply]
  rcases x with i | i
  · simp [hypEmb, Pi.single_apply]
  · simp [hypEmb, Pi.single_apply]

theorem polar_quadMinus_hyp (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (x : Fin (n - 1) ⊕ Fin (n - 1)) :
    polar (quadMinus n K b c) v (Pi.single (hypEmb (T := Fin 2) x) 1) = v (hypEmb x.swap) := by
  rcases x with i | i
  · exact polar_quadMinus_single_inl n K b c v i
  · exact polar_quadMinus_single_inr_inl n K b c v i

@[expose] noncomputable def minusCoord (hn : 4 ≤ n) :
    HypCoord (coordinateQuadMinus n K (by omega) b c) :=
  tailCoord (minusIndexEquiv n (by omega)) (quadMinus n K b c) (quadMinus_hyp n K b c)
    (polar_quadMinus_hyp n K b c) (by omega)

theorem minusCoord_tail (hn : 4 ≤ n) {t : Fin (2 * n)} (ht : t ∉ (minusCoord n K b c hn).hyp) :
    t = minusIndexEquiv n (by omega) (Sum.inr (Sum.inr 0)) ∨
      t = minusIndexEquiv n (by omega) (Sum.inr (Sum.inr 1)) := by
  obtain ⟨x, rfl⟩ := (minusIndexEquiv n (by omega)).surjective t
  rcases x with i | i | u
  · exact absurd ((mem_tailCoord_hyp _ _ _ _ _).mpr ⟨Sum.inl i, rfl⟩) ht
  · exact absurd ((mem_tailCoord_hyp _ _ _ _ _).mpr ⟨Sum.inr i, rfl⟩) ht
  · fin_cases u <;> simp

theorem minusCoord_Q_tail (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ t, t ∉ (minusCoord n K b c hn).hyp →
      coordinateQuadMinus n K (by omega) b c (Pi.single t 1) ≠ 0 := by
  intro t ht
  rcases minusCoord_tail n K b c hn ht with rfl | rfl
  · rw [coordinateQuadMinus_apply]
    simp
  · rw [coordinateQuadMinus_apply]
    simpa [Pi.single_apply] using fun h => hirr 0 (by simpa using h)

end Minus

end RootPairOrth

section Final

open RootPairOrth

theorem orthPairShape_minus {K : Type} [Field K] [Finite K]
    (k : Subfield K) {n ℓ e p : ℕ} (hn : 4 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hp : p.Prime) (hp3 : 3 < p) (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p))
    (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
      (coordinateQuadMinus n K (by omega) (b : K) (c : K)) := by
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

@[expose] def SubfieldPairOmegaMinusChar2 : Prop :=
  ∀ (n e p : ℕ) (hn : 4 ≤ n), 1 ≤ e → p.Prime → 3 < p →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = 2 ^ e →
      Nat.card K = 2 ^ (e * p) → ∀ b c : k, (∀ s : k, s ^ 2 + b * s + c ≠ 0) →
        OrthPairShape k (coordinateQuadMinus n k (by omega) b c)
          (coordinateQuadMinus n K (by omega) (b : K) (c : K))

theorem subfieldPairOmegaMinus_of_char2
    (h : SubfieldPairOmegaMinusChar2) : SubfieldPairOmegaMinus := by
  intro n ℓ e p hn hℓ he hp hp3 _ K _ _ k hk hK b c hirr
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    exact h n e p hn he hp hp3 K k hk hK b c hirr
  · exact orthPairShape_minus k hn hℓ hℓ2 he hp hp3 hk hK b c hirr

end Final

end CFSG.LieType.SeitzGeneration
