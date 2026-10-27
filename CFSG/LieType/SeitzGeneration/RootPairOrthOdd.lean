module

public import CFSG.LieType.SeitzGeneration.RootPairOrthTailInst
public import CFSG.LieType.SeitzGeneration.OuterOrthPair
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin

namespace RootPairOrth

section Odd

variable (n : ℕ) (K : Type) [Field K]

theorem quadOdd_hyp (x : Fin n ⊕ Fin n) :
    quadOdd n K (Pi.single (hypEmb (T := Unit) x) 1) = 0 := by
  rw [quadOdd_apply]
  rcases x with i | i
  · simp [hypEmb, Pi.single_apply]
  · simp [hypEmb, Pi.single_apply]

theorem polar_quadOdd_hyp (v : Fin n ⊕ Fin n ⊕ Unit → K) (x : Fin n ⊕ Fin n) :
    polar (quadOdd n K) v (Pi.single (hypEmb (T := Unit) x) 1) = v (hypEmb x.swap) := by
  rcases x with i | i
  · exact polar_quadOdd_single_inl n K v i
  · exact polar_quadOdd_single_inr_inl n K v i

@[expose] noncomputable def oddCoord (hn : 3 ≤ n) : HypCoord (coordinateQuadOdd n K) :=
  tailCoord (oddIndexEquiv n) (quadOdd n K) (quadOdd_hyp n K) (polar_quadOdd_hyp n K) hn

theorem oddCoord_tail (hn : 3 ≤ n) {t : Fin (2 * n + 1)} (ht : t ∉ (oddCoord n K hn).hyp) :
    t = oddIndexEquiv n (Sum.inr (Sum.inr ())) := by
  obtain ⟨x, rfl⟩ := (oddIndexEquiv n).surjective t
  rcases x with i | i | u
  · exact absurd ((mem_tailCoord_hyp _ _ _ _ _).mpr ⟨Sum.inl i, rfl⟩) ht
  · exact absurd ((mem_tailCoord_hyp _ _ _ _ _).mpr ⟨Sum.inr i, rfl⟩) ht
  · rfl

theorem oddTailPairs (hn : 3 ≤ n) (k : Subfield K) : TailPairs (oddCoord n K hn) k := by
  intro g' μ' x₀ y₀ _ t t' ht ht'
  rw [oddCoord_tail n K hn ht, oddCoord_tail n K hn ht', phi_self_left]
  exact k.zero_mem

end Odd

end RootPairOrth

section Final

open RootPairOrth

theorem orthPairShape_odd {K : Type} [Field K] [Finite K]
    (k : Subfield K) {n ℓ e p : ℕ} (hn : 3 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hp : p.Prime) (hp3 : 3 < p) (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) :
    OrthPairShape k (coordinateQuadOdd n k) (coordinateQuadOdd n K) := by
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
  exact orthPair_of_hypCoord (oddCoord n K hn) (coordinateQuadOdd_isExtension k n)
    (commutator_coordinateQuadOdd n K h2 hn).symm (regular_coordinateQuadOdd n K h2 hn).1 h2
    (oddTailPairs n K hn k) hp hp2 hdeg hK' hk3
    (fun σ hσo hσk => subfieldSetup_odd k hσk hp hp2 hσo hn h2) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

theorem subfieldPairOmegaOdd : SubfieldPairOmegaOdd := by
  intro n ℓ e p hn hℓ hℓ2 he hp hp3 _ K _ _ k hk hK
  exact orthPairShape_odd k hn hℓ hℓ2 he hp hp3 hk hK

end Final

end CFSG.LieType.SeitzGeneration
