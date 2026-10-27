module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SCatalog
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.GL83PartI.I713.Orthogonal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open scoped Pointwise

theorem outLift_of_orthogonalGates {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hg : OrthogonalGates Q f) (hE : ¬ ℓ ∣ (matrixProjectiveImage Q).index)
    (H : Subgroup (K ≃+* K))
    (hH : (Nat.card (K ≃+* K)).factorization ℓ ≤ (Nat.card H).factorization ℓ)
    (σ₀ : H →* similarityPairs Q) (hσ₀ : ∀ σ : H, (σ₀ σ).val.right = σ.1)
    [Finite (matrixProjectiveDerived Q)] : OutLift ℓ (matrixProjectiveDerived Q) := by
  haveI := finite_ringAut K
  obtain ⟨-, ⟨ψ, hψ1, hψk, -⟩, ⟨hID, k, hk⟩, -⟩ := hg
  have hDE : (linearConjugationHom Q).range ≤ matrixProjectiveImage Q := by
    rintro _ ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  have hIE : inner (matrixProjectiveDerived Q) ≤ matrixProjectiveImage Q := hID.trans hDE
  refine outLift_of_hom hℓ ((matrixProjectiveConjugationHom Q).comp σ₀) ?_ ?_
  · intro σ hσ
    have h1 : matrixProjectiveConjugationHom Q (σ₀ σ) ∈ (linearConjugationHom Q).range := hID hσ
    have h2 : (⟨matrixProjectiveConjugationHom Q (σ₀ σ), ⟨σ₀ σ, rfl⟩⟩ :
        matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [hψk]
      exact h1
    rw [MonoidHom.mem_ker, hψ1, hσ₀] at h2
    exact Subtype.ext h2
  · refine le_trans ?_ hH
    have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hID hDE
    have h2 := Subgroup.relIndex_mul_index hIE
    have h3 : (linearConjugationHom Q).range.relIndex (matrixProjectiveImage Q) =
        Nat.card ψ.range := by
      rw [Subgroup.relIndex, ← hψk, Subgroup.index_ker]
    have hout : Nat.card (Outer (matrixProjectiveDerived Q)) =
        (2 ^ k * Nat.card ψ.range) * (matrixProjectiveImage Q).index := by
      rw [← hk, ← h3, h1]
      exact h2.symm
    have hn1 : ¬ ℓ ∣ 2 ^ k := fun h =>
      hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h))
    have h4 : (Nat.card (Outer (matrixProjectiveDerived Q))).factorization ℓ =
        (Nat.card ψ.range).factorization ℓ := by
      rw [hout, Nat.factorization_mul (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero)
          Nat.card_pos.ne') Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hE, add_zero,
        Nat.factorization_mul (pow_ne_zero _ two_ne_zero) Nat.card_pos.ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hn1, zero_add]
    rw [h4]
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card ψ.range) ℓ

theorem outLift_of_orthogonalGates_top {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hg : OrthogonalGates Q f) (hE : ¬ ℓ ∣ (matrixProjectiveImage Q).index)
    (σ₀ : (K ≃+* K) →* similarityPairs Q) (hσ₀ : ∀ σ, (σ₀ σ).val.right = σ)
    [Finite (matrixProjectiveDerived Q)] : OutLift ℓ (matrixProjectiveDerived Q) :=
  outLift_of_orthogonalGates Q hℓ hℓ2 hg hE ⊤ (by rw [Subgroup.card_top])
    (σ₀.comp (⊤ : Subgroup (K ≃+* K)).subtype) fun σ => hσ₀ σ.1

@[expose] noncomputable def fieldPairHom {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K))
    (hQ : ∀ (σ : K ≃+* K) (v : Fin d → K), Q (coordinateFieldMap d σ v) = σ (Q v)) :
    (K ≃+* K) →* similarityPairs Q where
  toFun σ := CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair Q σ (hQ σ)
  map_one' := Subtype.ext (SemidirectProduct.ext rfl rfl)
  map_mul' σ τ := Subtype.ext (SemidirectProduct.ext (by
    change (1 : GL (Fin d) K) = 1 * (glFieldAut (Fin d) K σ) 1
    simp) rfl)

theorem liftClause_classical_POmegaOdd {n p f : ℕ} :
    FamilyLift fun S _ => StatedClassicalModel S .POmegaOdd n p f := by
  intro S _ _ _ hnonab h ℓ hℓ hℓ2 hSℓ
  have h0 := h
  obtain ⟨⟨hp, hf, hn, hr2⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hchar, -⟩ := coordinate_model_witness_odd h K hK e
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaOdd (Or.inl rfl)
    n p f h K hK e
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn
    (by rw [hchar]; exact hr2)
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    Finite.of_equiv S (coordinateOddWitnessEquiv K e).toEquiv
  refine OutLift.of_mulEquiv (coordinateOddWitnessEquiv K e) ?_
  exact outLift_of_orthogonalGates_top (coordinateQuadOdd n K) hℓ hℓ2 hg
    (by rw [htop, Subgroup.index_top]; exact hℓ.not_dvd_one)
    (fieldPairHom _ fun σ v =>
      CFSG.RankThree.PartOne.KCOrthogonalSubfield.coordinateQuadOdd_fieldAut n σ v) fun σ => rfl

theorem liftClause_classical_POmegaPlus {n p f : ℕ} :
    FamilyLift fun S _ => StatedClassicalModel S .POmegaPlus n p f := by
  intro S _ _ _ hnonab h ℓ hℓ hℓ2 hSℓ
  have h0 := h
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaPlus
    (Or.inr (Or.inl rfl)) n p f h K hK e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv S (coordinatePlusWitnessEquiv K e).toEquiv
  have hEidx : ¬ ℓ ∣ (matrixProjectiveImage (coordinateQuadPlus n K)).index := by
    by_cases hn5 : 5 ≤ n
    · rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn5,
        Subgroup.index_top]
      exact hℓ.not_dvd_one
    · have hℓ3 : 3 < ℓ := by
        by_contra hle
        have : ℓ = 3 := by
          have := hℓ.two_le
          omega
        subst this
        have h2 := GL83.I713.two_le_pRank_three_classical_POmegaPlus h
        omega
      obtain ⟨-, -, -, horb, -, hAE, -⟩ := hg
      have h1 : (projectivePointFamilyAut (coordinateQuadPlus n K)).index =
          (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
            (projectivePointFamily (coordinateQuadPlus n K))).ncard :=
        MulAction.index_stabilizer _ _
      rw [← hAE, h1]
      intro hd
      have := Nat.le_of_dvd (by
        rw [← h1, hAE]
        exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hd
      omega
  refine OutLift.of_mulEquiv (coordinatePlusWitnessEquiv K e) ?_
  exact outLift_of_orthogonalGates_top (coordinateQuadPlus n K) hℓ hℓ2 hg hEidx
    (fieldPairHom _ fun σ v =>
      CFSG.RankThree.PartOne.KCOrthogonalSubfield.coordinateQuadPlus_fieldAut n σ v) fun σ => rfl

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
