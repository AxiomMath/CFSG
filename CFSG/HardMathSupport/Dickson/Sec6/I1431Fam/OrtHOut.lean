module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Rank

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.OutStructure
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.PartOne.Sec66T
open CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

section Generic

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem t6orth_isInnerAut_of_image_top (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ k : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ k)
    (htop : matrixProjectiveImage Q = ⊤) {τ : MulAut (matrixProjectiveDerived Q)}
    (hτ : τ ∈ innAutDerived (matrixProjectiveDerived Q)) (h3 : τ ^ 3 = 1) : IsInnerAut τ := by
  have hmem : ∀ α : MulAut (matrixProjectiveDerived Q),
      ∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = α := fun α =>
    (mem_matrixProjectiveImage_iff Q α).mp (htop ▸ Subgroup.mem_top α)
  have hC : commutator (MulAut (matrixProjectiveDerived Q)) ≤ orthD Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro γ _ α _
    obtain ⟨g, rfl⟩ := hmem γ
    obtain ⟨h, rfl⟩ := hmem α
    exact comm_mem_orthD Q g h
  have hD : τ ∈ orthD Q :=
    (sup_le (inner_le_orthD Q) hC : innAutDerived (matrixProjectiveDerived Q) ≤ orthD Q) hτ
  exact orthD_D2_of_bound' Q hQ hab Nat.prime_three (by norm_num) hD (k := 1)
    (by rw [pow_one, h3]; exact one_mem _)

end Generic

section Models

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Automorphisms

theorem outDerived3_orthOddNe3 : OutDerived3At (fun t n p f => FamOrthOdd t n p f ∧ p ≠ 3) := by
  intro P _ _ t n p f hadm ht hF hm τ hτ hτ3
  obtain ⟨rfl, hp3⟩ := hF
  have hC : StatedClassicalModel P .POmegaOdd n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨⟨-, -, hn, hr2⟩, K, _, _, hK, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_odd hC K hK e
  have hQ : ∃ v, coordinateQuadOdd n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound P .POmegaOdd (.inl rfl) n p f
    hC K hK (quadOdd n K) (coe_quadOdd n K) e
  have hab' := card_abelianization_two_pow_of_bound (oddIndexEquiv n) (quadOdd n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn
    (by rw [hchar]; exact hr2)
  have h1 : MulAut.congr (coordinateOddWitnessEquiv K e) τ ∈
      innAutDerived (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    (mem_innAutDerived_congr (coordinateOddWitnessEquiv K e)).2 hτ
  have h3 : (MulAut.congr (coordinateOddWitnessEquiv K e) τ) ^ 3 = 1 := by
    rw [← map_pow, hτ3, map_one]
  exact (isInnerAut_congr (coordinateOddWitnessEquiv K e) τ).1
    (t6orth_isInnerAut_of_image_top _ hQ hab' htop h1 h3)

theorem outDerived3_orthPlusNe3 : OutDerived3At (fun t n p f => FamOrthPlus t n p f ∧ p ≠ 3) := by
  intro P _ _ t n p f hadm ht hF hm τ hτ hτ3
  obtain ⟨⟨rfl, hn5⟩, hp3⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hC K hK e
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound P .POmegaPlus
    (.inr (.inl rfl)) n p f hC K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' := card_abelianization_two_pow_of_bound (plusIndexEquiv n) (quadPlus n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn5
  have h1 : MulAut.congr (coordinatePlusWitnessEquiv K e) τ ∈
      innAutDerived (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    (mem_innAutDerived_congr (coordinatePlusWitnessEquiv K e)).2 hτ
  have h3 : (MulAut.congr (coordinatePlusWitnessEquiv K e) τ) ^ 3 = 1 := by
    rw [← map_pow, hτ3, map_one]
  exact (isInnerAut_congr (coordinatePlusWitnessEquiv K e) τ).1
    (t6orth_isInnerAut_of_image_top _ hQ hab' htop h1 h3)

theorem outDerived3_orthMinusNe3 : OutDerived3At (fun t n p f => FamOrthMinus t n p f ∧ p ≠ 3) := by
  intro P _ _ t n p f hadm ht hF hm τ hτ hτ3
  obtain ⟨rfl, hp3⟩ := hF
  have hC : StatedClassicalModel P .POmegaMinus n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hC
  have hn1 : 1 ≤ n := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hC K hK b c hirr e
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound P .POmegaMinus
    (.inr (.inr rfl)) n p f hC K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' := card_abelianization_two_pow_of_bound (minusIndexEquiv n hn1) (quadMinus n K b c) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn
    b c hirr
  have h1 : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) τ ∈
      innAutDerived (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    (mem_innAutDerived_congr (coordinateMinusWitnessEquiv K hn1 b c e)).2 hτ
  have h3 : (MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) τ) ^ 3 = 1 := by
    rw [← map_pow, hτ3, map_one]
  exact (isInnerAut_congr (coordinateMinusWitnessEquiv K hn1 b c e) τ).1
    (t6orth_isInnerAut_of_image_top _ hQ hab' htop h1 h3)

end Models

end CFSG.HardMathSupport.Dickson.Sec6.I1431
