module

public import CFSG.LieType.OutStructureRankFree
public import CFSG.LieType.OutStructureE6
public import CFSG.LieType.OutStructureOrthRemaining
import CFSG.Blueprint.SourceClassicalTransportOrthogonal

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def I713ClauseFreeFive (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Nonempty (K ≃* i.Group) → ∀ p : ℕ, p.Prime → 5 ≤ p →
        (¬ p ∣ Nat.card (Outer K)) ∨
        (∃ F : Subgroup (MulAut K), (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner K = ⊥ ∧
          ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).index ∧
          ∀ x : MulAut K, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F) ∨
        (p = 3 ∧ IsCyclic (Outer K) ∧ OuterPElementLifts K p)

theorem I713ClauseFree.toFive {i : TauCeti.CFSGIndex} (h : I713ClauseFree i) :
    I713ClauseFreeFive i := by
  intro K _ _ hK hnab he p hp hp5
  exact h K hK hnab he p hp (by omega)

section A1

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Semidihedral.SemilinearOuterQuotient

theorem i713ClauseFree_lie_A1 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩) := by
  intro K _ _ _ _ ⟨e⟩ p hp hp2
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := q.p) (n := q.exponent) (d := ⟨.A 1 q, hv⟩) ⟨q, rfl, rfl, rfl⟩
  let e3 : K ≃* coordinateG (GaloisField q.p q.exponent) :=
    e.trans (e2.trans (pslEquivCoordinateG (GaloisField q.p q.exponent)))
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv e3
    (exists_fieldPart_coordinateG (K := GaloisField q.p q.exponent)
      (p := p) (p₀ := q.p) (f := q.exponent) hp hp2 q.prime_p q.exponent_pos hcard)))

theorem i713ClauseFreeFive_lie_A1 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    I713ClauseFreeFive (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩) :=
  (i713ClauseFree_lie_A1 q hv).toFive

end A1

section E6

open CFSG.LieType.Chevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem i713ClauseFreeFive_lie_E6
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    I713ClauseFreeFive (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp hp5
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let S := (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group
  have : Finite S := Finite.of_equiv K eK.toEquiv
  have hm : ChevalleyExceptionalModel S .E6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq2 (MulEquiv.refl S)
    · exact CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.untwistedBridge_E6 q hv hq2 (MulEquiv.refl S)
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm.2
  let := hLfield
  let := hLfin
  have : Finite (adjointGroup Tag.E6 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_E6 q.prime_p q.exponent_pos L hLcard hp hp2 hp3)))

theorem i713ClauseFreeFive_lie_twistedE6
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    I713ClauseFreeFive (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp hp5
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let S := (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group
  have : Finite S := Finite.of_equiv K eK.toEquiv
  have hm : ChevalleyExceptionalModel S .twistedE6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hq2 (by decide)
        (MulEquiv.refl S)
    · exact CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hq2 (by decide)
        (MulEquiv.refl S)
  obtain ⟨L, hLfield, hLfin, σ, hLcard, hσ, ⟨eL⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_E6 hm
  let := hLfield
  let := hLfin
  have : Finite (twistedE6RootGroup L σ) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_twistedE6 q.prime_p q.exponent_pos L hLcard σ hσ hp hp2 hp3)))

end E6

section Lift

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical.SteinbergBY
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
open scoped Pointwise

theorem outLift_classical_POmegaOdd_free {n p f : ℕ} {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (h : StatedClassicalModel S .POmegaOdd n p f) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) : OutLift ℓ S := by
  have h0 := h
  obtain ⟨⟨-, -, hn, hr2⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hchar, -⟩ := coordinate_model_witness_odd h K hK e
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaOdd (Or.inl rfl)
    n p f h K hK e
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn
    (by rw [hchar]; exact hr2)
  have : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    Finite.of_equiv S (coordinateOddWitnessEquiv K e).toEquiv
  refine OutLift.of_mulEquiv (coordinateOddWitnessEquiv K e) ?_
  exact outLift_of_orthogonalGates_top (coordinateQuadOdd n K) hℓ hℓ2 hg
    (by rw [htop, Subgroup.index_top]; exact hℓ.not_dvd_one)
    (fieldPairHom _ fun σ v =>
      CFSG.RankThree.PartOne.KCOrthogonalSubfield.coordinateQuadOdd_fieldAut n σ v) fun σ => rfl

theorem outLift_classical_POmegaPlus_five {n p f : ℕ} {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (h : StatedClassicalModel S .POmegaPlus n p f) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ5 : 5 ≤ ℓ) : OutLift ℓ S := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaPlus
    (Or.inr (Or.inl rfl)) n p f h K hK e
  have : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv S (coordinatePlusWitnessEquiv K e).toEquiv
  have hEidx : ¬ ℓ ∣ (matrixProjectiveImage (coordinateQuadPlus n K)).index := by
    by_cases hn5 : 5 ≤ n
    · rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn5,
        Subgroup.index_top]
      exact hℓ.not_dvd_one
    · obtain ⟨-, -, -, horb, -, hAE, -⟩ := hg
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

theorem outLift_classical_POmegaMinus_free {n p f : ℕ} {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (h : StatedClassicalModel S .POmegaMinus n p f) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) : OutLift ℓ S := by
  have h0 := h
  obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  have := finite_ringAut K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (K ≃+* K)) := inferInstance
  have hcard : Nat.card (P : Subgroup (K ≃+* K)) = ℓ ^ (Nat.card (K ≃+* K)).factorization ℓ :=
    P.card_eq_multiplicity
  have hodd : Odd (Nat.card (P : Subgroup (K ≃+* K))) := by
    rw [hcard]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨b', c', hfix, hirr'⟩ := exists_fixed_rootFree_quadratic (P : Subgroup (K ≃+* K)) hodd
  obtain ⟨e'⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv hn1 hirr hirr'
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaMinus
    (Or.inr (Or.inr rfl)) n p f h hn1 K hK b' c' hirr' (e.trans e')
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4
    b' c' hirr'
  have : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b' c')) :=
    Finite.of_equiv S (coordinateMinusWitnessEquiv K hn1 b' c' (e.trans e')).toEquiv
  refine OutLift.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b' c' (e.trans e')) ?_
  refine outLift_of_orthogonalGates (coordinateQuadMinus n K hn1 b' c') hℓ hℓ2 hg
    (by rw [htop, Subgroup.index_top]; exact hℓ.not_dvd_one) (P : Subgroup (K ≃+* K)) ?_
    (fieldPairSubHom _ (P : Subgroup (K ≃+* K)) fun σ hσ v =>
      coordinateQuadMinus_fieldAut_of_fixed n hn1 (hfix σ hσ).1 (hfix σ hσ).2 v) fun σ => rfl
  rw [hcard, Nat.Prime.factorization_pow hℓ, Finsupp.single_eq_same]

end Lift

section Orth

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbedding
open CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
open CFSG.RankThree.PartOne.OutStructure
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

theorem i713ClauseFree_lie_B_odd (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p ≠ 2) (hr3 : 3 ≤ r) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩) := by
  intro K _ _ _ hnab ⟨eK⟩ p hp hp2
  have hSC : StatedClassicalModel K .POmegaOdd r q.p q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq2 hr3 eK
  have hChain : OutPChain p K := (outPNice_POmegaOdd_all hp hp2 hSC).toChain
  have hLift : OutLift p K := outLift_classical_POmegaOdd_free hSC hp hp2
  have hTower : OutTowerAt K p := outTowerAt_of_statedOdd_all hSC
  exact Or.inr (Or.inl (exists_fieldPart_of_outPChain_outLift_tower hnab hp hChain hLift hTower))

theorem i713ClauseFreeFive_lie_B_odd (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p ≠ 2) (hr3 : 3 ≤ r) :
    I713ClauseFreeFive (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩) :=
  (i713ClauseFree_lie_B_odd r q hv hq2 hr3).toFive

theorem i713ClauseFreeFive_lie_D (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) :
    I713ClauseFreeFive (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩) := by
  intro K _ _ _ hnab ⟨eK⟩ p hp hp5
  have hp2 : p ≠ 2 := by omega
  have hr4 : 4 ≤ r :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hSC : StatedClassicalModel K .POmegaPlus r q.p q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv eK
  have hChain : OutPChain p K := by
    rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
    · exact outPChain_POmegaPlus_four_gen hp hp5 hSC
    · exact (outPNice_POmegaPlus_all_ge_five hp hp2 hr5 hSC).toChain
  have hLift : OutLift p K := outLift_classical_POmegaPlus_five hSC hp hp5
  have hTower : OutTowerAt K p := outTowerAt_of_statedPlus hSC hp hp5
  exact Or.inr (Or.inl (exists_fieldPart_of_outPChain_outLift_tower hnab hp hChain hLift hTower))

theorem i713ClauseFreeFive_lie_twistedD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) :
    I713ClauseFreeFive (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩) := by
  intro K _ _ _ hnab ⟨eK⟩ p hp hp5
  have hp2 : p ≠ 2 := by omega
  have hSC : StatedClassicalModel K .POmegaMinus r q.p q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv eK
  have hChain : OutPChain p K := (outPNice_POmegaMinus_all hp hp2 hSC).toChain
  have hLift : OutLift p K := outLift_classical_POmegaMinus_free hSC hp hp2
  have hTower : OutTowerAt K p := outTowerAt_of_statedMinus hSC hp hp5
  exact Or.inr (Or.inl (exists_fieldPart_of_outPChain_outLift_tower hnab hp hChain hLift hTower))

end Orth

end CFSG.LieType.OutStructure
