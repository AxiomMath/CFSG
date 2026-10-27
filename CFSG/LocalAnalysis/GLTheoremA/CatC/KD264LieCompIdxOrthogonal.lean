module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompRel
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedOrthogonal
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open TauCeti CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

section CatalogueOverBridge

open CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaAux.C

private theorem catalogueOver_projOrthDerived_odd {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 3 ≤ n) (h2 : ringChar K ≠ 2) :
    CatalogueOver (ringChar K) (Nat.card K) (ProjOrthDerived (quadOdd n K)) := by
  obtain ⟨q, hv, hcard, hqp, ⟨iso⟩⟩ :=
    exists_mulEquiv_catalogue_statedProj_odd (K := K) n hn h2
  obtain ⟨hreg, hregT⟩ :=
    CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := K) (n := n) (Ring.two_ne_zero h2) hn
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hreg hregT
  haveI := hsimple
  have hZ : Subgroup.center (ProjOrthDerived (quadOdd n K)) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnonab
  refine ⟨.lie ⟨.B n q, hv⟩, ⟨⟨?e⟩, ?h⟩⟩
  · exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans
        ((CFSG.RankThree.PartOne.statedProjOrthEquiv (coe_quadOdd n K)).symm.trans
          iso))
  · refine Or.inl ⟨(LieTypeIndex.characteristic_B n q).trans hqp, ?_, ?_⟩
    · show q.card = Nat.card K
      rw [hcard, Nat.card_eq_fintype_card]
    · simp [suzRee]

private theorem catalogueOver_projOrthDerived_plus {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 4 ≤ n) :
    CatalogueOver (ringChar K) (Nat.card K) (ProjOrthDerived (quadPlus n K)) := by
  obtain ⟨q, hv, hcard, hqp, ⟨iso⟩⟩ :=
    exists_mulEquiv_catalogue_statedProj_plus (K := K) n hn
  obtain ⟨hreg, hregT⟩ :=
    CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n) (by omega)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hreg hregT
  haveI := hsimple
  have hZ : Subgroup.center (ProjOrthDerived (quadPlus n K)) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnonab
  refine ⟨.lie ⟨.D n q, hv⟩, ⟨⟨?e⟩, ?h⟩⟩
  · exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans
        ((CFSG.RankThree.PartOne.statedProjOrthEquiv (coe_quadPlus n K)).symm.trans
          iso))
  · refine Or.inl ⟨(LieTypeIndex.characteristic_D n q).trans hqp, ?_, ?_⟩
    · show q.card = Nat.card K
      rw [hcard, Nat.card_eq_fintype_card]
    · simp [suzRee]

private theorem catalogueOver_projOrthDerived_minus {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CatalogueOver (ringChar K) (Nat.card K) (ProjOrthDerived (quadMinus n K b c)) := by
  obtain ⟨q, hv, hcard, hqp, ⟨iso⟩⟩ :=
    exists_mulEquiv_catalogue_statedProj_minus (K := K) n hn hirr
  obtain ⟨hreg, hregT⟩ :=
    CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) hn hirr
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hreg hregT
  haveI := hsimple
  have hZ : Subgroup.center (ProjOrthDerived (quadMinus n K b c)) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnonab
  refine ⟨.lie ⟨.twistedD n q, hv⟩, ⟨⟨?e⟩, ?h⟩⟩
  · exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans
        ((CFSG.RankThree.PartOne.statedProjOrthEquiv
          (coe_quadMinus n K b c)).symm.trans iso))
  · refine Or.inl ⟨(LieTypeIndex.characteristic_twistedD n q).trans hqp, ?_, ?_⟩
    · show q.card = Nat.card K
      rw [hcard, Nat.card_eq_fintype_card]
    · simp [suzRee]

private theorem catalogueOver_projOrthDerived_large {K : Type} [Field K] [Fintype K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 7 ≤ Module.finrank K V)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    CatalogueOver (ringChar K) (Nat.card K) (ProjOrthDerived Q) := by
  rcases Nat.even_or_odd' (Module.finrank K V) with ⟨n, hn | hn⟩
  · have hn4 : 4 ≤ n := by omega
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ
      (by omega) hn with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
    · have hc := catalogueOver_projOrthDerived_plus (K := K) n hn4
      exact hc.of_mulEquiv
        (CFSG.RankThree.PartOne.KCOrthogonalDescent.projOrthDerivedEquiv e.toLinearEquiv 1
          (fun v => by rw [Units.val_one, one_mul]; exact e.map_app v)).symm
    · have hc := catalogueOver_projOrthDerived_minus (K := K) n hn4 hirr
      exact hc.of_mulEquiv
        (CFSG.RankThree.PartOne.KCOrthogonalDescent.projOrthDerivedEquiv e.toLinearEquiv 1
          (fun v => by rw [Units.val_one, one_mul]; exact e.map_app v)).symm
  · have hn3 : 3 ≤ n := by omega
    have h2 : ringChar K ≠ 2 := by
      intro h2
      haveI : CharP K 2 := ringChar.of_eq h2
      obtain ⟨m, hm⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
      omega
    obtain ⟨d, hd0, ⟨e⟩⟩ := CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd h2 Q hQ hn
    have hc := catalogueOver_projOrthDerived_odd (K := K) n hn3 h2
    exact hc.of_mulEquiv
      (CFSG.RankThree.PartOne.KCOrthogonalDescent.projOrthDerivedEquiv e.toLinearEquiv
        (Units.mk0 d hd0) (fun v => e.map_app v)).symm

private theorem catalogueOver_orthDerived_large {K : Type} [Field K] [Fintype K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 7 ≤ Module.finrank K V)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    CatalogueOver (ringChar K) (Nat.card K) ↥(orthDerived Q) := by
  obtain ⟨-, hcenter, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  haveI := hsimple
  have hZ : Subgroup.center (ProjOrthDerived Q) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnonab
  obtain ⟨i, ⟨eP⟩, hidx⟩ := catalogueOver_projOrthDerived_large hQ hd hT
  refine ⟨i, ⟨⟨?e⟩, hidx⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hcenter).trans
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eP)

theorem catalogueOver_of_orthFactorOver {ℓ q : ℕ} {X : Type} [Group X]
    (h : OrthFactorOver ℓ q X) : ∃ j : ℕ, 1 ≤ j ∧ CatalogueOver ℓ (q ^ j) X := by
  rcases h with ⟨m, j, E, hfield, hfinite, hm, hj, hchar, hcard, h4, ⟨e⟩⟩
    | ⟨m, j, q', E, hfield, hfinite, hm, hj, hchar, hq', hcard, hne, ⟨e⟩⟩
    | ⟨K', hfield, hfinite, hK, hchar, s, hs, hne, ⟨e⟩⟩
    | ⟨K', hfield, hfinite, V, hAdd, hMod, hFin, Q, hK, hchar, hQ, hd, hT, ⟨e⟩⟩
  · letI := hfield
    letI := hfinite
    have hc := catalogueOver_sl E m hm h4
    rw [hchar, hcard] at hc
    exact ⟨j, hj, hc.of_mulEquiv e.symm⟩
  · letI := hfield
    letI := hfinite
    have hc := catalogueOver_su E m q' hcard hm hne
    rw [hchar] at hc
    refine ⟨j, hj, ?_⟩
    rw [← hq']
    exact hc.of_mulEquiv e.symm
  · letI := hfield
    letI := hfinite
    have hne' : (s, Fintype.card K') ≠ (2, 2) := by
      simpa [Nat.card_eq_fintype_card] using hne
    have hc := catalogueOver_sp K' s hs hne'
    have hcard' : Fintype.card K' = q := by rw [← Nat.card_eq_fintype_card, hK]
    rw [hchar, hcard'] at hc
    refine ⟨1, le_rfl, ?_⟩
    simpa [pow_one] using hc.of_mulEquiv e.symm
  · letI := hfield
    letI := hfinite
    letI := hAdd
    letI := hMod
    letI := hFin
    have hc := catalogueOver_orthDerived_large (K := K') (V := V) (Q := Q) hQ hd hT
    rw [hchar, hK] at hc
    refine ⟨1, le_rfl, ?_⟩
    simpa [pow_one] using hc.of_mulEquiv e.symm

end CatalogueOverBridge

theorem catalogueOver_component_conj_omega {t : CFSG.Open.StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] [Finite G]
    {n ℓ f : ℕ} (hG : CFSG.Open.StatedClassicalModel G t n ℓ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (a : G) (ha : a ^ p = 1) (J : Subgroup G)
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a))) :
    ∃ j : ℕ, 1 ≤ j ∧ CatalogueOver ℓ ((ℓ ^ f) ^ j) ↥J := by
  obtain ⟨X, _, _, hX, hfac, -, g, hg, hk⟩ :=
    exists_lieFactor_of_component_conj_omega_card slFactorFacts_holds suFactorFacts_holds
      omegaFactorField_holds hp hp2 ht hG hpℓ a ha J hJ
  obtain ⟨j, hj, hcat⟩ := catalogueOver_of_orthFactorOver hfac
  exact ⟨j, hj, hcat.of_surjective hX.perfect g hg hk⟩

private theorem primePower_prime_of_card_eq {q : TauCeti.PrimePower} {ℓ f : ℕ}
    (hp : ℓ.Prime) (hq : q.card = ℓ ^ f) : q.p = ℓ := by
  have hcard := hq
  rw [TauCeti.PrimePower.card_def] at hcard
  have hdvd : q.p ∣ ℓ ^ f := hcard ▸ dvd_pow_self q.p q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p hp).mp (q.prime_p.dvd_of_dvd_pow hdvd)

theorem matrixModel_facts_pomegaOdd {n ℓ f : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaOdd n ℓ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    (QuadraticMap.polarBilin (coordinateQuadOdd n K)).Nondegenerate ∧
      (∃ T : Submodule K (Fin (2 * n + 1) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadOdd n K x = 0) ∧
      Subgroup.center (matrixProjectiveDerived (coordinateQuadOdd n K)) = ⊥ ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∀ β ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadOdd n K)), β ^ p = 1 →
          β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
            (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  have hadm := hG.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hℓ2 : ℓ ≠ 2 := hadm.2.2.2
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  have h2 : ringChar K ≠ 2 := by rw [hchar]; exact hℓ2
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_odd hG K hK e
  have hQ : ∃ v, coordinateQuadOdd n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := card_abelianization_two_pow_of_bound (oddIndexEquiv n) (quadOdd n K)
    (orthogonal_model_isometry_abelianization_order_bound G .POmegaOdd (Or.inl rfl) n ℓ f hG
      K hK (quadOdd n K) (coe_quadOdd n K) e)
  have htop : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn h2
  have hdpos : 0 < 2 * n + 1 := by omega
  refine ⟨hnd, hT,
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot hdpos hnd hT,
    fun p hp hp2 β hβ hβp => ?_⟩
  exact mem_inner_of_mem_innAutDerived_of_pow_eq_one (coordinateQuadOdd n K) hQ hab hp hp2
    htop hβ hβp

theorem matrixModel_facts_pomegaPlus {n ℓ f : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f) (hn : 5 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    (QuadraticMap.polarBilin (coordinateQuadPlus n K)).Nondegenerate ∧
      (∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadPlus n K x = 0) ∧
      Subgroup.center (matrixProjectiveDerived (coordinateQuadPlus n K)) = ⊥ ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∀ β ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadPlus n K)), β ^ p = 1 →
          β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
            (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  have hadm := hG.1
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hG K hK e
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := card_abelianization_two_pow_of_bound (plusIndexEquiv n) (quadPlus n K)
    (orthogonal_model_isometry_abelianization_order_bound G .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f hG K hK (quadPlus n K) (coe_quadPlus n K) e)
  have htop : matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  have hdpos : 0 < 2 * n := by omega
  refine ⟨hnd, hT,
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot hdpos hnd hT,
    fun p hp hp2 β hβ hβp => ?_⟩
  exact mem_inner_of_mem_innAutDerived_of_pow_eq_one (coordinateQuadPlus n K) hQ hab hp hp2
    htop hβ hβp

theorem matrixModel_facts_pomegaMinus {n ℓ f : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (hn1 : 1 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    (QuadraticMap.polarBilin (coordinateQuadMinus n K hn1 b c)).Nondegenerate ∧
      (∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadMinus n K hn1 b c x = 0) ∧
      Subgroup.center (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) = ⊥ ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∀ β ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)),
          β ^ p = 1 →
          β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
            (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
  have hadm := hG.1
  have hn4 : 4 ≤ n := hadm.2.2
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hG K hK b c hirr e
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := card_abelianization_two_pow_of_bound (minusIndexEquiv n hn1)
    (quadMinus n K b c)
    (orthogonal_model_isometry_abelianization_order_bound G .POmegaMinus (Or.inr (Or.inr rfl))
      n ℓ f hG K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e)
  have htop : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
  have hdpos : 0 < 2 * n := by omega
  refine ⟨hnd, hT,
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot hdpos hnd hT,
    fun p hp hp2 β hβ hβp => ?_⟩
  exact mem_inner_of_mem_innAutDerived_of_pow_eq_one (coordinateQuadMinus n K hn1 b c) hQ hab
    hp hp2 htop hβ hβp

theorem compIdxAt_pomegaOdd {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f) :
    CompIdxAt p (.B n q) G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn : 3 ≤ n := hadm.2.2.1
  have hℓ2 : ℓ ≠ 2 := hadm.2.2.2
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  have h2 : ringChar K ≠ 2 := by rw [hchar]; exact hℓ2
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    Finite.of_equiv G (coordinateOddWitnessEquiv K e).toEquiv
  have hcoord : CompIdxAt p (.B n q) (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
    intro β hβmem hβp hβ1 J hJ
    obtain ⟨-, -, hZ, hinner⟩ := matrixModel_facts_pomegaOdd hG0 hK e
    obtain ⟨a, ha, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ
      (hinner p hp hp2 β hβmem hβp) hβp
    have hM : CFSG.Open.StatedClassicalModel (matrixProjectiveDerived (coordinateQuadOdd n K))
        .POmegaOdd n ℓ f :=
      ⟨hadm, K, hfield, hfinite, hK,
        ⟨(statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n K) (coe_quadOdd n K)).symm⟩⟩
    obtain ⟨j, hj, i, ⟨eJ⟩, hidx⟩ :=
      catalogueOver_component_conj_omega (t := .POmegaOdd) (Or.inl rfl) hM hp hp2 hpℓ a ha J hJ
    refine ⟨i, ⟨eJ⟩, ?_⟩
    have hfield_eq : fieldSize (.B n q : TauCeti.LieTypeIndex) = ℓ ^ f := hq
    have hchar_eq : (.B n q : TauCeti.LieTypeIndex).characteristic = ℓ := by
      rw [TauCeti.LieTypeIndex.characteristic_B]
      exact primePower_prime_of_card_eq hadm.1 hq
    exact compRelC_of_idxOver (d := .B n q) (i := i) (j := j) hj (by
      simpa [hfield_eq, hchar_eq] using hidx)
  exact compIdxAt_of_mulEquiv (coordinateOddWitnessEquiv K e).symm hcoord

theorem compIdxAt_pomegaPlus {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f) (hn : 5 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f) :
    CompIdxAt p (.D n q) G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn4 : 4 ≤ n := hadm.2.2
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv G (coordinatePlusWitnessEquiv K e).toEquiv
  have hcoord : CompIdxAt p (.D n q) (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    intro β hβmem hβp hβ1 J hJ
    obtain ⟨-, -, hZ, hinner⟩ := matrixModel_facts_pomegaPlus hG0 hn hK e
    obtain ⟨a, ha, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ
      (hinner p hp hp2 β hβmem hβp) hβp
    have hM : CFSG.Open.StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K))
        .POmegaPlus n ℓ f :=
      ⟨hadm, K, hfield, hfinite, hK,
        ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K)).symm⟩⟩
    obtain ⟨j, hj, i, ⟨eJ⟩, hidx⟩ :=
      catalogueOver_component_conj_omega (t := .POmegaPlus) (Or.inr (Or.inl rfl)) hM hp hp2 hpℓ
        a ha J hJ
    refine ⟨i, ⟨eJ⟩, ?_⟩
    have hfield_eq : fieldSize (.D n q : TauCeti.LieTypeIndex) = ℓ ^ f := hq
    have hchar_eq : (.D n q : TauCeti.LieTypeIndex).characteristic = ℓ := by
      rw [TauCeti.LieTypeIndex.characteristic_D]
      exact primePower_prime_of_card_eq hadm.1 hq
    exact compRelC_of_idxOver (d := .D n q) (i := i) (j := j) hj (by
      simpa [hfield_eq, hchar_eq] using hidx)
  exact compIdxAt_of_mulEquiv (coordinatePlusWitnessEquiv K e).symm hcoord

theorem compIdxAt_pomegaMinus {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f) :
    CompIdxAt p (.twistedD n q) G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn4 : 4 ≤ n := hadm.2.2
  have hn1 : 1 ≤ n := by omega
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    Finite.of_equiv G (coordinateMinusWitnessEquiv K hn1 b c e).toEquiv
  have hcoord : CompIdxAt p (.twistedD n q)
      (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
    intro β hβmem hβp hβ1 J hJ
    obtain ⟨-, -, hZ, hinner⟩ := matrixModel_facts_pomegaMinus hG0 hK hn1 b c hirr e
    obtain ⟨a, ha, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ
      (hinner p hp hp2 β hβmem hβp) hβp
    have hM : CFSG.Open.StatedClassicalModel
        (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) .POmegaMinus n ℓ f :=
      ⟨hadm, K, hfield, hfinite, hK, b, c, hirr,
        ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn1) (quadMinus n K b c)
          (coe_quadMinus n K b c)).symm⟩⟩
    obtain ⟨j, hj, i, ⟨eJ⟩, hidx⟩ :=
      catalogueOver_component_conj_omega (t := .POmegaMinus) (Or.inr (Or.inr rfl)) hM hp hp2 hpℓ
        a ha J hJ
    refine ⟨i, ⟨eJ⟩, ?_⟩
    have hfield_eq : fieldSize (.twistedD n q : TauCeti.LieTypeIndex) = ℓ ^ f := hq
    have hchar_eq : (.twistedD n q : TauCeti.LieTypeIndex).characteristic = ℓ := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedD]
      exact primePower_prime_of_card_eq hadm.1 hq
    exact compRelC_of_idxOver (d := .twistedD n q) (i := i) (j := j) hj (by
      simpa [hfield_eq, hchar_eq] using hidx)
  exact compIdxAt_of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e).symm hcoord

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
