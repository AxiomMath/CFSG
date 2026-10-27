module

public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic
public import CFSG.LieType.SeitzGeneration.ExcWideThree.F4E7E8
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6
public import CFSG.LieType.SeitzGeneration.ExcWideThree.G2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwistedE6
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrow

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti

section Families


@[expose] def E6ThreeDiagPlanes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → E ≤ e6Inndiag K → ¬ E ≤ innerAut (adjointGroup Tag.E6 K) →
      Subgroup.closure (fixUnion E) = ⊤

@[expose] def TwistedE6ThreeDiagPlanes : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = ℓ ^ (2 * f) → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ →
      ¬ E ≤ innerAut (twistedE6RootGroup K σ) → Subgroup.closure (fixUnion E) = ⊤

@[expose] def TrialityThreePlanesOdd : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ E : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      ¬ E ≤ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
      Subgroup.closure (fixUnion E) = ⊤

@[expose] def D4ElemType {K : Type} [Field K] [Finite K] (α : MulAut (adjointGroup Tag.D4 K))
    (c : ℕ → (K ≃+* K) → Prop) : Prop :=
  ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ),
    ε < 3 ∧ σ ^ 3 = 1 ∧ c ε σ ∧
      α = MulAut.conj g *
        (exactNormalAut Tag.D4 K a σ 0 * CFSG.HardMathSupport.Lang.D4Three.d4Graph K ε)

@[expose] def D4ThreeFieldPlanes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → (∃ α ∈ E, D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1) →
      Subgroup.closure (fixUnion E) = ⊤

@[expose] def D4ThreeGraphFieldPlanes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → (¬ ∃ α ∈ E, D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1) →
      (∃ α ∈ E, D4ElemType α fun ε σ => ε ≠ 0 ∧ σ ≠ 1) →
      Subgroup.closure (fixUnion E) = ⊤

@[expose] def D4ThreeGraphPlanes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (adjointGroup Tag.D4 K) →
      (∀ α ∈ E, α ∉ innerAut (adjointGroup Tag.D4 K) →
        D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
      Subgroup.closure (fixUnion E) = ⊤

theorem exists_catEquiv_D4 (q : PrimePower) (hv : (LieTypeIndex.D 4 q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧ CharP K q.p ∧
      Nonempty (CFSG.LieType.SeitzGeneration.Cat ⟨LieTypeIndex.D 4 q, hv⟩ ≃*
        ↥(adjointGroup Tag.D4 K)) := by
  obtain ⟨K, _, _, hK, hKchar⟩ := exists_field_pow q Nat.one_pos
  rw [pow_one] at hK
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_adjointQuotient_D4_equiv
    K q hv hK
  have hZ : Subgroup.center ↥(adjointGroup Tag.D4 K) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨K, inferInstance, inferInstance, hK, hKchar,
    ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩


theorem seitzExcOuterWideE6_three_of_diag (hD : E6ThreeDiagPlanes) :
    SeitzExcOuterWideForAt IsE6Index PrimeRange.three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨q, hq⟩, hp3⟩
  subst hq
  have hp3' : p = 3 := hp3
  subst hp3'
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hpq : 3 ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E6 q).symm)
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K q.p]
    exact fun h => hpq h.symm
  refine planeGen_outer_of_closure e Nat.prime_three (fun E' hE' hc' hout' => ?_) hE hc hout
  have hnin : ¬ E' ≤ innerAut (adjointGroup Tag.E6 K) := fun hle =>
    hout' fun φ hφ => (hle hφ).imp fun g hg => hg.symm
  by_cases hdiag : E' ≤ e6Inndiag K
  · exact hD K hK3 E' hE' hc' hdiag hnin
  · have := hE'
    exact e6_fieldPlanes_three subfieldMaximalAllThree_E6 hK3 E' hc' hdiag

theorem seitzExcOuterWideTwE6_three_of (hker : TwistedE6KernelLemma)
    (hD : TwistedE6ThreeDiagPlanes) : SeitzExcOuterWideForAt IsTwistedE6Index PrimeRange.three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨q, hq⟩, hp3⟩
  subst hq
  have hp3' : p = 3 := hp3
  subst hp3'
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hpq : 3 ≠ q.p := by simpa [TauCeti.ValidLieTypeIndex.characteristic] using hpd
  have hK' : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  refine planeGen_outer_of_closure e Nat.prime_three (fun E' hE' hc' hout' => ?_) hE hc hout
  have hnin : ¬ E' ≤ innerAut (twistedE6RootGroup K σ) := fun hle =>
    hout' fun φ hφ => (hle hφ).imp fun g hg => hg.symm
  by_cases hdiag : E' ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
  · exact hD q.p q.exponent q.prime_p (fun h => hpq h.symm) q.exponent_pos K hK' σ hσ E' hE' hc'
      hdiag hnin
  · have := hE'
    exact twistedE6_fieldPlanes_three hker q.prime_p (fun h => hpq h.symm) q.exponent_pos hK' σ hσ
      E' hc' hdiag

theorem seitzExcOuterWideTriality_three_of_odd_two (hOdd : TrialityThreePlanesOdd)
    (hTwo : CFSG.RankThree.PartTwo.Sec19.SeitzThreeTrialityWideTwo) :
    SeitzExcOuterWideForAt IsTrialityIndex PrimeRange.three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hns, ⟨q, hq⟩, hp3⟩
  subst hq
  have hp3' : p = 3 := hp3
  subst hp3'
  by_cases h2 : q.p = 2
  · refine hTwo ⟨_, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨rfl, ⟨q, rfl⟩, ?_, Or.inl ⟨hout, hns⟩⟩
    simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using h2
  · obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
    have hpq : 3 ≠ q.p := by
      intro h3
      apply hpd
      simpa [TauCeti.ValidLieTypeIndex.characteristic,
        TauCeti.LieTypeIndex.characteristic_trialityD4] using h3
    refine planeGen_outer_of_closure e Nat.prime_three (fun E' hE' hc' hout' => ?_) hE hc hout
    have hnin : ¬ E' ≤ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun hle =>
      hout' fun φ hφ => (hle hφ).imp fun g hg => hg.symm
    exact hOdd q.p q.exponent q.prime_p h2 (fun h3 => hpq h3.symm) q.exponent_pos K hK σ hσ E'
      hE' hc' hnin

theorem seitzExcOuterWideDFour_three_of_parts (hF : D4ThreeFieldPlanes)
    (hGF : D4ThreeGraphFieldPlanes) (hG : D4ThreeGraphPlanes) :
    SeitzExcOuterWideForAt IsDFourIndex PrimeRange.three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨q, hq⟩, hp3⟩
  subst hq
  have hp3' : p = 3 := hp3
  subst hp3'
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ := exists_catEquiv_D4 q hv
  have hpq : 3 ≠ q.p := by
    intro h3
    apply hpd
    simpa [TauCeti.ValidLieTypeIndex.characteristic,
      TauCeti.LieTypeIndex.characteristic_D] using h3
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K q.p]
    exact fun h => hpq h.symm
  refine planeGen_outer_of_closure e Nat.prime_three (fun E' hE' hc' hout' => ?_) hE hc hout
  have hnin : ¬ E' ≤ innerAut (adjointGroup Tag.D4 K) := fun hle =>
    hout' fun φ hφ => (hle hφ).imp fun g hg => hg.symm
  have hcases : ∀ β ∈ E', β ∉ innerAut (adjointGroup Tag.D4 K) →
      (D4ElemType β fun ε σ => ε = 0 ∧ σ ≠ 1) ∨ (D4ElemType β fun ε σ => ε ≠ 0 ∧ σ ≠ 1) ∨
        (D4ElemType β fun ε σ => ε ≠ 0 ∧ σ = 1) := by
    intro β hβ hβin
    have hβ3 : β ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian β hβ
    obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ := outer_cube_normal_form_cases β hβ3 hβin
    rcases hcase with h1 | h1 | h1
    · exact Or.inl ⟨g, a, σ, ε, hε, hσ3, h1, hαeq⟩
    · exact Or.inr (Or.inl ⟨g, a, σ, ε, hε, hσ3, h1, hαeq⟩)
    · exact Or.inr (Or.inr ⟨g, a, σ, ε, hε, hσ3, h1, hαeq⟩)
  by_cases h1 : ∃ α ∈ E', D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1
  · exact hF K hK3 E' hE' hc' h1
  by_cases h2 : ∃ α ∈ E', D4ElemType α fun ε σ => ε ≠ 0 ∧ σ ≠ 1
  · exact hGF K hK3 E' hE' hc' h1 h2
  · refine hG K hK3 E' hE' hc' hnin fun α hα hαin => ?_
    rcases hcases α hα hαin with h | h | h
    · exact absurd ⟨α, hα, h⟩ h1
    · exact absurd ⟨α, hα, h⟩ h2
    · exact h


theorem seitzExcOuterWideThreeFamilies_of_open_inputs
    (hE6D : E6ThreeDiagPlanes) (hTwK : TwistedE6KernelLemma) (hTwD : TwistedE6ThreeDiagPlanes)
    (hTriOdd : TrialityThreePlanesOdd)
    (hTriTwo : CFSG.RankThree.PartTwo.Sec19.SeitzThreeTrialityWideTwo)
    (hD4F : D4ThreeFieldPlanes) (hD4GF : D4ThreeGraphFieldPlanes)
    (hD4G : D4ThreeGraphPlanes) : SeitzExcOuterWideThreeFamilies where
  g2 :=
    seitzExcOuterWide_G2_three
  triality := seitzExcOuterWideTriality_three_of_odd_two hTriOdd hTriTwo
  f4 := seitzExcOuterWideF4_three
  e6 := seitzExcOuterWideE6_three_of_diag hE6D
  e7 := seitzExcOuterWideE7_three
  e8 := seitzExcOuterWideE8_three
  twistedE6 := seitzExcOuterWideTwE6_three_of hTwK hTwD
  dFour := seitzExcOuterWideDFour_three_of_parts hD4F hD4GF hD4G

end Families

end CFSG.LieType.SeitzGeneration.ExcWideThree
