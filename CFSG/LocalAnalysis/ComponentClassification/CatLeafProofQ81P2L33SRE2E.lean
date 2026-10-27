module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Open
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2Tools
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotOddCore
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def highRootElt
    (τ : Tag) : adjointGroup τ K :=
  ⟨pinnedX τ K (highRoot τ) 1, pinnedX_mem_adjointGroup _ _⟩

theorem highRootElt_ne_one
    (τ : Tag) : highRootElt K τ ≠ 1 := by
  intro h
  have h' : pinnedX τ K (highRoot τ) 1 = pinnedX τ K (highRoot τ) 0 := by
    rw [pinnedX_zero]
    exact congrArg Subtype.val h
  exact one_ne_zero (pinnedX_injective τ K (highRoot τ) h')

theorem highRoot_mem_heightSeries
    (τ : Tag) {h : ℤ} (hh : h ≤ height (highRoot τ)) :
    (highRootElt K τ : ModGL τ K) ∈ heightSeries τ K h := by
  unfold heightSeries
  refine pinnedX_mem_rootSpan ?_ 1
  exact ⟨isRoot_highRoot τ, height_highRoot_pos τ, hh⟩

theorem highRoot_centralizer_not_isPGroup_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E8) [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    ¬ IsPGroup 2 ↥(centralizer ({highRootElt K τ} : Set (adjointGroup τ K))) := by
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := hτ.imp_right Or.inr
  by_cases hf2 : 2 ≤ f
  · exact not_isPGroup_of_mem_closure_odd (x := highRootElt K τ)
      (pinnedX_mem_closure_odd_E hτ' hf2 hK rfl (isRoot_highRoot τ) (height_highRoot_pos τ) 1)
      (highRootElt_ne_one τ)
  · have hK2 : Nat.card K = 2 := by rw [hK, show f = 1 by omega, pow_one]
    have hu : (highRootElt K τ : ModGL τ K) ∈ posUnipotent τ K := by
      rw [← heightSeries_one]
      exact highRoot_mem_heightSeries τ (height_highRoot_pos τ)
    exact not_isPGroup_of_mem_closure_odd
      (posUnipotent_le_closure_odd_E_two (u := highRootElt K τ) hτ' hK2 rfl hu)
      (highRootElt_ne_one τ)

theorem e6_centralizer_not_isPGroup
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {t : adjointGroup .E6 K} (ht : orderOf t = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set (adjointGroup .E6 K))) := by
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE6 ht2 ht1
  refine not_isPGroup_centralizer_of_isConj (a := g * t * g⁻¹)
    (isConj_iff.mpr ⟨g⁻¹, by group⟩) ?_
  rcases hg with h | h | h <;> rw [h]
  · exact highRoot_centralizer_not_isPGroup_E (Or.inl rfl) hf hK
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E6_y (by rfl)
      (highRootElt K .E6) (highRoot_mem_heightSeries .E6 (h := 4) (by decide)))
      (highRootElt_ne_one .E6)
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E6_z (by rfl)
      (highRootElt K .E6) (highRoot_mem_heightSeries .E6 (h := 5) (by decide)))
      (highRootElt_ne_one .E6)

theorem e7_centralizer_not_isPGroup
    [Finite K] [CharP K 2] {t : adjointGroup .E7 K} (ht : orderOf t = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set (adjointGroup .E7 K))) := by
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE7 ht2 ht1
  refine not_isPGroup_centralizer_of_isConj (a := g * t * g⁻¹)
    (isConj_iff.mpr ⟨g⁻¹, by group⟩) ?_
  have hr := highRoot_mem_heightSeries (K := K) .E7 (h := 10) (by decide)
  rcases hg with h | h | h | h | h <;> rw [h]
  · exact not_isPGroup_of_mem_closure_odd (E7Pilot.heightSeries_le_closure_odd_E7_x
      (by rw [E7Pilot.oddDerivE7XFrame, List.map_singleton, List.prod_singleton])
      (highRootElt K .E7) hr) (highRootElt_ne_one .E7)
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E7_y (by rfl)
      (highRootElt K .E7) (highRoot_mem_heightSeries .E7 (h := 5) (by decide)))
      (highRootElt_ne_one .E7)
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E7_z (by rfl)
      (highRootElt K .E7) (highRoot_mem_heightSeries .E7 (h := 7) (by decide)))
      (highRootElt_ne_one .E7)
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E7_u (by rfl)
      (highRootElt K .E7) hr) (highRootElt_ne_one .E7)
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E7_v (by rfl)
      (highRootElt K .E7) hr) (highRootElt_ne_one .E7)

theorem e8_centralizer_not_isPGroup
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {t : adjointGroup .E8 K} (ht : orderOf t = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set (adjointGroup .E8 K))) := by
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  obtain ⟨g, hg⟩ := classListE8_exists_conj_mem_innerRepsE8 ht2 ht1
  refine not_isPGroup_centralizer_of_isConj (a := g * t * g⁻¹)
    (isConj_iff.mpr ⟨g⁻¹, by group⟩) ?_
  rcases hg with h | h | h | h <;> rw [h]
  · exact highRoot_centralizer_not_isPGroup_E (Or.inr rfl) hf hK
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E8_y (by rfl)
      (highRootElt K .E8) (highRoot_mem_heightSeries .E8 (h := 7) (by decide)))
      (highRootElt_ne_one .E8)
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E8_z (by rfl)
      (highRootElt K .E8) (highRoot_mem_heightSeries .E8 (h := 11) (by decide)))
      (highRootElt_ne_one .E8)
  · exact not_isPGroup_of_mem_closure_odd (heightSeries_le_closure_odd_E8_u (by rfl)
      (highRootElt K .E8) (highRoot_mem_heightSeries .E8 (h := 13) (by decide)))
      (highRootElt_ne_one .E8)

end CFSG.ComponentClassification.HarrisLit.L33.SR.E2

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem involutionCentralizerNotTwoGroup_E6
    : InvolutionCentralizerNotTwoGroup .E6 := by
  intro Y _ _ f hY _ c hc
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact SR.E2.not_isPGroup_of_mulEquiv e c
    (SR.E2.e6_centralizer_not_isPGroup hf hK (by rw [MulEquiv.orderOf_eq]; exact hc))

theorem involutionCentralizerNotTwoGroup_E7
    : InvolutionCentralizerNotTwoGroup .E7 := by
  intro Y _ _ f hY _ c hc
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact SR.E2.not_isPGroup_of_mulEquiv e c
    (SR.E2.e7_centralizer_not_isPGroup (by rw [MulEquiv.orderOf_eq]; exact hc))

theorem involutionCentralizerNotTwoGroup_E8
    : InvolutionCentralizerNotTwoGroup .E8 := by
  intro Y _ _ f hY _ c hc
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact SR.E2.not_isPGroup_of_mulEquiv e c
    (SR.E2.e8_centralizer_not_isPGroup hf hK (by rw [MulEquiv.orderOf_eq]; exact hc))

end CFSG.ComponentClassification.HarrisLit.L33.E2
