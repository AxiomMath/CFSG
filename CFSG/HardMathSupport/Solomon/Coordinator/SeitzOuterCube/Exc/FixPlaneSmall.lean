module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneUntw
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenG2Two
public import CFSG.RankThree.PartOne.SEITZ2.G2Outer
public import CFSG.RankThree.SteinbergBRThreeG2Noninner
public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.TauCetiBridge TauCeti CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.SEITZ2

theorem not_sq_dvd_card_G2_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ^ 2 ∣ 12096 := by
  intro h
  have hle : p ^ 2 ≤ 12096 := Nat.le_of_dvd (by norm_num) h
  have hp110 : p ≤ 110 := by nlinarith
  interval_cases p <;> first
    | (exfalso; revert hp; norm_num; done)
    | (revert h; norm_num; done)
    | omega

section G2Descent


theorem stdDescent_G2_even {f p : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) : StdDescent .G2 K p := by
  intro α hα
  obtain ⟨h0, σ, hσ, h⟩ := SEITZ2.exists_conj_entrywise hp hf hK α hα
  exact ⟨MulAut.conj h0, σ, hσ, h⟩

theorem stdDescent_G2_odd {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) :
    StdDescent .G2 K p := by
  classical
  obtain ⟨hNFpt, Θ, hΘspec, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
      (Or.inr ⟨rfl, hℓ3⟩)
  have hNF := conj_normalForm_of_pointwise hNFpt
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card hℓ hf hK
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  intro α hα
  obtain ⟨hord, hout⟩ := hα
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
  obtain ⟨hσp, -, ⟨δ, hδ⟩, -⟩ :=
    odd_Chevalley_inner_field_noninner_prime_local_core_trivial .G2 hℓ hℓ2 hf K hK hNF hp ⊤
      le_top ⟨α, Subgroup.mem_top _⟩ (fun ⟨g, hg⟩ => hout g hg.symm)
      (by rw [Subgroup.orderOf_mk]; exact hord) x σ hxσ
  set τ : K ≃+* K := Θ δ with hτ
  have hΘτ : Θ (entrywiseAdjointAut .G2 τ) = τ := by
    refine hΘspec _ 1 τ fun h => ?_
    rw [coe_entrywiseAdjointAut]
    simp
  have hker1 : δ⁻¹ * entrywiseAdjointAut .G2 τ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΘτ, ← hτ, inv_mul_cancel]
  rw [hker] at hker1
  obtain ⟨g, hg⟩ := hker1
  have hcomm : τ * σ = σ * τ := by
    let _ := IsCyclic.commGroup (α := K ≃+* K)
    exact mul_comm τ σ
  have hcomm' : entrywiseAdjointAut .G2 σ * entrywiseAdjointAut .G2 τ =
      entrywiseAdjointAut .G2 τ * entrywiseAdjointAut .G2 σ := by
    rw [← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, hcomm]
  refine ⟨MulAut.conj g⁻¹, σ, hσp, ?_⟩
  have hgi : MulAut.conj g⁻¹ = (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹ := by
    rw [map_inv, hg]
  rw [hgi]
  calc (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹ * α * (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹⁻¹
      = (entrywiseAdjointAut .G2 τ)⁻¹ * (δ * α * δ⁻¹) * entrywiseAdjointAut .G2 τ := by
        group
    _ = (entrywiseAdjointAut .G2 τ)⁻¹ * (entrywiseAdjointAut .G2 σ *
          entrywiseAdjointAut .G2 τ) := by rw [hδ, mul_assoc]
    _ = entrywiseAdjointAut .G2 σ := by rw [hcomm', inv_mul_cancel_left]

theorem stdDescent_G2_three {f p : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (hp : p.Prime) (hp5 : 5 ≤ p) : StdDescent .G2 K p := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hf hK
  have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := hchar
  obtain ⟨-, hNF, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  intro α hα
  obtain ⟨hord, hout⟩ := hα
  let α' : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K) := α
  have hord' : orderOf α' = p := hord
  have hout' : ∀ g : adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K, α' ≠ MulAut.conj g := hout
  obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α'
  obtain ⟨-, -, ⟨σ, -, hσp, hσeq, -⟩, ⟨h, hh⟩, -⟩ :=
    CFSG.RankThree.three_G2_noninner_odd_prime_local_core_trivial hf hK hp (by omega) ⊤ le_top
      (⟨α', Subgroup.mem_top _⟩ :
        (⊤ : Subgroup (MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K))))
      (fun ⟨g, hg⟩ => hout' g hg.symm)
      (by rw [Subgroup.orderOf_mk]; exact hord') x a a.2 hxa
  have hfin : MulAut.conj h * α' * (MulAut.conj h)⁻¹ =
      entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.G2.tag σ := hh.trans hσeq
  exact ⟨MulAut.conj h, σ, hσp, hfin⟩

end G2Descent

section G2Fix


theorem two_le_card (q : PrimePower) : 2 ≤ q.card := by
  rw [PrimePower.card_def]
  exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' _)

theorem valid_G2_of_three_le {q : PrimePower} (h : 3 ≤ q.card) :
    (LieTypeIndex.G2 q).Valid := by
  refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
  · simp only [LieTypeIndex.inStandardRange_iff]
    omega
  · simp [LieTypeIndex.isDuplicateRepresentative_iff]

theorem conj_injective_cat_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨.G2 q, hv⟩ →* MulAut (Cat ⟨.G2 q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  exact conj_injective_of_mulEquiv e (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := .G2) (K := K)))

theorem fixPlaneGen_G2 (hLow : ExcInnerLowPlanes) {q : PrimePower} (hq3 : 3 ≤ q.card)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q.p) (h8 : ¬ (p = 3 ∧ q.card = 8))
    (hrank : RankLE2 p (adjointGroup .G2 K)) : FixPlaneGen ↥(adjointGroup .G2 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have hdesc : StdDescent .G2 K p := by
    by_cases h2 : q.p = 2
    · have hf : 2 ≤ q.exponent := by
        by_contra hlt
        have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
        rw [PrimePower.card_def, h1, h2] at hq3
        omega
      exact stdDescent_G2_even hf (by rw [hK', h2]) hp
    · by_cases h3 : q.p = 3
      · have hp5 : 5 ≤ p :=
          five_le_of_prime_ne_two_three hp hp2 (by rw [h3] at hpq; exact hpq)
        exact stdDescent_G2_three q.exponent_pos (by rw [hK', h3]) hp hp5
      · exact stdDescent_G2_odd q.prime_p h2 h3 q.exponent_pos hK' hp
  refine fixPlaneGen_untw_of_data hLow Even.chevalleyBridgesAll.g2
    (fun q => (isChevalleyExcIndex_G2 q).not_classical)
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_G2 q))
    (fun q => LieTypeIndex.characteristic_G2 q) (fun q hv => conj_injective_cat_G2 q hv) hK hp hp2
    hpq hrank ?_ hdesc
    (fun σ _ => CFSG.ComponentClassification.UnbalancedCatalog.entrywiseFixedGroup_eq_fixedFieldImage σ)
  intro q₀ hqq hv k _ _ hk
  have h3 : q₀.card < 3 := by
    by_contra h
    exact hv (valid_G2_of_three_le (not_lt.1 h))
  have h2 : q₀.card = 2 := by
    have := two_le_card q₀
    omega
  have hc : Nat.card (adjointGroup .G2 k) = 12096 :=
    CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two (hk.trans h2)
  rw [hc]
  by_cases hp3 : p = 3
  · exfalso
    apply h8
    refine ⟨hp3, ?_⟩
    rw [hqq, h2, hp3]
    norm_num
  · exact not_sq_dvd_card_G2_two hp (five_le_of_prime_ne_two_three hp hp2 hp3)

end G2Fix


end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
