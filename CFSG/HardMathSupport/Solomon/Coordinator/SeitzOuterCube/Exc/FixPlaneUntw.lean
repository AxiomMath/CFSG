module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.Basic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FixedGroup
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.OutRank
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Untwisted
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FixedGroupE7
public import CFSG.HardMathSupport.Lang.E6Descent.FixedE6
public import CFSG.LieType.SeitzGeneration.ExcRankVacuous

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP
  CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

theorem exists_primePower_fixSubfield {q : PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card) (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p) :
    ∃ q₀ : PrimePower, q₀.p = q.p ∧ q₀.card = Nat.card (fixSubfield σ) ∧
      q.card = q₀.card ^ p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield q.prime_p q.exponent_pos hK' σ
  rw [hσ] at hdvd hcard
  have hpos : 0 < q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hdvd) hp.pos
  refine ⟨⟨q.p, q.exponent / p, q.prime_p, hpos⟩, rfl, ?_, ?_⟩
  · rw [PrimePower.card_def]
    exact hcard.symm
  · rw [PrimePower.card_def q, PrimePower.card_def ⟨q.p, q.exponent / p, q.prime_p, hpos⟩, ← pow_mul,
      Nat.div_mul_cancel hdvd]

section Bridge


theorem catEquiv_adjointGroup_of_card {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = q.card) : Nonempty (Cat ⟨c q, hv⟩ ≃* ↥(adjointGroup τ K)) := by
  obtain ⟨φ⟩ := hB q hv K hK
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

@[expose] def StdDescent (τ : Tag) (K : Type) [Field K] (p : ℕ) : Prop :=
  ∀ α : MulAut ↥(adjointGroup τ K), IsOuterOfOrder p α →
    ∃ (ψ : MulAut ↥(adjointGroup τ K)) (σ : K ≃+* K), orderOf σ = p ∧
      ψ * α * ψ⁻¹ = entrywiseAdjointAut τ σ

theorem stdDescent_of_fieldDescentAt {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (h : CFSG.AGLEmbedding.SeitzEqTwo.FieldDescentAt τ K p) : StdDescent τ K p := by
  intro α hα
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hord, hout⟩ := hα
  have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
  have hα' : α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range :=
    fun ⟨g, hg⟩ => hout g hg.symm
  obtain ⟨T, r, j, ψ, hTo, hj, hψ⟩ := h α hαp hα'
  have hαe : α = ψ⁻¹ * (entrywiseAdjointAut τ T) ^ j * ψ := by
    have h1 : α ^ r = ψ⁻¹ * entrywiseAdjointAut τ T * ψ := by rw [← hψ]; group
    rw [← hj, h1, show ψ⁻¹ * entrywiseAdjointAut τ T * ψ =
      ψ⁻¹ * entrywiseAdjointAut τ T * ψ⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
  have hTj : orderOf (T ^ j) = p := by
    have hTjp : (T ^ j) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hTo, pow_orderOf_eq_one, one_pow]
    refine orderOf_eq_prime hTjp fun h1 => ?_
    have : α = 1 := by
      rw [hαe, ← entrywiseAdjointAut_pow, h1, entrywiseAdjointAut_one]; group
    have h0 : orderOf α = 1 := by rw [this]; exact orderOf_one
    have := hp.one_lt
    omega
  refine ⟨ψ, T ^ j, hTj, ?_⟩
  rw [hαe, entrywiseAdjointAut_pow]
  group

theorem fixPlaneGen_untw_of_data (hLow : ExcInnerLowPlanes) {τ : Tag}
    {c : PrimePower → LieTypeIndex} (hB : Even.UntwistedBridgeAll τ c)
    (hnc : ∀ q, ¬ IsClassicalIndex (c q)) (hex : ∀ q p, ¬ IsD2SeitzException p (c q))
    (hchar : ∀ q, (c q).characteristic = q.p)
    (hinj : ∀ (q : PrimePower) (hv : (c q).Valid),
      Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)))
    {q : PrimePower} {K : Type} [Field K] [Finite K] (hK : Nat.card K = q.card) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) (hrank : RankLE2 p (adjointGroup τ K))
    (hsmall : ∀ q₀ : PrimePower, q.card = q₀.card ^ p → ¬ (c q₀).Valid →
      ∀ (k : Type) [Field k] [Finite k], Nat.card k = q₀.card →
        ¬ p ^ 2 ∣ Nat.card ↥(adjointGroup τ k))
    (hdesc : StdDescent τ K p)
    (hΓJ : ∀ σ : K ≃+* K, orderOf σ = p → entrywiseFixedGroup τ σ = fixedFieldImage τ σ) :
    FixPlaneGen ↥(adjointGroup τ K) p := by
  refine fixPlaneGen_of_standard_cat ⊤
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut τ σ} ?_ ?_
  · intro α hα
    obtain ⟨ψ, σ, hσ, h⟩ := hdesc α hα
    refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut τ σ, ⟨σ, hσ, rfl⟩, ?_⟩
    rw [← h]
    group
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨q₀, hq₀p, hq₀card, hq₀pow⟩ := exists_primePower_fixSubfield hK σ hp hσ
  have e₁ := ExcOuterLeOne.fixedEquivOfEq σ (hΓJ σ hσ)
  by_cases hv : (c q₀).Valid
  · obtain ⟨e₂⟩ := catEquiv_adjointGroup_of_card hB q₀ hv (fixSubfield σ) hq₀card.symm
    refine ⟨Cat ⟨c q₀, hv⟩, inferInstance, e₁.trans e₂.symm, ?_⟩
    intro B hBa hBc
    exact closure_centralizers_of_excInnerLow hLow (hnc q₀) hp hp2
      (by show p ≠ (c q₀).characteristic; rw [hchar, hq₀p]; exact hpq) (hex q₀ p)
      (hinj q₀ hv) (rankLE2_of_equiv_fixed (e₁.trans e₂.symm) hrank) B hBa hBc
  · refine ⟨↥(fixedSubgroup (entrywiseAdjointAut τ σ)), inferInstance, MulEquiv.refl _, ?_⟩
    intro B hBa hBc
    exfalso
    refine hsmall q₀ hq₀pow hv (fixSubfield σ) hq₀card.symm ?_
    rw [← Nat.card_congr e₁.toEquiv, ← hBc]
    exact Subgroup.card_subgroup_dvd_card B

theorem fixPlaneGen_F4 (hLow : ExcInnerLowPlanes) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hrank : RankLE2 p (adjointGroup Tag.F4 K)) : FixPlaneGen ↥(adjointGroup Tag.F4 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  exact fixPlaneGen_untw_of_data hLow Even.chevalleyBridgesAll.f4
    (fun q => (isChevalleyExcIndex_F4 q).not_classical)
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_F4 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
    (fun q hv => conj_injective_cat_F4 q hv) hK hp hp2 hpq hrank
    (fun q₀ _ h => absurd (by simp) h)
    (stdDescent_of_fieldDescentAt hp
      (CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_F4 q.prime_p q.exponent_pos hK' hp hp2))
    (fun σ _ => ExcOuterLeOne.entrywiseFixedGroup_F4_eq σ)

theorem fixPlaneGen_E6 (hLow : ExcInnerLowPlanes) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hrank : RankLE2 p (adjointGroup Tag.E6 K)) : FixPlaneGen ↥(adjointGroup Tag.E6 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp2 : p ≠ 2 := by omega
  exact fixPlaneGen_untw_of_data hLow Even.chevalleyBridgesAll.e6
    (fun q => (isChevalleyExcIndex_E6 q).not_classical)
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E6 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
    (fun q hv => conj_injective_cat_E6 q hv) hK hp hp2 hpq hrank
    (fun q₀ _ h => absurd (by simp) h)
    (stdDescent_of_fieldDescentAt hp (CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (τ := .E6) (Or.inl rfl) q.exponent_pos hK' hp
      hp2 (ExcOuterLeOne.not_dvd_det_cartan_E (Or.inl rfl) hp hp3)))
    (fun σ hσ => CFSG.HardMathSupport.Lang.E6Descent.entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow
      σ (hσ ▸ pow_orderOf_eq_one σ) ((Nat.coprime_primes hp Nat.prime_three).2 (by omega)))

theorem fixPlaneGen_E7 (hLow : ExcInnerLowPlanes) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hrank : RankLE2 p (adjointGroup Tag.E7 K)) : FixPlaneGen ↥(adjointGroup Tag.E7 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp2 : p ≠ 2 := by omega
  exact fixPlaneGen_untw_of_data hLow Even.chevalleyBridgesAll.e7
    (fun q => (isChevalleyExcIndex_E7 q).not_classical)
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E7 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
    (fun q hv => conj_injective_cat_E7 q hv) hK hp hp2 hpq hrank
    (fun q₀ _ h => absurd (by simp) h)
    (stdDescent_of_fieldDescentAt hp (CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (τ := .E7) (Or.inr (Or.inl rfl))
      q.exponent_pos hK' hp hp2 (ExcOuterLeOne.not_dvd_det_cartan_E (Or.inr (Or.inl rfl)) hp hp3)))
    (fun σ hσ => ExcOuterLeOne.entrywiseFixedGroup_E7_eq_of_pow σ hp hp3
      (hσ ▸ pow_orderOf_eq_one σ))

theorem fixPlaneGen_E8 (hLow : ExcInnerLowPlanes) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hrank : RankLE2 p (adjointGroup Tag.E8 K)) : FixPlaneGen ↥(adjointGroup Tag.E8 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp2 : p ≠ 2 := by omega
  exact fixPlaneGen_untw_of_data hLow Even.chevalleyBridgesAll.e8
    (fun q => (isChevalleyExcIndex_E8 q).not_classical)
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E8 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
    (fun q hv => conj_injective_cat_E8 q hv) hK hp hp2 hpq hrank
    (fun q₀ _ h => absurd (by simp) h)
    (stdDescent_of_fieldDescentAt hp (CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (τ := .E8) (Or.inr (Or.inr rfl))
      q.exponent_pos hK' hp hp2 (ExcOuterLeOne.not_dvd_det_cartan_E (Or.inr (Or.inr rfl)) hp hp3)))
    (fun σ _ => ExcOuterLeOne.entrywiseFixedGroup_E8_eq σ)

end Bridge

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
