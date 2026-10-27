module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighField
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneTw
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneUntw
public import CFSG.LieType.SeitzGeneration.ExcSeitzWide

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

@[expose] def SeitzGoodOuterHighE6Three : Prop :=
  SeitzGoodOuterHighAt fun d p =>
    p = 3 ∧ ((∃ q : PrimePower, d.1 = .E6 q ∧ 3 ∣ q.card - 1) ∨
      (∃ q : PrimePower, d.1 = .twistedE6 q))

section Families

set_option linter.unusedSectionVars false

theorem fixPlaneGen_untw_kfact (hS : KFactSeitzRankTwo) {τ : Tag}
    {c : PrimePower → LieTypeIndex} (hB : Even.UntwistedBridgeAll τ c)
    (hex : ∀ q p, ¬ IsD2SeitzException p (c q)) (hchar : ∀ q, (c q).characteristic = q.p)
    (hinj : ∀ (q : PrimePower) (hv : (c q).Valid),
      Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)))
    {q : PrimePower} {K : Type} [Field K] [Finite K] (hK : Nat.card K = q.card) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
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
    exact closure_centralizers_cat_of_kfact hS hp hp2
      (by show p ≠ (c q₀).characteristic; rw [hchar, hq₀p]; exact hpq) (hex q₀ p)
      (hinj q₀ hv) B hBa hBc
  · refine ⟨↥(fixedSubgroup (entrywiseAdjointAut τ σ)), inferInstance, MulEquiv.refl _, ?_⟩
    intro B hBa hBc
    exfalso
    refine hsmall q₀ hq₀pow hv (fixSubfield σ) hq₀card.symm ?_
    rw [← Nat.card_congr e₁.toEquiv, ← hBc]
    exact Subgroup.card_subgroup_dvd_card B

theorem fixPlaneGen_F4_kfact (hS : KFactSeitzRankTwo) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) :
    FixPlaneGen ↥(adjointGroup Tag.F4 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  exact fixPlaneGen_untw_kfact hS Even.chevalleyBridgesAll.f4
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_F4 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
    (fun q hv => conj_injective_cat_F4 q hv) hK hp hp2 hpq
    (fun q₀ _ h => absurd (by simp) h)
    (stdDescent_of_fieldDescentAt hp
      (CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_F4 q.prime_p q.exponent_pos hK' hp hp2))
    (fun σ _ => ExcOuterLeOne.entrywiseFixedGroup_F4_eq σ)

theorem fixPlaneGen_E6_kfact (hS : KFactSeitzRankTwo) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p) :
    FixPlaneGen ↥(adjointGroup Tag.E6 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp2 : p ≠ 2 := by omega
  exact fixPlaneGen_untw_kfact hS Even.chevalleyBridgesAll.e6
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E6 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
    (fun q hv => conj_injective_cat_E6 q hv) hK hp hp2 hpq
    (fun q₀ _ h => absurd (by simp) h)
    (stdDescent_of_fieldDescentAt hp (CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (τ := .E6)
      (Or.inl rfl) q.exponent_pos hK' hp hp2
      (ExcOuterLeOne.not_dvd_det_cartan_E (Or.inl rfl) hp hp3)))
    (fun σ hσ =>
      CFSG.HardMathSupport.Lang.E6Descent.entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow
        σ (hσ ▸ pow_orderOf_eq_one σ) ((Nat.coprime_primes hp Nat.prime_three).2 (by omega)))

theorem fixPlaneGen_E7_kfact (hS : KFactSeitzRankTwo) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) :
    FixPlaneGen ↥(adjointGroup Tag.E7 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact fixPlaneGen_untw_kfact hS Even.chevalleyBridgesAll.e7
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E7 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
    (fun q hv => conj_injective_cat_E7 q hv) hK hp hp2 hpq
    (fun q₀ _ h => absurd (by simp) h)
    (stdDescent_of_fieldDescentAt hp (CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (τ := .E7)
      (Or.inr (Or.inl rfl)) q.exponent_pos hK' hp hp2
      (ExcOuterLeOne.not_dvd_det_cartan_E_of_odd (Or.inl rfl) hp hp2)))
    (fun σ hσ => ExcOuterLeOne.entrywiseFixedGroup_E7_eq_of_odd_pow σ hp hp2
      (hσ ▸ pow_orderOf_eq_one σ))

theorem fixPlaneGen_E8_kfact (hS : KFactSeitzRankTwo) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) :
    FixPlaneGen ↥(adjointGroup Tag.E8 K) p := by
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact fixPlaneGen_untw_kfact hS Even.chevalleyBridgesAll.e8
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E8 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
    (fun q hv => conj_injective_cat_E8 q hv) hK hp hp2 hpq
    (fun q₀ _ h => absurd (by simp) h)
    (stdDescent_of_fieldDescentAt hp (CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_E (τ := .E8)
      (Or.inr (Or.inr rfl)) q.exponent_pos hK' hp hp2
      (ExcOuterLeOne.not_dvd_det_cartan_E_of_odd (Or.inr rfl) hp hp2)))
    (fun σ _ => ExcOuterLeOne.entrywiseFixedGroup_E8_eq σ)

theorem fixPlaneGen_twE6_kfact (hS : KFactSeitzRankTwo) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card ^ 2) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ q.card)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p) :
    FixPlaneGen ↥(twistedE6RootGroup K σ) p := by
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 2 := by rw [hK, PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [hσ, PrimePower.card_def]
  have hp2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  refine fixPlaneGen_of_standard_cat ⊤
    {g | ∃ η : K ≃+* K, orderOf η = p ∧ g = fieldActor (t := TwistTag.E6) σ η} ?_ ?_
  · intro α hα
    obtain ⟨ψ, η, hη, h⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_conj_fieldActor_twE6
      q.prime_p q.exponent_pos hK' σ hσ' hp hp3 α hα
    refine ⟨ψ⁻¹, Subgroup.mem_top _, fieldActor (t := TwistTag.E6) σ η, ⟨η, hη, rfl⟩, ?_⟩
    rw [← h]
    group
  · rintro _ ⟨η, hη, rfl⟩
    obtain ⟨q₀, hq₀p, hqq, hF⟩ :=
      exists_primePower_fixSubfield_twisted (m := 2) (by norm_num) hK η hp hp2 hη
    have hv₀ : (LieTypeIndex.twistedE6 q₀).Valid := by simp
    obtain ⟨e⟩ := twE6_fixedSubgroup_equiv_cat hqq hp hp3 hK σ hσ hη hF hv₀
    refine ⟨Cat ⟨.twistedE6 q₀, hv₀⟩, inferInstance, e, ?_⟩
    intro B hBa hBc
    exact closure_centralizers_cat_of_kfact hS hp (by omega)
      (by
        show p ≠ (LieTypeIndex.twistedE6 q₀).characteristic
        rw [LieTypeIndex.characteristic_twistedE6, hq₀p]
        exact hpq)
      (not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_twistedE6 q₀))
      (conj_injective_cat_twE6 q₀ hv₀) B hBa hBc

theorem pair_F4 (hS : KFactSeitzRankTwo) {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) :
    FieldAutData (Cat ⟨.F4 q, hv⟩) p ∧ FixPlaneGen (Cat ⟨.F4 q, hv⟩) p := by
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  exact ⟨(ExcOuterLeOne.fieldAutData_F4_of_odd hp hp2 hpK).of_mulEquiv e hp,
    (fixPlaneGen_F4_kfact hS hK hp hp2 hpq).of_mulEquiv e hp⟩

theorem pair_E6 (hS : KFactSeitzRankTwo) {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p) :
    FieldAutData (Cat ⟨.E6 q, hv⟩) p ∧ FixPlaneGen (Cat ⟨.E6 q, hv⟩) p := by
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  exact ⟨(fieldAutData_E6_of_subfieldMaximalAll ExcOuterLeOne.subfieldMaximalAll_E6 hp hp5
      hpK).of_mulEquiv e hp,
    (fixPlaneGen_E6_kfact hS hK hp (by omega) hpq).of_mulEquiv e hp⟩

theorem pair_E7 (hS : KFactSeitzRankTwo) {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) :
    FieldAutData (Cat ⟨.E7 q, hv⟩) p ∧ FixPlaneGen (Cat ⟨.E7 q, hv⟩) p := by
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  exact ⟨(ExcOuterLeOne.fieldAutData_E7_of_odd hp hp2 hpK).of_mulEquiv e hp,
    (fixPlaneGen_E7_kfact hS hK hp hp2 hpq).of_mulEquiv e hp⟩

theorem pair_E8 (hS : KFactSeitzRankTwo) {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) :
    FieldAutData (Cat ⟨.E8 q, hv⟩) p ∧ FixPlaneGen (Cat ⟨.E8 q, hv⟩) p := by
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  exact ⟨(ExcOuterLeOne.fieldAutData_E8_of_odd hp hp2 hpK).of_mulEquiv e hp,
    (fixPlaneGen_E8_kfact hS hK hp hp2 hpq).of_mulEquiv e hp⟩

theorem pair_twE6 (hS : KFactSeitzRankTwo) {q : PrimePower}
    (hv : (LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) :
    FieldAutData (Cat ⟨.twistedE6 q, hv⟩) p ∧ FixPlaneGen (Cat ⟨.twistedE6 q, hv⟩) p := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _
    q.prime_p.ne_zero))
  have hK' : Nat.card K = q.card ^ 2 := by rw [hK, PrimePower.card_def]
  have hσ' : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ, PrimePower.card_def]
  exact ⟨(fieldAutData_twE6_of_subfieldMaximalAll ExcOuterLeOne.subfieldMaximalAllTwE6
      q.prime_p q.exponent_pos hK σ hσ hp hp5 hpq).of_mulEquiv e hp,
    (fixPlaneGen_twE6_kfact hS hK' σ hσ' hp (by omega) hpq).of_mulEquiv e hp⟩

section E6Three

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Fischer

theorem cubeDescent_of_not_dvd {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (h : ¬ 3 ∣ Nat.card (fixSubfield σ) - 1) : ExcWideThree.CubeDescent σ := by
  intro b d _
  have hcop : (Nat.card (fixSubfield σ)ˣ).Coprime 3 := by
    rw [Nat.card_units]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h)
  refine ⟨(powCoprime hcop).symm b, ?_⟩
  have h1 := (powCoprime hcop).apply_symm_apply b
  rw [powCoprime_apply] at h1
  exact h1.symm

theorem not_dvd_card_fixSubfield_sub_one {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ : orderOf σ = 3) (h : ¬ 3 ∣ Nat.card K - 1) : ¬ 3 ∣ Nat.card (fixSubfield σ) - 1 := by
  intro h3
  apply h
  have hcard := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ
  rw [hσ] at hcard
  rw [hcard]
  have h1 : Nat.card (fixSubfield σ) - 1 ∣ Nat.card (fixSubfield σ) ^ 3 - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (Nat.card (fixSubfield σ)) 1 3
  exact h3.trans h1

theorem fieldAutData_E6_three_of_not_dvd {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hnd : ¬ 3 ∣ Nat.card K - 1) : FieldAutData (adjointGroup Tag.E6 K) 3 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  have hdiag : e6Inndiag K = innerAut (adjointGroup Tag.E6 K) :=
    e6Inndiag_eq_innerAut_of_not_dvd K hnd
  obtain ⟨Θ, -, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hmax := subfieldMaximalAllThree_of_E .E6 (Or.inl rfl)
  refine fieldAutData_of_standard ⊤
    {g | ∃ σ : K ≃+* K, orderOf σ = 3 ∧ g = entrywiseAdjointAut Tag.E6 σ} ?_ ?_ ?_ ?_ ?_
  · intro E' hE' hEc'
    have := hE'
    obtain ⟨ι, hιE, hι1, hιker⟩ := ExcWideThree.exists_ne_one_mem_ker_of_plane Tag.E6
      (Or.inl rfl) Nat.prime_three (by norm_num) Θ E' hEc'
    have hιdiag : ι ∈ e6Inndiag K := (ExcWideThree.mem_ker_iff_mem_e6Inndiag Θ hker ι).1 hιker
    rw [hdiag] at hιdiag
    obtain ⟨g, rfl⟩ := hιdiag
    exact ⟨g, fun hg => hι1 (by rw [hg, map_one]), hιE⟩
  · intro α hα
    obtain ⟨hαo, hαin⟩ := hα
    have hα3 : α ^ 3 = 1 := by rw [← hαo]; exact pow_orderOf_eq_one α
    have hαdiag : α ∉ e6Inndiag K := by
      rw [hdiag]
      rintro ⟨g, hg⟩
      exact hαin g hg.symm
    obtain ⟨σ, hσ, -, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
      Nat.prime_three (by norm_num) hα3 hαdiag
    refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut Tag.E6 σ, ⟨σ, hσ, rfl⟩, ?_⟩
    rw [← hψ]
    group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := Tag.E6))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσ hτ)
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    exact ExcWideThree.eq_one_of_central_fixed_E6 σ
      (cubeDescent_of_not_dvd σ (not_dvd_card_fixSubfield_sub_one hσ hnd)) hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d _ hne
    exact Or.inl (closure_pair_eq_top_of_maximal
      (hmax K σ 3 rfl (fun h => hK3 h.symm) hσ) d hne)

theorem fixPlaneGen_E6_three_kfact (hS : KFactSeitzRankTwo) {q : PrimePower} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q.card) (hpq : 3 ≠ q.p)
    (hnd : ¬ 3 ∣ Nat.card K - 1) : FixPlaneGen ↥(adjointGroup Tag.E6 K) 3 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK' : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have hdiag : e6Inndiag K = innerAut (adjointGroup Tag.E6 K) :=
    e6Inndiag_eq_innerAut_of_not_dvd K hnd
  refine fixPlaneGen_untw_kfact hS Even.chevalleyBridgesAll.e6
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E6 q))
    (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
    (fun q hv => conj_injective_cat_E6 q hv) hK Nat.prime_three (by norm_num) hpq
    (fun q₀ _ h => absurd (by simp) h) ?_
    (fun σ hσ => ExcWideThree.entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow σ
      (cubeDescent_of_not_dvd σ (not_dvd_card_fixSubfield_sub_one hσ hnd)))
  intro α hα
  obtain ⟨hαo, hαin⟩ := hα
  have hα3 : α ^ 3 = 1 := by rw [← hαo]; exact pow_orderOf_eq_one α
  have hαdiag : α ∉ e6Inndiag K := by
    rw [hdiag]
    rintro ⟨g, hg⟩
    exact hαin g hg.symm
  obtain ⟨σ, hσ, -, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK'
    Nat.prime_three (by norm_num) hα3 hαdiag
  exact ⟨ψ, σ, hσ, hψ⟩

theorem pair_E6_three (hS : KFactSeitzRankTwo) {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid)
    (hpq : 3 ≠ q.p) (hnd : ¬ 3 ∣ q.card - 1) :
    FieldAutData (CFSG.LieType.SeitzGeneration.Cat ⟨.E6 q, hv⟩) 3 ∧
      FixPlaneGen (CFSG.LieType.SeitzGeneration.Cat ⟨.E6 q, hv⟩) 3 := by
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : ringChar K ≠ 3 := by rw [ringChar.eq K q.p]; exact fun h => hpq h.symm
  have hndK : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; exact hnd
  exact ⟨(fieldAutData_E6_three_of_not_dvd hpK hndK).of_mulEquiv e Nat.prime_three,
    (fixPlaneGen_E6_three_kfact hS hK hpq hndK).of_mulEquiv e Nat.prime_three⟩

end E6Three

end Families

section Assembly

set_option linter.unusedSectionVars false

theorem seitzGoodOuterHighAt_excRest (hS : KFactSeitzRankTwo) :
    SeitzGoodOuterHighAt fun d p => ¬ IsClassicalIndex d.1 ∧
      ¬ (p = 3 ∧ ((∃ q : PrimePower, d.1 = .E6 q ∧ 3 ∣ q.card - 1) ∨
        (∃ q : PrimePower, d.1 = .twistedE6 q))) := by
  refine SeitzGoodOuterHighAt.of_pair ?_
  rintro ⟨d, hv⟩ p ⟨hnc, hne⟩ hp hp2 hpd - - - ⟨F, hFa, hFc⟩
  rcases (not_isClassicalIndex_iff d).1 hnc with hch | hree
  · rcases hch with (hg2 | hf4 | he6 | he7 | he8) | (htri | htw)
    · exact (SeitzHyperGoodInAux.no_cube_G2 (d := ⟨d, hv⟩) hg2 hp hp2 hpd hFa hFc).elim
    · obtain ⟨q, rfl⟩ := hf4
      exact pair_F4 hS hv hp hp2 (by simpa using hpd)
    · obtain ⟨q, rfl⟩ := he6
      by_cases hp3 : p = 3
      · subst hp3
        exact pair_E6_three hS hv (by simpa using hpd) fun h => hne ⟨rfl, Or.inl ⟨q, rfl, h⟩⟩
      · exact pair_E6 hS hv hp (five_le_of_prime_ne_two_three hp hp2 hp3) (by simpa using hpd)
    · obtain ⟨q, rfl⟩ := he7
      exact pair_E7 hS hv hp hp2 (by simpa using hpd)
    · obtain ⟨q, rfl⟩ := he8
      exact pair_E8 hS hv hp hp2 (by simpa using hpd)
    · exact (SeitzHyperGoodInAux.no_cube_triality (d := ⟨d, hv⟩) htri hp hp2 hpd hFa hFc).elim
    · obtain ⟨q, rfl⟩ := htw
      have hp3 : p ≠ 3 := fun h => hne ⟨h, Or.inr ⟨q, rfl⟩⟩
      exact pair_twE6 hS hv hp (five_le_of_prime_ne_two_three hp hp2 hp3) (by simpa using hpd)
  · exact (SeitzHyperGoodInAux.no_cube_reeType (d := ⟨d, hv⟩) hree hp hp2 hpd hFa hFc).elim

theorem seitzGoodOuterHighExceptional_of_e6Three (hS : KFactSeitzRankTwo)
    (hE6 : SeitzGoodOuterHighE6Three) : SeitzGoodOuterHighExceptional := by
  refine seitzGoodOuterHighFor_of_at (SeitzGoodOuterHighAt.of_cover ?_ hE6
    (seitzGoodOuterHighAt_excRest hS))
  intro d p hnc
  by_cases h : p = 3 ∧ ((∃ q : PrimePower, d.1 = .E6 q ∧ 3 ∣ q.card - 1) ∨
      (∃ q : PrimePower, d.1 = .twistedE6 q))
  · exact Or.inl h
  · exact Or.inr ⟨hnc, h⟩

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

end
