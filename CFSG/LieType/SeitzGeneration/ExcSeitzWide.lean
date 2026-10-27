module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddPower
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddMain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Maximal
public import CFSG.LieType.SeitzGeneration.ExcSeitzGaps
public import CFSG.LieType.SeitzGeneration.HyperExReeType

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

section

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.RankThree.PartOne.CTP CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent


theorem fieldAutData_twE6_of_subfieldMaximalAll (h : SubfieldMaximalAllTwE6) {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) :
    FieldAutData ↥(twistedE6RootGroup K σ) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hp3 : 3 < p := by omega
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (twistedE6RootGroup K σ) := Subtype.finite
  refine fieldAutData_of_standard ⊤
    {g | ∃ η : K ≃+* K, orderOf η = p ∧ g = fieldActor σ η} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_inner_mem_of_plane_twE6 hℓ hf hK σ hσ hp hp3 E hEc
  · intro α hα
    obtain ⟨ψ, η, hη, h⟩ := exists_conj_fieldActor_twE6 hℓ hf hK σ hσ hp hp3 α hα
    refine ⟨ψ⁻¹, Subgroup.mem_top _, fieldActor σ η, ⟨η, hη, rfl⟩, ?_⟩
    rw [← h]
    group
  · rintro _ ⟨η, hη, rfl⟩ _ ⟨η', hη', rfl⟩
    have := fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.E6) σ)
      (zpowers_ringEquiv_eq_of_orderOf hℓ (by omega : 1 ≤ 2 * f) hK' hη hη')
    simpa only [fieldActorHom_apply] using this
  · rintro _ ⟨η, hη, rfl⟩ _ x hx hc
    exact eq_one_of_central_fixed_twE6 hℓ hf hK σ hσ hp hp3 hη hx hc
  · rintro _ ⟨η, hη, rfl⟩ d _ hne
    exact Or.inl (closure_pair_eq_top_of_maximal (h ℓ f hℓ hf K hK σ hσ p hp hp5 hpℓ η hη) d hne)

end

section

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.RankThree.PartOne.CTP CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent


open TauCeti (PrimePower LieTypeIndex) 
in
theorem seitzExcOuterWideFive_of_fieldAutData {τ : Tag} {c : PrimePower → LieTypeIndex}
    {F : LieTypeIndex → Prop} {X : PrimePower → Prop}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q, (c q).characteristic = q.p)
    (hinj : ∀ (K : Type) [Field K] [Finite K],
      Function.Injective (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)))
    (hF : ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → p ≠ ringChar K →
      FieldAutData ↥(adjointGroup τ K) p) :
    SeitzExcOuterWideForAt F
      (fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = c q ∧ X q) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, -, hp5, q, hdq, -⟩
  obtain rfl : d = c q := hdq
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hpq : p ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  exact planeGen_outer_of_fieldAutData (hinj K) e hp (hF K p hp hp5 hpK) hE hc hout

end

section

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.RankThree.PartOne.CTP CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent


theorem fieldAutData_E6_of_subfieldMaximalAll (h : SubfieldMaximalAll .E6) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.E6 K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hp3 : 3 < p := by omega
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  refine fieldAutData_of_standard ⊤
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut Tag.E6 σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_inner_mem_of_plane_E6 hp hp3 E hEc
  · intro α hα
    obtain ⟨ψ, σ, hσ, h⟩ := exists_conj_entrywise_E6 hp hp3 α hα
    refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut Tag.E6 σ, ⟨σ, hσ, rfl⟩, ?_⟩
    rw [← h]
    group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := Tag.E6))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσ hτ)
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    exact eq_one_of_central_fixed_E6 σ (hσ ▸ pow_orderOf_eq_one σ) hcop hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d _ hne
    exact Or.inl (closure_pair_eq_top_of_maximal (h K σ p hp hp5 hpK hσ) d hne)

end

section

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.RankThree.PartOne.CTP CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent


theorem fieldAutData_E_of_subfieldMaximalAll (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hΓJ : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p : ℕ), p.Prime → 3 < p →
      σ ^ p = 1 → entrywiseFixedGroup τ σ = fixedFieldImage τ σ)
    (h : SubfieldMaximalAll τ) {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup τ K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hdet := not_dvd_det_cartan_E hτ hp hp3
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  refine fieldAutData_of_standard ⊤
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut τ σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_inner_mem_of_plane_E τ hτ hp hp3 E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
    have hα' : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup τ K) :=
      fun ⟨g, hg⟩ => hout g hg.symm
    obtain ⟨d, T, r, j, ψ, -, hTo, -, hj, hψ⟩ :=
      exists_conj_entrywise_of_outer_E τ hτ n.pos K hK hp hp2 hdet α hαp hα'
    have hαe : α = ψ⁻¹ * (entrywiseAdjointAut τ T) ^ j * ψ := by
      have h1 : α ^ r = ψ⁻¹ * entrywiseAdjointAut τ T * ψ := by rw [← hψ]; group
      rw [← hj, h1, show ψ⁻¹ * entrywiseAdjointAut τ T * ψ =
        ψ⁻¹ * entrywiseAdjointAut τ T * ψ⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
    have hTj : orderOf (T ^ j) = p := by
      have hTjp : (T ^ j) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, ← hTo, pow_orderOf_eq_one, one_pow]
      refine orderOf_eq_prime hTjp fun h1 => ?_
      have : α = 1 := by rw [hαe, ← entrywiseAdjointAut_pow, h1, entrywiseAdjointAut_one]; group
      have h0 : orderOf α = 1 := by rw [this]; exact orderOf_one
      omega
    refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut τ (T ^ j), ⟨T ^ j, hTj, rfl⟩, ?_⟩
    rw [hαe, entrywiseAdjointAut_pow]
    group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ', hτ', rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := τ))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσ hτ')
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    exact eq_one_of_central_fixed_of_eq σ (hΓJ K σ p hp hp3 (hσ ▸ pow_orderOf_eq_one σ)) hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d _ hne
    exact Or.inl (closure_pair_eq_top_of_maximal (h K σ p hp hp5 hpK hσ) d hne)

theorem fieldAutData_F4_of_subfieldMaximalAll (h : SubfieldMaximalAll .F4) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.F4 K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hp2 : p ≠ 2 := by omega
  have hdesc := CFSG.AGLEmbedding.SeitzEqTwo.fieldDescentAt_F4 (K := K) hℓ n.pos hK hp hp2
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (adjointGroup Tag.F4 K) := Subtype.finite
  refine fieldAutData_of_standard ⊤
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut Tag.F4 σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact CFSG.RankThree.PartOne.SEITZ2.exists_conj_mem_of_plane_of_cyclic_outer hp
      isCyclic_outer_F4 E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
    have hα' : α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range :=
      fun ⟨g, hg⟩ => hout g hg.symm
    obtain ⟨T, r, j, ψ, hTo, hj, hψ⟩ := hdesc α hαp hα'
    have hαe : α = ψ⁻¹ * (entrywiseAdjointAut Tag.F4 T) ^ j * ψ := by
      have h1 : α ^ r = ψ⁻¹ * entrywiseAdjointAut Tag.F4 T * ψ := by rw [← hψ]; group
      rw [← hj, h1, show ψ⁻¹ * entrywiseAdjointAut Tag.F4 T * ψ =
        ψ⁻¹ * entrywiseAdjointAut Tag.F4 T * ψ⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
    have hTj : orderOf (T ^ j) = p := by
      have hTjp : (T ^ j) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, ← hTo, pow_orderOf_eq_one, one_pow]
      refine orderOf_eq_prime hTjp fun h1 => ?_
      have : α = 1 := by
        rw [hαe, ← entrywiseAdjointAut_pow, h1, entrywiseAdjointAut_one]; group
      have h0 : orderOf α = 1 := by rw [this]; exact orderOf_one
      omega
    refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut Tag.F4 (T ^ j), ⟨T ^ j, hTj, rfl⟩, ?_⟩
    rw [hαe, entrywiseAdjointAut_pow]
    group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ', hτ', rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := Tag.F4))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσ hτ')
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    exact eq_one_of_central_fixed_of_eq σ (entrywiseFixedGroup_F4_eq σ) hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d _ hne
    exact Or.inl (closure_pair_eq_top_of_maximal (h K σ p hp hp5 hpK hσ) d hne)

open TauCeti (PrimePower LieTypeIndex) 
in
theorem seitzExcOuterWideE6_of_subfieldMaximalAll (h : SubfieldMaximalAll .E6) :
    SeitzExcOuterWideForAt IsE6Index
      (fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = LieTypeIndex.E6 q ∧ True) :=
  seitzExcOuterWideFive_of_fieldAutData (c := LieTypeIndex.E6) (X := fun _ => True)
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 LieTypeIndex.characteristic_E6
    (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
    fun _ _ _ _ hp hp5 hpK => fieldAutData_E6_of_subfieldMaximalAll h hp hp5 hpK

open TauCeti (PrimePower LieTypeIndex) 
in
theorem seitzExcOuterWideF4_of_subfieldMaximalAll (h : SubfieldMaximalAll .F4) :
    SeitzExcOuterWideForAt IsF4Index
      (fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = LieTypeIndex.F4 q ∧ ¬ (q.p = 2 ∧ q.exponent = 1)) :=
  seitzExcOuterWideFive_of_fieldAutData (c := LieTypeIndex.F4)
    (X := fun q => ¬ (q.p = 2 ∧ q.exponent = 1))
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 LieTypeIndex.characteristic_F4
    (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
    fun _ _ _ _ hp hp5 hpK => fieldAutData_F4_of_subfieldMaximalAll h hp hp5 hpK

open TauCeti (PrimePower LieTypeIndex) 
in
theorem seitzExcOuterWideE7_of_subfieldMaximalAll (h : SubfieldMaximalAll .E7) :
    SeitzExcOuterWideForAt IsE7Index
      (fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = LieTypeIndex.E7 q ∧ True) :=
  seitzExcOuterWideFive_of_fieldAutData (c := LieTypeIndex.E7) (X := fun _ => True)
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 LieTypeIndex.characteristic_E7
    (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
    fun _ _ _ _ hp hp5 hpK =>
      fieldAutData_E_of_subfieldMaximalAll .E7 (Or.inr (Or.inl rfl))
        (fun _ _ _ σ p hp hp3 hσp => entrywiseFixedGroup_E7_eq_of_pow σ hp hp3 hσp) h hp hp5 hpK

open TauCeti (PrimePower LieTypeIndex) 
in
theorem seitzExcOuterWideE8_of_subfieldMaximalAll (h : SubfieldMaximalAll .E8) :
    SeitzExcOuterWideForAt IsE8Index
      (fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = LieTypeIndex.E8 q ∧ True) :=
  seitzExcOuterWideFive_of_fieldAutData (c := LieTypeIndex.E8) (X := fun _ => True)
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 LieTypeIndex.characteristic_E8
    (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
    fun _ _ _ _ hp hp5 hpK =>
      fieldAutData_E_of_subfieldMaximalAll .E8 (Or.inr (Or.inr rfl))
        (fun _ _ _ σ _ _ _ _ => entrywiseFixedGroup_E8_eq σ) h hp hp5 hpK

open TauCeti (PrimePower LieTypeIndex) 
in
theorem seitzExcOuterWideTwE6_of_subfieldMaximalAll (h : SubfieldMaximalAllTwE6) :
    SeitzExcOuterWideForAt IsTwistedE6Index
      (fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = LieTypeIndex.twistedE6 q ∧ True) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, -, hp5, q, rfl, -⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpq : p ≠ q.p := by simpa [TauCeti.ValidLieTypeIndex.characteristic] using hpd
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    mulAut_conj_injective_of_center_eq_bot (center_graphFixedRootGroup_eq_bot σ.surjective)
  exact planeGen_outer_of_fieldAutData hinj e hp
    (fieldAutData_twE6_of_subfieldMaximalAll h q.prime_p q.exponent_pos hK σ hσ hp hp5 hpq) hE hc
    hout

end

section

open CFSG.TauCetiBridge TauCeti


theorem rankLE2_cat_G2_five (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p) : RankLE2 p (Cat ⟨.G2 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  exact RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_adjointGroup_G2 K hp hp5 hpK)

end

section

open CFSG.TauCetiBridge TauCeti


theorem seitzExcHighFive_of_top (h : SeitzExcHighForAt IsTopIndex PrimeRange.geFive) :
    SeitzExcHighFive := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, hnc, hp5, hr, hN⟩
  rcases (not_isClassicalIndex_iff d).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · obtain ⟨q, rfl⟩ := hd
    exact (hr (rankLE2_cat_G2_five q hv hp hp5 (by simpa using hpd))).elim
  · exact h ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, Or.inl hd, hp5, hr, hN⟩
  · exact h ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, Or.inr (Or.inl hd), hp5, hr, hN⟩
  · exact h ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, Or.inr (Or.inr (Or.inl hd)), hp5, hr, hN⟩
  · exact h ⟨d, hv⟩ p hp hp2 hpd hex E hE hc
      ⟨hi, Or.inr (Or.inr (Or.inr (Or.inl hd))), hp5, hr, hN⟩
  · obtain ⟨q, rfl⟩ := hd
    exact (hr (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_trialityD4 q hv hp hp5
      (by simpa using hpd))).elim
  · exact h ⟨d, hv⟩ p hp hp2 hpd hex E hE hc
      ⟨hi, Or.inr (Or.inr (Or.inr (Or.inr hd))), hp5, hr, hN⟩
  · obtain ⟨m, rfl⟩ := hd
    exact (not_innerPlane_suzuki hv hp hp2 hE hc hi).elim
  · obtain ⟨m, rfl⟩ := hd
    have h3 : p ≠ 3 := by
      have := hpd
      rwa [show (⟨TauCeti.LieTypeIndex.reeG2 m, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic
        = 3 from TauCeti.LieTypeIndex.characteristic_reeG2 m] at this
    exact (hr (rankLE2_cat_reeG2 hv hp hp2 h3)).elim
  · obtain ⟨m, rfl⟩ := hd
    exact (hr (rankLE2_cat_reeF4_five hv hp hp5)).elim
  · subst hd
    have h3 : p ≠ 3 := fun h => hex (Or.inl ⟨h, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)
    have h5 : p ≠ 5 := fun h => hex (Or.inr ⟨h, Or.inl rfl⟩)
    exact (no_plane_tits hv hp hp2 h3 h5 hc).elim

theorem seitzExcHighFive_of_families
    (hF4 : SeitzExcHighForAt IsF4Index PrimeRange.geFive)
    (hE6 : SeitzExcHighForAt IsE6Index PrimeRange.geFive)
    (hE7 : SeitzExcHighForAt IsE7Index PrimeRange.geFive)
    (hE8 : SeitzExcHighForAt IsE8Index PrimeRange.geFive)
    (hTw : SeitzExcHighForAt IsTwistedE6Index PrimeRange.geFive) : SeitzExcHighFive :=
  seitzExcHighFive_of_top (SeitzExcHighForAt.top_of_families hF4 hE6 hE7 hE8 hTw)

end

section

open CFSG.TauCetiBridge TauCeti


theorem seitzExcHighThree_of_top (h : SeitzExcHighForAt IsTopIndex PrimeRange.three) :
    SeitzExcHighThree := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hi, hnc, hp3, hr, hN⟩
  subst hp3
  rcases (not_isClassicalIndex_iff d).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · obtain ⟨q, rfl⟩ := hd
    exact (hr (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv
      (by simpa using hpd))).elim
  · exact h ⟨d, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hi, Or.inl hd, rfl, hr, hN⟩
  · exact h ⟨d, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hi, Or.inr (Or.inl hd), rfl, hr, hN⟩
  · exact h ⟨d, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hi, Or.inr (Or.inr (Or.inl hd)), rfl, hr, hN⟩
  · exact h ⟨d, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hi, Or.inr (Or.inr (Or.inr (Or.inl hd))), rfl, hr, hN⟩
  · obtain ⟨q, rfl⟩ := hd
    exact (hr (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv
      (fun h : q.p = 3 => hpd (by simpa using h.symm)))).elim
  · exact h ⟨d, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hi, Or.inr (Or.inr (Or.inr (Or.inr hd))), rfl, hr, hN⟩
  · obtain ⟨m, rfl⟩ := hd
    exact (not_innerPlane_suzuki hv hp hp2 hE hc hi).elim
  · obtain ⟨m, rfl⟩ := hd
    exact absurd (TauCeti.LieTypeIndex.characteristic_reeG2 m).symm hpd
  · obtain ⟨m, rfl⟩ := hd
    exact (hr (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv)).elim
  · subst hd
    exact (hex (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)).elim

theorem seitzExcHighThree_of_families
    (hF4 : SeitzExcHighForAt IsF4Index PrimeRange.three)
    (hE6 : SeitzExcHighForAt IsE6Index PrimeRange.three)
    (hE7 : SeitzExcHighForAt IsE7Index PrimeRange.three)
    (hE8 : SeitzExcHighForAt IsE8Index PrimeRange.three)
    (hTw : SeitzExcHighForAt IsTwistedE6Index PrimeRange.three) : SeitzExcHighThree :=
  seitzExcHighThree_of_top (SeitzExcHighForAt.top_of_families hF4 hE6 hE7 hE8 hTw)

end

section

open TauCeti CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP


theorem seitzExcOuterWide_suzuki_five : SeitzExcOuterWideForAt IsSuzukiIndex PrimeRange.geFive :=
  SeitzPlanes.mono (fun d p E hE => by
      obtain ⟨hout, -, ⟨m, hm⟩, hp5⟩ := hE
      exact ⟨hout, m, hm, hp5, trivial⟩)
    (seitzPlanes_outer_family (c := LieTypeIndex.suzuki) (P := fun _ _ => True)
      (fun _ hv => finite_isSimpleGroup_cat_suzuki hv)
      (fun m => ExtSeitzAtOuterFor.of_outer
        (SEITZ2.extSeitzAtOuter_suzuki_of_pair SEITZ10.subfieldPairSz_holds m)))

end

section

open TauCeti CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP


theorem seitzExcOuterWide_reeF4_five : SeitzExcOuterWideForAt IsReeF4Index PrimeRange.geFive :=
  SeitzPlanes.mono (fun d p E hE => by
      obtain ⟨hout, -, ⟨m, hm⟩, hp5⟩ := hE
      exact ⟨hout, m, hm, hp5, trivial⟩)
    (seitzPlanes_outer_family (c := LieTypeIndex.reeF4) (P := fun _ _ => True)
      (fun _ hv => finite_isSimpleGroup_cat_reeF4 hv)
      (fun m => ExtSeitzAtOuterFor.of_outer
        (SEITZ2.extSeitzAtOuter_reeF4_of_pair SEITZRF.subfieldPairReeF4_holds m)))

theorem seitzExcOuterWide_reeF4_three : SeitzExcOuterWideForAt IsReeF4Index PrimeRange.three := by
  have hpair := CFSG.RankThree.PartOne.SEITZRF.subfieldPairReeF4Three_holds
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨m, hm⟩, hp3⟩
  subst hm
  obtain ⟨hfin, hsimple⟩ := finite_isSimpleGroup_cat_reeF4 hv
  have : Fact p.Prime := ⟨hp⟩
  have hel : IsElementaryAbelian p ↥E := isElementaryAbelian_of_isElemAbelian hE
  have hnab := exists_noncommuting_of_isElementaryAbelian_aut hel hc
  obtain ⟨X, _, _, _, ha, hX, ⟨e⟩⟩ := CFSG.RankThree.PartOne.SEITZX.exists_reeGamma_model
    (K := Cat ⟨.reeF4 m, hv⟩) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have hd : FieldAutData (Cat ⟨.reeF4 m, hv⟩) p :=
    (CFSG.RankThree.PartOne.SEITZRF.fieldAutData_reeF4_three hpair hp hp3 ha hX).of_mulEquiv e hp
  rw [planeGen_iff_closure_fixUnion]
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc
    (fun hall => hout fun φ hφ => (hall φ hφ).elim fun g hg => ⟨g, hg.symm⟩)

theorem SeitzExcOuterWideThreeFamilies.toWideThree (h : SeitzExcOuterWideThreeFamilies) :
    SeitzExcOuterWideThree := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hP, hp3⟩
  rcases hP with hnc | hD4
  · rcases (not_isClassicalIndex_iff d).mp hnc with
      ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
    · exact h.g2 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp3⟩
    · exact h.f4 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp3⟩
    · exact h.e6 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp3⟩
    · exact h.e7 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp3⟩
    · exact h.e8 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp3⟩
    · exact h.triality ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp3⟩
    · exact h.twistedE6 ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp3⟩
    · obtain ⟨m, rfl⟩ := hd
      subst hp3
      exact (no_plane_suzuki_three hv hE hc).elim
    · obtain ⟨m, rfl⟩ := hd
      subst hp3
      exact absurd (TauCeti.LieTypeIndex.characteristic_reeG2 m).symm hpd
    · exact seitzExcOuterWide_reeF4_three ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp3⟩
    · subst hd
      subst hp3
      exact (hex (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)).elim
  · exact h.dFour ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hD4, hp3⟩

end

section

open TauCeti CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP


theorem extSeitzAtOuterFor_G2_all (q : PrimePower) : ExtSeitzAtOuterFor (.G2 q) fun _ => True :=
  extSeitzAtOuterFor_union (P₁ := fun _ => q.p = 2 ∨ (q.p ≠ 2 ∧ q.exponent = 1))
    (P₂ := fun _ => q.p ≠ 2 ∧ q.exponent ≠ 1)
    (fun _ _ _ _ => by
      by_cases h2 : q.p = 2
      · exact Or.inl (Or.inl h2)
      by_cases he : q.exponent = 1
      · exact Or.inl (Or.inr ⟨h2, he⟩)
      · exact Or.inr ⟨h2, he⟩)
    (extSeitzAtOuterFor_G2_proved q)
    (CFSG.HardMathSupport.Seitz.G2Noninner.extSeitzAtOuterFor_G2_oddPower
      CFSG.HardMathSupport.Seitz.G2Noninner.subfieldPairG2Odd q)

theorem seitzExcOuterWide_G2_five : SeitzExcOuterWideForAt IsG2Index PrimeRange.geFive :=
  SeitzPlanes.mono (fun d p E hE => by
      obtain ⟨hout, -, ⟨q, hq⟩, hp5⟩ := hE
      exact ⟨hout, q, hq, hp5, trivial⟩)
    (seitzPlanes_outer_family (c := LieTypeIndex.G2) (P := fun _ _ => True)
      (fun _ hv => finite_isSimpleGroup_cat_G2 hv) extSeitzAtOuterFor_G2_all)

theorem extSeitzAtOuterFor_trialityD4_all (q : PrimePower) :
    ExtSeitzAtOuterFor (.trialityD4 q) fun _ => True := by
  by_cases h : q.p = 2
  · exact extSeitzAtOuterFor_trialityD4_even h
  · exact ExtSeitzAtOuterFor.of_outer
      (CFSG.HardMathSupport.Seitz.TrialityOdd.extSeitzAtOuter_trialityD4_odd_of_pair
        CFSG.HardMathSupport.Seitz.TrialityOdd.subfieldPairD4Odd_proof h)

theorem seitzExcOuterWide_triality_five :
    SeitzExcOuterWideForAt IsTrialityIndex PrimeRange.geFive :=
  SeitzPlanes.mono (fun d p E hE => by
      obtain ⟨hout, -, ⟨q, hq⟩, hp5⟩ := hE
      exact ⟨hout, q, hq, hp5, trivial⟩)
    (seitzPlanes_outer_family (c := LieTypeIndex.trialityD4) (P := fun _ _ => True)
      (fun _ hv => finite_isSimpleGroup_cat_trialityD4 hv) extSeitzAtOuterFor_trialityD4_all)

end

section

open TauCeti CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP


theorem seitzExcOuterWide_F4_two :
    SeitzExcOuterWideForAt IsF4Index
      (fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = LieTypeIndex.F4 q ∧ q.p = 2 ∧ q.exponent = 1) :=
  SeitzPlanes.mono (fun d p E hE => by
      obtain ⟨hout, -, -, hp5, q, hq, hq2⟩ := hE
      exact ⟨hout, q, hq, hp5, hq2⟩)
    (seitzPlanes_outer_family (c := LieTypeIndex.F4) (P := fun q _ => q.p = 2 ∧ q.exponent = 1)
      (fun _ hv => finite_isSimpleGroup_cat_F4 hv)
      (fun q K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hout =>
        extSeitzAtOuter_F4_two hP.1 hP.2 K hnab hiso p hp hp5 hpd E hE hcard hout))

end

section

open TauCeti CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP


theorem seitzExcOuterWide_reeG2_five : SeitzExcOuterWideForAt IsReeG2Index PrimeRange.geFive := by
  have hpair := CFSG.LocalAnalysis.SubfieldPairReeG2.subfieldPairReeG2_of_pieces
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨m, hm⟩, hp5⟩
  subst hm
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, ha, hX, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model
      (K := Cat ⟨.reeG2 m, hv⟩) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have := (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple ha X hX).2.1
  have hsimple : IsSimpleGroup (Cat ⟨.reeG2 m, hv⟩) := MulEquiv.isSimpleGroup e
  have hfin : Finite (Cat ⟨.reeG2 m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hel : IsElementaryAbelian p ↥E := isElementaryAbelian_of_isElemAbelian hE
  have hnab := exists_noncommuting_of_isElementaryAbelian_aut hel hc
  have hd : FieldAutData (Cat ⟨.reeG2 m, hv⟩) p :=
    (CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.fieldAutData_reeG2 hpair hp hp5 ha
      hX).of_mulEquiv e hp
  rw [planeGen_iff_closure_fixUnion]
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc
    (fun hall => hout fun φ hφ => (hall φ hφ).elim fun g hg => ⟨g, hg.symm⟩)

end

section

open TauCeti CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP


theorem seitzExcOuterWideFive_of_maximal
    (hF4 : ExcOuterLeOne.SubfieldMaximalAll .F4) (hE6 : ExcOuterLeOne.SubfieldMaximalAll .E6)
    (hE7 : ExcOuterLeOne.SubfieldMaximalAll .E7) (hE8 : ExcOuterLeOne.SubfieldMaximalAll .E8)
    (hTw : ExcOuterLeOne.SubfieldMaximalAllTwE6) : SeitzExcOuterWideFive := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hnc, hp5⟩
  rcases (not_isClassicalIndex_iff d).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · exact seitzExcOuterWide_G2_five ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp5⟩
  · obtain ⟨q, rfl⟩ := hd
    by_cases hq : q.p = 2 ∧ q.exponent = 1
    · exact seitzExcOuterWide_F4_two ⟨.F4 q, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hout, hs, ⟨q, rfl⟩, hp5, q, rfl, hq⟩
    · exact seitzExcOuterWideF4_of_subfieldMaximalAll hF4 ⟨.F4 q, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hout, hs, ⟨q, rfl⟩, hp5, q, rfl, hq⟩
  · obtain ⟨q, rfl⟩ := hd
    exact seitzExcOuterWideE6_of_subfieldMaximalAll hE6 ⟨.E6 q, hv⟩ p hp hp2 hpd hex E hE hc
      ⟨hout, hs, ⟨q, rfl⟩, hp5, q, rfl, trivial⟩
  · obtain ⟨q, rfl⟩ := hd
    exact seitzExcOuterWideE7_of_subfieldMaximalAll hE7 ⟨.E7 q, hv⟩ p hp hp2 hpd hex E hE hc
      ⟨hout, hs, ⟨q, rfl⟩, hp5, q, rfl, trivial⟩
  · obtain ⟨q, rfl⟩ := hd
    exact seitzExcOuterWideE8_of_subfieldMaximalAll hE8 ⟨.E8 q, hv⟩ p hp hp2 hpd hex E hE hc
      ⟨hout, hs, ⟨q, rfl⟩, hp5, q, rfl, trivial⟩
  · exact seitzExcOuterWide_triality_five ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp5⟩
  · obtain ⟨q, rfl⟩ := hd
    exact seitzExcOuterWideTwE6_of_subfieldMaximalAll hTw ⟨.twistedE6 q, hv⟩ p hp hp2 hpd hex E hE
      hc ⟨hout, hs, ⟨q, rfl⟩, hp5, q, rfl, trivial⟩
  · exact seitzExcOuterWide_suzuki_five ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp5⟩
  · exact seitzExcOuterWide_reeG2_five ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp5⟩
  · exact seitzExcOuterWide_reeF4_five ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hd, hp5⟩
  · subst hd
    exact (hout (innerPlane_tits hv hp hp2 hc)).elim

end

section


theorem seitzExcOuterWideFive_holds : SeitzExcOuterWideFive :=
  seitzExcOuterWideFive_of_maximal ExcOuterLeOne.subfieldMaximalAll_F4
    ExcOuterLeOne.subfieldMaximalAll_E6 ExcOuterLeOne.subfieldMaximalAll_E7
    ExcOuterLeOne.subfieldMaximalAll_E8 ExcOuterLeOne.subfieldMaximalAllTwE6

end

end CFSG.LieType.SeitzGeneration
