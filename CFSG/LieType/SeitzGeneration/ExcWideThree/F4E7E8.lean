module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Maximal
public import CFSG.LieType.SeitzGeneration.ExcSeitzGaps
public import CFSG.LieType.SeitzGeneration.ExcWideThree.PlaneKernel

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Lang.E6Descent CFSG.Open
  CFSG.AGLEmbeddingD2 TauCeti

section FieldAut


theorem not_dvd_det_cartan_E78 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ τ.cartan.det.natAbs := by
  rcases hτ with rfl | rfl
  · rw [det_cartan_E7]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · rw [det_cartan_E8]
    intro h
    exact hp.one_lt.ne' (Nat.dvd_one.1 h)

theorem exists_inner_mem_of_plane_E78 (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut ↥(adjointGroup τ K))) [hE : CFSG.IsElementaryAbelian p ↥E]
    (hEc : Nat.card ↥E = p ^ 2) : ∃ g : ↥(adjointGroup τ K), g ≠ 1 ∧ MulAut.conj g ∈ E := by
  classical
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    hτ.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hdet := not_dvd_det_cartan_E78 hτ hp hp2
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  obtain ⟨Θ, -, -, hker, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ' K
  obtain ⟨ι, hιE, hι1, hιker⟩ := exists_ne_one_mem_ker_of_plane τ hτ' hp hp2 Θ E hEc
  have hιp := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) ι hιE
  obtain ⟨g, hg⟩ := mem_inner_of_mem_ker_E τ hτ' hp hdet Θ hker hιker hιp
  refine ⟨g, ?_, hg ▸ hιE⟩
  rintro rfl
  rw [map_one] at hg
  exact hι1 hg.symm

theorem fieldAutData_E78_of_maximalOdd (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8)
    (h : SubfieldMaximalAllOdd τ) {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup τ K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    hτ.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hdet := not_dvd_det_cartan_E78 hτ hp hp2
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  refine fieldAutData_of_standard ⊤
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut τ σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_inner_mem_of_plane_E78 τ hτ hp hp2 E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
    have hα' : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup τ K) :=
      fun ⟨g, hg⟩ => hout g hg.symm
    obtain ⟨d, T, r, j, ψ, -, hTo, -, hj, hψ⟩ :=
      exists_conj_entrywise_of_outer_E τ hτ' n.pos K hK hp hp2 hdet α hαp hα'
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
      have := hp.one_lt
      omega
    refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut τ (T ^ j), ⟨T ^ j, hTj, rfl⟩, ?_⟩
    rw [hαe, entrywiseAdjointAut_pow]
    group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ', hτ', rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := τ))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσ hτ')
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    have hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ := by
      rcases hτ with rfl | rfl
      · exact entrywiseFixedGroup_eq_fixedFieldImage_E7_of_pow σ (hσ ▸ pow_orderOf_eq_one σ) hcop2
      · exact entrywiseFixedGroup_E8_eq σ
    exact eq_one_of_central_fixed_of_eq σ hΓJ hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d _ hne
    exact Or.inl (closure_pair_eq_top_of_maximal (h K σ p hp hp2 hpK hσ) d hne)

theorem fieldAutData_F4_of_maximalOdd (h : SubfieldMaximalAllOdd .F4) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.F4 K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
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
      have := hp.one_lt
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
    exact Or.inl (closure_pair_eq_top_of_maximal (h K σ p hp hp2 hpK hσ) d hne)

theorem seitzExcOuterWideThree_of_fieldAutData {τ : Tag} {c : PrimePower → LieTypeIndex}
    {F : LieTypeIndex → Prop} {X : PrimePower → Prop}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q, (c q).characteristic = q.p)
    (hinj : ∀ (K : Type) [Field K] [Finite K],
      Function.Injective (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)))
    (hF : ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → FieldAutData ↥(adjointGroup τ K) 3) :
    SeitzExcOuterWideForAt F (fun d p => p = 3 ∧ ∃ q : PrimePower, d = c q ∧ X q) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, -, hp3, q, hdq, -⟩
  obtain rfl : d = c q := hdq
  subst hp3
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hpq : 3 ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  have hpK : ringChar K ≠ 3 := by rw [ringChar.eq K q.p]; exact fun h => hpq h.symm
  exact planeGen_outer_of_fieldAutData (hinj K) e hp (hF K hpK) hE hc hout

theorem seitzExcOuterWideF4_three : SeitzExcOuterWideForAt IsF4Index PrimeRange.three :=
  SeitzPlanes.mono (fun d p E hE => by
      obtain ⟨hout, hs, ⟨q, hq⟩, hp3⟩ := hE
      exact ⟨hout, hs, ⟨q, hq⟩, hp3, q, hq, trivial⟩)
    (seitzExcOuterWideThree_of_fieldAutData (c := LieTypeIndex.F4) (F := IsF4Index)
      (X := fun _ => True)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 LieTypeIndex.characteristic_F4
      (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
      fun _ _ _ hK3 =>
        fieldAutData_F4_of_maximalOdd subfieldMaximalAllOdd_F4 Nat.prime_three (by norm_num)
          fun h => hK3 h.symm)

theorem seitzExcOuterWideE7_three : SeitzExcOuterWideForAt IsE7Index PrimeRange.three :=
  SeitzPlanes.mono (fun d p E hE => by
      obtain ⟨hout, hs, ⟨q, hq⟩, hp3⟩ := hE
      exact ⟨hout, hs, ⟨q, hq⟩, hp3, q, hq, trivial⟩)
    (seitzExcOuterWideThree_of_fieldAutData (c := LieTypeIndex.E7) (F := IsE7Index)
      (X := fun _ => True)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 LieTypeIndex.characteristic_E7
      (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
      fun _ _ _ hK3 =>
        fieldAutData_E78_of_maximalOdd .E7 (Or.inl rfl)
          (subfieldMaximalAllOdd_of_E .E7 (Or.inr (Or.inl rfl))) Nat.prime_three (by norm_num)
          fun h => hK3 h.symm)

theorem seitzExcOuterWideE8_three : SeitzExcOuterWideForAt IsE8Index PrimeRange.three :=
  SeitzPlanes.mono (fun d p E hE => by
      obtain ⟨hout, hs, ⟨q, hq⟩, hp3⟩ := hE
      exact ⟨hout, hs, ⟨q, hq⟩, hp3, q, hq, trivial⟩)
    (seitzExcOuterWideThree_of_fieldAutData (c := LieTypeIndex.E8) (F := IsE8Index)
      (X := fun _ => True)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 LieTypeIndex.characteristic_E8
      (fun _ _ _ => CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup)
      fun _ _ _ hK3 =>
        fieldAutData_E78_of_maximalOdd .E8 (Or.inr rfl)
          (subfieldMaximalAllOdd_of_E .E8 (Or.inr (Or.inr rfl))) Nat.prime_three (by norm_num)
          fun h => hK3 h.symm)

end FieldAut

end CFSG.LieType.SeitzGeneration.ExcWideThree
