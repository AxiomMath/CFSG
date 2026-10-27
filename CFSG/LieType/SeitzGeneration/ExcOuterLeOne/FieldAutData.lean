module

public import CFSG.HardMathSupport.Lang.E6Descent.FieldAutE6
public import CFSG.HardMathSupport.Lang.E6Descent.FieldAutTwE6
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Defs
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FixedGroup
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FixedGroupE7
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Generic
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.OutRank
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Untwisted
public import CFSG.HardMathSupport.Lang.E6Descent.FixedE6

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.E6Descent

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne


theorem fieldAutData_E6_of_maximalAt {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup Tag.E6 σ) →
      ∀ M : Subgroup ↥(adjointGroup Tag.E6 K),
        subfieldGroup Tag.E6 σ ≤ M → M = subfieldGroup Tag.E6 σ ∨ M = ⊤) :
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
    by_cases hdvd : p ∣ Nat.card ↥(fixedSubgroup (entrywiseAdjointAut Tag.E6 σ))
    · exact Or.inl (closure_pair_eq_top_of_maximal (hmax σ hσ hdvd) d hne)
    · exact Or.inr hdvd

theorem fieldAutData_E6_of_maximal (h : SubfieldMaximalLeOne .E6) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K)
    (hle : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1) :
    FieldAutData (adjointGroup Tag.E6 K) p :=
  fieldAutData_E6_of_maximalAt (K := K) hp hp5
    (fun σ hσ hdvd M hRM => h K σ p hp hp5 hpK hσ hle hdvd M hRM)

theorem fieldAutData_twE6_of_maximalAt {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmax : ∀ η : K ≃+* K, orderOf η = p →
      p ∣ Nat.card ↥(fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)) →
      ∀ M : Subgroup ↥(twistedE6RootGroup K σ),
        fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ≤ M →
        M = fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ∨ M = ⊤) :
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
    by_cases hdvd : p ∣ Nat.card ↥(fixedSubgroup (fieldActor (t := TwistTag.E6) σ η))
    · exact Or.inl (closure_pair_eq_top_of_maximal (hmax η hη hdvd) d hne)
    · exact Or.inr hdvd

theorem fieldAutData_twE6_of_maximal (h : SubfieldMaximalLeOneTwE6) {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ)
    (hle : degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p)) ≤ 1) :
    FieldAutData ↥(twistedE6RootGroup K σ) p :=
  fieldAutData_twE6_of_maximalAt hℓ hf hK σ hσ hp hp5
    (fun η hη hdvd M hRM => h ℓ f hℓ hf K hK σ hσ p hp hp5 hpℓ η hη hle hdvd M hRM)

theorem fieldAutData_E_of_maximalAt_odd (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ¬ p ∣ τ.cartan.det.natAbs)
    (hΓJ : ∀ σ : K ≃+* K, σ ^ p = 1 → entrywiseFixedGroup τ σ = fixedFieldImage τ σ)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup τ σ) →
      ∀ M : Subgroup ↥(adjointGroup τ K),
        subfieldGroup τ σ ≤ M → M = subfieldGroup τ σ ∨ M = ⊤) :
    FieldAutData (adjointGroup τ K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  refine fieldAutData_of_standard ⊤
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut τ σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_inner_mem_of_plane_E_of_odd τ hτ hp hp2 hdet E hEc
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
      have hTjp : (T ^ j) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, ← hTo, pow_orderOf_eq_one, one_pow]
      refine orderOf_eq_prime hTjp fun h1 => ?_
      have : α = 1 := by rw [hαe, ← entrywiseAdjointAut_pow, h1, entrywiseAdjointAut_one]; group
      have h0 : orderOf α = 1 := by rw [this]; exact orderOf_one
      exact hp.one_lt.ne' (hord.symm.trans h0)
    refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut τ (T ^ j), ⟨T ^ j, hTj, rfl⟩, ?_⟩
    rw [hαe, entrywiseAdjointAut_pow]
    group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ', hτ', rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := τ))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσ hτ')
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    exact eq_one_of_central_fixed_of_eq σ (hΓJ σ (hσ ▸ pow_orderOf_eq_one σ)) hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d _ hne
    by_cases hdvd : p ∣ Nat.card ↥(fixedSubgroup (entrywiseAdjointAut τ σ))
    · exact Or.inl (closure_pair_eq_top_of_maximal (hmax σ hσ hdvd) d hne)
    · exact Or.inr hdvd

theorem fieldAutData_E_of_maximalAt (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hΓJ : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p : ℕ), p.Prime → 3 < p →
      σ ^ p = 1 → entrywiseFixedGroup τ σ = fixedFieldImage τ σ)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup τ σ) →
      ∀ M : Subgroup ↥(adjointGroup τ K),
        subfieldGroup τ σ ≤ M → M = subfieldGroup τ σ ∨ M = ⊤) :
    FieldAutData (adjointGroup τ K) p :=
  fieldAutData_E_of_maximalAt_odd τ hτ hp (by omega) (not_dvd_det_cartan_E hτ hp (by omega))
    (fun σ hσ => hΓJ K σ p hp (by omega) hσ) hmax

theorem fieldAutData_E_of_maximal (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hΓJ : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (p : ℕ), p.Prime → 3 < p →
      σ ^ p = 1 → entrywiseFixedGroup τ σ = fixedFieldImage τ σ)
    (h : SubfieldMaximalLeOne τ) {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K)
    (hle : CFSG.LieType.SeitzGeneration.degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1) :
    FieldAutData (adjointGroup τ K) p :=
  fieldAutData_E_of_maximalAt (K := K) τ hτ hΓJ hp hp5
    (fun σ hσ hdvd M hRM => h K σ p hp hp5 hpK hσ hle hdvd M hRM)

theorem fieldAutData_F4_of_maximalAt_odd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup Tag.F4 σ) →
      ∀ M : Subgroup ↥(adjointGroup Tag.F4 K),
        subfieldGroup Tag.F4 σ ≤ M → M = subfieldGroup Tag.F4 σ ∨ M = ⊤) :
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
      exact hp.one_lt.ne' (hord.symm.trans h0)
    refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut Tag.F4 (T ^ j), ⟨T ^ j, hTj, rfl⟩, ?_⟩
    rw [hαe, entrywiseAdjointAut_pow]
    group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ', hτ', rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := Tag.F4))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσ hτ')
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    exact eq_one_of_central_fixed_of_eq σ (entrywiseFixedGroup_F4_eq σ) hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d _ hne
    by_cases hdvd : p ∣ Nat.card ↥(fixedSubgroup (entrywiseAdjointAut Tag.F4 σ))
    · exact Or.inl (closure_pair_eq_top_of_maximal (hmax σ hσ hdvd) d hne)
    · exact Or.inr hdvd

theorem fieldAutData_F4_of_maximalAt {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup Tag.F4 σ) →
      ∀ M : Subgroup ↥(adjointGroup Tag.F4 K),
        subfieldGroup Tag.F4 σ ≤ M → M = subfieldGroup Tag.F4 σ ∨ M = ⊤) :
    FieldAutData (adjointGroup Tag.F4 K) p :=
  fieldAutData_F4_of_maximalAt_odd hp (by omega) hmax

theorem fieldAutData_F4_of_maximal (h : SubfieldMaximalLeOne .F4) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K)
    (hle : CFSG.LieType.SeitzGeneration.degCount Tag.F4
      (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1) :
    FieldAutData (adjointGroup Tag.F4 K) p :=
  fieldAutData_F4_of_maximalAt (K := K) hp hp5
    (fun σ hσ hdvd M hRM => h K σ p hp hp5 hpK hσ hle hdvd M hRM)

theorem fieldAutData_E7_of_maximalAt {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup Tag.E7 σ) →
      ∀ M : Subgroup ↥(adjointGroup Tag.E7 K),
        subfieldGroup Tag.E7 σ ≤ M → M = subfieldGroup Tag.E7 σ ∨ M = ⊤) :
    FieldAutData (adjointGroup Tag.E7 K) p :=
  fieldAutData_E_of_maximalAt (K := K) .E7 (Or.inr (Or.inl rfl))
    (fun _ _ _ σ p hp hp3 hσp => entrywiseFixedGroup_E7_eq_of_pow σ hp hp3 hσp) hp hp5 hmax

theorem fieldAutData_E7_of_maximal (h : SubfieldMaximalLeOne .E7) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K)
    (hle : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1) :
    FieldAutData (adjointGroup Tag.E7 K) p :=
  fieldAutData_E7_of_maximalAt (K := K) hp hp5
    (fun σ hσ hdvd M hRM => h K σ p hp hp5 hpK hσ hle hdvd M hRM)

theorem fieldAutData_E8_of_maximalAt {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup Tag.E8 σ) →
      ∀ M : Subgroup ↥(adjointGroup Tag.E8 K),
        subfieldGroup Tag.E8 σ ≤ M → M = subfieldGroup Tag.E8 σ ∨ M = ⊤) :
    FieldAutData (adjointGroup Tag.E8 K) p :=
  fieldAutData_E_of_maximalAt (K := K) .E8 (Or.inr (Or.inr rfl))
    (fun _ _ _ σ _ _ _ _ => entrywiseFixedGroup_E8_eq σ) hp hp5 hmax

theorem fieldAutData_E8_of_maximal (h : SubfieldMaximalLeOne .E8) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ≠ ringChar K)
    (hle : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1) :
    FieldAutData (adjointGroup Tag.E8 K) p :=
  fieldAutData_E8_of_maximalAt (K := K) hp hp5
    (fun σ hσ hdvd M hRM => h K σ p hp hp5 hpK hσ hle hdvd M hRM)

theorem fieldAutData_E7_of_maximalAt_odd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup Tag.E7 σ) →
      ∀ M : Subgroup ↥(adjointGroup Tag.E7 K),
        subfieldGroup Tag.E7 σ ≤ M → M = subfieldGroup Tag.E7 σ ∨ M = ⊤) :
    FieldAutData (adjointGroup Tag.E7 K) p :=
  fieldAutData_E_of_maximalAt_odd (K := K) .E7 (Or.inr (Or.inl rfl)) hp hp2
    (not_dvd_det_cartan_E_of_odd (Or.inl rfl) hp hp2)
    (fun σ hσ => entrywiseFixedGroup_E7_eq_of_odd_pow σ hp hp2 hσ) hmax

theorem fieldAutData_E8_of_maximalAt_odd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hmax : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card ↥(subfieldGroup Tag.E8 σ) →
      ∀ M : Subgroup ↥(adjointGroup Tag.E8 K),
        subfieldGroup Tag.E8 σ ≤ M → M = subfieldGroup Tag.E8 σ ∨ M = ⊤) :
    FieldAutData (adjointGroup Tag.E8 K) p :=
  fieldAutData_E_of_maximalAt_odd (K := K) .E8 (Or.inr (Or.inr rfl)) hp hp2
    (not_dvd_det_cartan_E_of_odd (Or.inr rfl) hp hp2)
    (fun σ _ => entrywiseFixedGroup_E8_eq σ) hmax

theorem fieldAutData_F4_of_subfieldMaximalAllOdd (h : SubfieldMaximalAllOdd .F4) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.F4 K) p :=
  fieldAutData_F4_of_maximalAt_odd (K := K) hp hp2 (fun σ hσ _ M hRM => h K σ p hp hp2 hpK hσ M hRM)

theorem fieldAutData_E7_of_subfieldMaximalAllOdd (h : SubfieldMaximalAllOdd .E7) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.E7 K) p :=
  fieldAutData_E7_of_maximalAt_odd (K := K) hp hp2 (fun σ hσ _ M hRM => h K σ p hp hp2 hpK hσ M hRM)

theorem fieldAutData_E8_of_subfieldMaximalAllOdd (h : SubfieldMaximalAllOdd .E8) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.E8 K) p :=
  fieldAutData_E8_of_maximalAt_odd (K := K) hp hp2 (fun σ hσ _ M hRM => h K σ p hp hp2 hpK hσ M hRM)

theorem fieldAutData_F4_of_subfieldMaximalAllThree (h : SubfieldMaximalAllThree .F4) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p = 3) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.F4 K) p :=
  fieldAutData_F4_of_maximalAt_odd (K := K) (by rw [hp]; exact Nat.prime_three) (by omega)
    (fun σ hσ _ M hRM => h K σ p hp hpK hσ M hRM)

theorem fieldAutData_E7_of_subfieldMaximalAllThree (h : SubfieldMaximalAllThree .E7) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p = 3) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.E7 K) p :=
  fieldAutData_E7_of_maximalAt_odd (K := K) (by rw [hp]; exact Nat.prime_three) (by omega)
    (fun σ hσ _ M hRM => h K σ p hp hpK hσ M hRM)

theorem fieldAutData_E8_of_subfieldMaximalAllThree (h : SubfieldMaximalAllThree .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p = 3) (hpK : p ≠ ringChar K) :
    FieldAutData (adjointGroup Tag.E8 K) p :=
  fieldAutData_E8_of_maximalAt_odd (K := K) (by rw [hp]; exact Nat.prime_three) (by omega)
    (fun σ hσ _ M hRM => h K σ p hp hpK hσ M hRM)

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
