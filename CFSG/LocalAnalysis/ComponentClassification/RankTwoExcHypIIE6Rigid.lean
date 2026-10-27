module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIBasic
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6OuterInvolutionOddCore

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LieType.Chevalley.E6GraphFullCoset (IsOrdinaryDiagGraph)

section Data

variable {G : Type*} [Group G] {C J : Subgroup G} [Finite C]

theorem rigidInvolution_of_derivedFixed (hZ : center C = ⊥) {η : MulAut C}
    (hηX : η ∉ OuterAutomorphisms.inner C) (hD : DerivedFixedSubgroupData C J η)
    (hcent : centralizer {η} ⊓ centralizer ((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) :
      Set (MulAut C)) = zpowers η) :
    RigidInvolution (OuterAutomorphisms.inner C) η := by
  obtain ⟨hord, hJC, -, -, hJs, hJe, -, hNη, hNnorm⟩ := hD
  have hη2 : η ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one η
  exact rigidInvolution_of_simple' hZ hηX hη2 hJC hJs hJe hNη hNnorm hcent.le

theorem rigidInvolution_of_canonicalGraph (hZ : center C = ⊥) {P : G} {η : MulAut C}
    (hηX : η ∉ OuterAutomorphisms.inner C) (hD : CanonicalGraphFixedSubgroup C J P)
    (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (hcent : centralizer {η} ⊓ centralizer ((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) :
      Set (MulAut C)) = zpowers η) :
    RigidInvolution (OuterAutomorphisms.inner C) η := by
  obtain ⟨η₀, hη₀, hord, hJC, -, hJs, hJe, -, hNη, hNnorm⟩ := hD
  have e : η₀ = η := MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, hη])
  subst e
  have hη2 : η₀ ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one η₀
  exact rigidInvolution_of_simple' hZ hηX hη2 hJC hJs hJe hNη hNnorm hcent.le

end Data

theorem not_mem_inner_of_conj {M : Type*} [Group M] {α β φ : MulAut M} (h : φ * α * φ⁻¹ = β)
    (hα : α ∉ OuterAutomorphisms.inner M) : β ∉ OuterAutomorphisms.inner M := fun hβ => hα (by
  have := (inner_normal M).conj_mem _ hβ φ⁻¹
  rwa [← h, show φ⁻¹ * (φ * α * φ⁻¹) * φ⁻¹⁻¹ = α by group] at this)

theorem rigid_or_secondGraph_E6
    {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ f) (α : MulAut (adjointGroup TwistTag.E6.tag k))
    (hαX : α ∉ OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k)) (hα2 : α ^ 2 = 1) :
    RigidInvolution (OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k)) α ∨
      ∃ (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k)
        (φ : MulAut (adjointGroup TwistTag.E6.tag k)),
        φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * diagramConjAut TwistTag.E6 k := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite (adjointGroup TwistTag.E6.tag k) := generated_group_finite _ k
  have : Fintype k := Fintype.ofFinite k
  have hZ : center (adjointGroup TwistTag.E6.tag k) = ⊥ := center_adjointGroup_eq_bot
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  obtain ⟨Θ, -, hΘ, -, -, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) k
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) k
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have hΘα := hΘ α g a σ ε hga
  have hε2 : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε2 with h0 | h1
    ·
      refine absurd (CFSG.RankThree.Chevalley.mem_inner_of_conj_mul_rootDiagAut hf k hk hα2 g a
        (MulEquiv.ext fun h => Subtype.ext ?_)) hαX
      have e1 : Units.map (entrywiseHom (1 : k ≃+* k).toRingHom)
          (h : ModGL TwistTag.E6.tag k) = h := Units.ext (entrywise_id _)
      rw [hga h, h0, exactQ_zero, e1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
      group
    ·
      obtain ⟨ht, η, hη, hconj, hiff, -, -⟩ :=
        (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 k hk
      have hηγ : η = diagramConjAut TwistTag.E6 k :=
        MulEquiv.ext fun g => Subtype.ext (by rw [hη, coe_diagramConjAut])
      have hdiag : IsOrdinaryDiagGraph k α := by
        rw [hiff Θ hΘ, hΘα, h1, Nat.cast_one]
      rcases hconj α hdiag hα2 with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
      · left
        refine rigidInvolution_of_conj hφ ?_
        have hD := canonicalGraphFixedSubgroup_adjointGroup k hf hk h2
        rw [map_baseChangeGL_id] at hD
        have hcent := even_E6_canonical_graph_full_pointwise_centralizer hf k hk
        rw [← hηγ] at hcent
        exact rigidInvolution_of_canonicalGraph hZ (not_mem_inner_of_conj hφ hαX) hD hη hcent
      · right
        exact ⟨ht, φ, hηγ ▸ hφ⟩
  ·
    left
    have hσ2 : σ ^ 2 = 1 := by
      have h1 : Θ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
      rw [hΘα, Prod.pow_mk, Prod.mk_eq_one] at h1
      exact h1.1
    obtain ⟨⟨e, he⟩, hσc, -⟩ := hfield 2 f Nat.prime_two hf hk σ hσ2 hσ1
    have he1 : 1 ≤ e := by omega
    have hk' : Nat.card k = 2 ^ (2 * e) := by rw [hk, he, two_mul]
    have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show f / 2 = e by omega]
    obtain ⟨hQ1, hQP⟩ :=
      even_exceptional_quadratic_field_graph_field_involution_descent he1 k hk' σ.toRingHom hσ'
    have hconj : ∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ =
        diagramConjAut TwistTag.E6 k ^ (ε : ℕ) * entrywiseAdjointAut TwistTag.E6.tag σ := by
      rcases hε2 with h0 | h1
      · obtain ⟨_, -, hdesc⟩ := hQ1 TwistTag.E6.tag
        obtain ⟨-, hdα⟩ := hdesc g a
        obtain ⟨ψ, hψ, -⟩ := hdα α (fun u => by
          rw [hga u, h0, exactQ_zero, mul_one, inv_one, mul_one]) (by rw [← pow_two]; exact hα2)
        refine ⟨ψ, MulEquiv.ext fun u => Subtype.ext ?_⟩
        rw [hψ u, h0, pow_zero, one_mul, coe_entrywiseAdjointAut]
      · obtain ⟨_, -, hdesc⟩ := hQP
        obtain ⟨-, hdα⟩ := hdesc g a
        obtain ⟨ψ, hψ, -⟩ := hdα α (fun u => by
          rw [hga u, h1]
          rfl) (by rw [← pow_two]; exact hα2)
        refine ⟨ψ, MulEquiv.ext fun u => Subtype.ext ?_⟩
        rw [hψ u, h1, pow_one, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut]
    obtain ⟨φ, hφ⟩ := hconj
    refine rigidInvolution_of_conj hφ ?_
    obtain ⟨hD0, hD1⟩ :=
      even_E6_canonical_field_graph_field_derived_fixed_subgroups he1 k hk' σ hσ'
    obtain ⟨hc0, hc1⟩ :=
      even_E6_canonical_field_graph_field_pointwise_centralizers he1 k hk' σ hσ'
    have hX := not_mem_inner_of_conj hφ hαX
    rcases hε2 with h0 | h1
    · rw [h0] at hX ⊢
      exact rigidInvolution_of_derivedFixed hZ hX hD0 hc0
    · rw [h1] at hX ⊢
      exact rigidInvolution_of_derivedFixed hZ hX hD1 hc1

theorem rigid_or_secondGraph_twistedE6
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hαX : α ∉ OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hα2 : α ^ 2 = 1) :
    RigidInvolution (OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
        α ∨
      ∃ (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
          graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
        (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
        (∀ h, (η h : ModGL TwistTag.E6.tag K) =
          diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) ∧
        ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
          φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subtype.finite
  have hZ : center (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hk := CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hf hK hσ'
  obtain ⟨ht, η, hη, -, -, hnoninner, -, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ.toRingHom hσ'
  have hnc : ∀ c, α ≠ MulAut.conj c := fun c h => hαX ⟨c, h.symm⟩
  rcases hnoninner α hα2 hnc with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · left
    refine rigidInvolution_of_conj hφ ?_
    obtain ⟨-, ⟨hD, -⟩⟩ := even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K hk hK σ.toRingHom hσ'
    have hcent := even_twisted_E6_canonical_graph_full_pointwise_centralizer hf
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K hk hK σ.toRingHom hσ' η hη
    exact rigidInvolution_of_canonicalGraph hZ (not_mem_inner_of_conj hφ hαX) hD hη hcent
  · exact Or.inr ⟨ht, η, hη, φ, hφ⟩

end CFSG.ComponentClassification.RankTwoExcHypII
