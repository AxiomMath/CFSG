module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneE6OuterBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptional

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LieType.Chevalley.E6GraphFullCoset (IsOrdinaryDiagGraph)
open CFSG.LieType.Chevalley.E6SecondGraphFull (secondGraphFullCentralizer_adjointGroup
  secondGraphFullCentralizer_graphFixedRootGroup)
open CFSG.RankThree.Chevalley (inf_centralizer_congr center_eq_bot_of_mulEquiv_adjointGroup
  pinnedX_e6HighestRoot_one_sq mem_inner_of_conj_mul_rootDiagAut)

theorem not_mem_inner_of_conj {C : Type*} [Group C] {α φ η : MulAut C} (hαI : α ∉ inner C)
    (hφ : φ * α * φ⁻¹ = η) : η ∉ inner C := fun h => hαI (by
  have := (inner_normal C).conj_mem _ h φ⁻¹
  rwa [← hφ, show φ⁻¹ * (φ * α * φ⁻¹) * φ⁻¹⁻¹ = α by group] at this)

theorem noNormalZ4OrZ2xZ4_inf_centralizer_inner_of_F4 {G : Type*} [Group G]
    {J : Subgroup G}
    (k : Type) [Field k] (hF4 : InnerInvolutionInput (adjointGroup Tag.F4 k))
    (e : J ≃* adjointGroup Tag.F4 k) {t : G} (htJ : t ∈ J) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (τJ : MulAut J) (hτJ : ∀ x : J, (τJ x : G) = t * x * t⁻¹) (L : Subgroup (MulAut J))
    (hL : inner J ≤ L) : NoNormalZ4OrZ2xZ4 ↥(L ⊓ centralizer ({τJ} : Set (MulAut J))) := by
  have hτ : τJ = MulAut.conj (⟨t, htJ⟩ : J) := MulEquiv.ext fun x => Subtype.ext (hτJ x)
  subst hτ
  set Φ := MulAut.congr e with hΦ
  have hΦconj : ∀ y : J, Φ (MulAut.conj y) = MulAut.conj (e y) := fun y =>
    MulEquiv.ext fun b => by
      change e (y * e.symm b * y⁻¹) = e y * b * (e y)⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hZJ : center J = ⊥ := center_eq_bot_of_mulEquiv_adjointGroup k e
  have htord : orderOf (⟨t, htJ⟩ : J) = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => ht1 (congrArg Subtype.val h)
    rw [Subgroup.coe_pow, pow_two, ht2, Subgroup.coe_one]
  have hord : orderOf (Φ (MulAut.conj (⟨t, htJ⟩ : J))) = 2 := by
    rw [MulEquiv.orderOf_eq,
      orderOf_injective _ (mulAut_conj_injective_of_center_eq_bot hZJ), htord]
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 k) ≤
      L.map Φ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), hL ⟨e.symm y, rfl⟩, ?_⟩
    change Φ (MulAut.conj (e.symm y)) = MulAut.conj y
    rw [hΦconj, MulEquiv.apply_symm_apply]
  have hmem : Φ (MulAut.conj (⟨t, htJ⟩ : J)) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.F4 k) :=
    ⟨e ⟨t, htJ⟩, (hΦconj _).symm⟩
  exact NoNormalZ4OrZ2xZ4.of_mulEquiv (inf_centralizer_congr e L _).symm
    (hF4 (L.map Φ.toMonoidHom) hinner _ hmem hord)

theorem abelianNormalCardLeTwo_of_derivedFixed {G : Type*} [Group G] {C J : Subgroup G}
    {η : MulAut C} (hD : DerivedFixedSubgroupData C J η)
    (hcent : centralizer {η} ⊓ centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = zpowers η)
    (hηI : η ∉ inner C) (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer ({η} : Set (MulAut C))) := by
  obtain ⟨hord, hJC, -, -, hJs, -, hinj, hNη, hNnorm⟩ := hD
  have hη : η ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one η
  exact abelianNormalCardLeTwo_of_simple_inner hη hJC hJs hinj hNη hNnorm hcent hηI H hIH

theorem abelianNormalCardLeTwo_of_canonicalGraph {G : Type*} [Group G] {C J : Subgroup G}
    {P : G} (hD : CanonicalGraphFixedSubgroup C J P) {η : MulAut C}
    (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (hcent : centralizer {η} ⊓ centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = zpowers η)
    (hηI : η ∉ inner C) (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer ({η} : Set (MulAut C))) := by
  obtain ⟨η₀, hη₀, hord, hJC, -, hJs, -, hinj, hNη, hNnorm⟩ := hD
  have e : η₀ = η := MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, hη])
  subst e
  have hη2 : η₀ ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one η₀
  exact abelianNormalCardLeTwo_of_simple_inner hη2 hJC hJs hinj hNη hNnorm hcent hηI H hIH

theorem abelianNormalCardLeTwo_E6_field_class {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f)
    (Θ : MulAut (adjointGroup TwistTag.E6.tag K) →*
      RingAut K × Multiplicative (ZMod (exactE TwistTag.E6.tag)))
    (hΘ : ∀ (β : MulAut (adjointGroup TwistTag.E6.tag K)) (g : adjointGroup TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE TwistTag.E6.tag)),
      (∀ h : adjointGroup TwistTag.E6.tag K, (β h : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          exactQ TwistTag.E6.tag K ε * Units.map (entrywiseHom σ.toRingHom)
            (h : ModGL TwistTag.E6.tag K) * (exactQ TwistTag.E6.tag K ε)⁻¹ *
              (rootDiagUnit TwistTag.E6.tag a)⁻¹ * (g : ModGL TwistTag.E6.tag K)⁻¹) →
      Θ β = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE TwistTag.E6.tag))))
    (H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag K)))
    (hIH : inner (adjointGroup TwistTag.E6.tag K) ≤ H)
    {α : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hαI : α ∉ inner (adjointGroup TwistTag.E6.tag K)) (hα : orderOf α = 2)
    (hΘα : (Θ α).1 ≠ 1) :
    AbelianNormalCardLeTwo
      ↥(H ⊓ centralizer ({α} : Set (MulAut (adjointGroup TwistTag.E6.tag K)))) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have hΘα' := hΘ α g a σ ε hga
  have hσ1 : σ ≠ 1 := by
    rw [hΘα'] at hΘα
    exact hΘα
  have hσ2 : σ ^ 2 = 1 := by
    have h1 : Θ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
    rw [hΘα', Prod.pow_mk, Prod.mk_eq_one] at h1
    exact h1.1
  obtain ⟨-, -, -, -, -, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨⟨e, he⟩, hσc, -⟩ := hfield 2 f Nat.prime_two hf hK σ hσ2 hσ1
  have he1 : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show f / 2 = e by omega]
  obtain ⟨hQ1, hQP⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ'
  have hε2 : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega
  have hconj : ∃ φ : MulAut (adjointGroup TwistTag.E6.tag K), φ * α * φ⁻¹ =
      diagramConjAut TwistTag.E6 K ^ (ε : ℕ) * entrywiseAdjointAut TwistTag.E6.tag σ := by
    rcases hε2 with h0 | h1
    · obtain ⟨_, -, hdesc⟩ := hQ1 TwistTag.E6.tag
      obtain ⟨-, hdα⟩ := hdesc g a
      have hαform : ∀ u, (α u : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag a * Units.map (entrywiseHom σ.toRingHom)
            (u : ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro u
        rw [hga u, h0, exactQ_zero, mul_one, inv_one, mul_one]
      obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα2)
      refine ⟨ψ, MulEquiv.ext fun u => Subtype.ext ?_⟩
      rw [hψ u, h0, pow_zero, one_mul, coe_entrywiseAdjointAut]
    · obtain ⟨_, -, hdesc⟩ := hQP
      obtain ⟨-, hdα⟩ := hdesc g a
      have hαform : ∀ u, (α u : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
            Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro u
        rw [hga u, h1]
        rfl
      obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα2)
      refine ⟨ψ, MulEquiv.ext fun u => Subtype.ext ?_⟩
      rw [hψ u, h1, pow_one, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut]
  obtain ⟨φ, hφ⟩ := hconj
  have hηI := not_mem_inner_of_conj hαI hφ
  refine AbelianNormalCardLeTwo.of_conj hφ ?_
  have hIH' := inner_le_map_conj_of_le hIH φ
  obtain ⟨hD0, hD1⟩ := even_E6_canonical_field_graph_field_derived_fixed_subgroups he1 K hK' σ hσ'
  obtain ⟨hc0, hc1⟩ :=
    even_E6_canonical_field_graph_field_pointwise_centralizers he1 K hK' σ hσ'
  rcases hε2 with h0 | h1
  · rw [h0] at hηI ⊢
    exact abelianNormalCardLeTwo_of_derivedFixed hD0 hc0 hηI _ hIH'
  · rw [h1] at hηI ⊢
    exact abelianNormalCardLeTwo_of_derivedFixed hD1 hc1 hηI _ hIH'

theorem abelianNormalCardLeTwo_E6_graph_class {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = 2 ^ f) (η : MulAut (adjointGroup TwistTag.E6.tag k))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹)
    (H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag k)))
    (hIH : inner (adjointGroup TwistTag.E6.tag k) ≤ H)
    {α φ : MulAut (adjointGroup TwistTag.E6.tag k)}
    (hαI : α ∉ inner (adjointGroup TwistTag.E6.tag k)) (hα : φ * α * φ⁻¹ = η) :
    AbelianNormalCardLeTwo
      ↥(H ⊓ centralizer ({α} : Set (MulAut (adjointGroup TwistTag.E6.tag k)))) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have hD := canonicalGraphFixedSubgroup_adjointGroup k hf hk h2
  rw [map_baseChangeGL_id] at hD
  have hηγ : η = diagramConjAut TwistTag.E6 k :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη, coe_diagramConjAut])
  have hcent := even_E6_canonical_graph_full_pointwise_centralizer hf k hk
  rw [← hηγ] at hcent
  exact AbelianNormalCardLeTwo.of_conj hα (abelianNormalCardLeTwo_of_canonicalGraph hD hη hcent
    (not_mem_inner_of_conj hαI hα) _ (inner_le_map_conj_of_le hIH φ))

theorem sq_ne_E6_graph {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k] (hk : Nat.card k = 2 ^ f)
    (η : MulAut (adjointGroup TwistTag.E6.tag k))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹)
    (β : MulAut (adjointGroup TwistTag.E6.tag k)) : β ^ 2 ≠ η := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) k
  obtain ⟨-, -, -, -, hiff, -, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 k hk
  have hdiag : IsOrdinaryDiagGraph k η :=
    ⟨1, 1, one_mem _, fun h => by rw [hη, rootDiagUnit_one]; group⟩
  have hΘη := (hiff Θ hΘ η).1 hdiag
  intro h
  have h2 : (Θ β).2 ^ 2 = Multiplicative.ofAdd 1 := by
    rw [← Prod.pow_snd, ← map_pow, h, hΘη]
  have key : ∀ x : Multiplicative (ZMod (exactE TwistTag.E6.tag)), x ^ 2 = 1 := by
    change ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1
    decide
  have hne : (1 : Multiplicative (ZMod (exactE TwistTag.E6.tag))) ≠ Multiplicative.ofAdd 1 := by
    change (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd 1
    decide
  rw [key] at h2
  exact hne h2

theorem noNormalZ4OrZ2xZ4_E6_second_graph_class {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = 2 ^ f) (hF4 : InnerInvolutionInput (adjointGroup Tag.F4 k))
    (H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag k)))
    (hIH : inner (adjointGroup TwistTag.E6.tag k) ≤ H)
    (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k)
    (η : MulAut (adjointGroup TwistTag.E6.tag k))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹)
    {α φ : MulAut (adjointGroup TwistTag.E6.tag k)}
    (hφ : φ * α * φ⁻¹ = MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag k) * η) :
    NoNormalZ4OrZ2xZ4
      ↥(H ⊓ centralizer ({α} : Set (MulAut (adjointGroup TwistTag.E6.tag k)))) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  obtain ⟨htJ, -, -⟩ := secondGraphFullCentralizer_adjointGroup hf k hk
  obtain ⟨ht2, ht1⟩ := pinnedX_e6HighestRoot_one_sq h2
  have hF4' := fun τJ hτJ L hL => noNormalZ4OrZ2xZ4_inf_centralizer_inner_of_F4 k hF4
    (graphFixedImageF4Equiv (RingHom.id k) h2) htJ ht2 ht1 τJ hτJ L hL
  have hξ : ∀ g, ((MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag k) * η) g :
      ModGL TwistTag.E6.tag k) =
      pinnedX TwistTag.E6.tag k e6HighestRoot 1 *
        (diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) *
          (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹ := fun g => by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη]
  have hZJ := center_eq_bot_of_mulEquiv_adjointGroup k (graphFixedImageF4Equiv (RingHom.id k) h2)
  refine NoNormalZ4OrZ2xZ4.of_conj hφ ?_
  exact noNormalZ4OrZ2xZ4_inf_centralizer_xi (secondGraphFullCentralizer_adjointGroup hf k hk)
    diagramMap_E6_mul_self hZJ η hη _ hξ hF4' _ (inner_le_map_conj_of_le hIH φ)
    fun _ _ _ b _ => sq_ne_E6_graph hf k hk η hη b

theorem outerInvolutionInput_E6 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (hF4 : InnerInvolutionInput (adjointGroup .F4 K)) :
    OuterInvolutionInput (adjointGroup .E6 K) := by
  change OuterInvolutionInput (adjointGroup TwistTag.E6.tag K)
  intro H hIH α _ hαI hα
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have hΘα := hΘ α g a σ ε hga
  by_cases hσ1 : σ = 1
  · subst hσ1
    have hε2 : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
      have := ε.isLt
      change (ε : ℕ) < 2 at this
      omega
    rcases hε2 with h0 | h1
    ·
      exfalso
      refine hαI (mem_inner_of_conj_mul_rootDiagAut hf K hK hα2 g a ?_)
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
          (h : ModGL TwistTag.E6.tag K) = h := Units.ext (entrywise_id _)
      rw [hga h, h0, exactQ_zero, e1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
      group
    ·
      obtain ⟨ht, η, hη, hconj, hiff, -, -⟩ :=
        (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 K hK
      have hdiag : IsOrdinaryDiagGraph K α := by
        rw [hiff Θ hΘ, hΘα, h1, Nat.cast_one]
      rcases hconj α hdiag hα2 with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
      · exact (abelianNormalCardLeTwo_E6_graph_class hf K hK η hη H hIH hαI
          hφ).noNormalZ4OrZ2xZ4
      · exact noNormalZ4OrZ2xZ4_E6_second_graph_class hf K hK hF4 H hIH ht η hη hφ
  · exact (abelianNormalCardLeTwo_E6_field_class hf K hK Θ hΘ H hIH hαI hα
      (by rw [hΘα]; exact hσ1)).noNormalZ4OrZ2xZ4

theorem abelianNormalCardLeTwo_twistedE6_graph_class {f : ℕ} (hf : 1 ≤ f) (k K : Type)
    [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹)
    (H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))
    (hIH : inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H)
    {α φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ)}
    (hαI : α ∉ inner (graphFixedRootGroup TwistTag.E6 K σ)) (hα : φ * α * φ⁻¹ = η) :
    AbelianNormalCardLeTwo
      ↥(H ⊓ centralizer ({α} : Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨-, hD, -⟩ := even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  have hcent := even_twisted_E6_canonical_graph_full_pointwise_centralizer hf k K hk hK σ hσ η hη
  exact AbelianNormalCardLeTwo.of_conj hα (abelianNormalCardLeTwo_of_canonicalGraph hD hη hcent
    (not_mem_inner_of_conj hαI hα) _ (inner_le_map_conj_of_le hIH φ))

theorem sq_ne_twistedE6_graph {f : ℕ} (hf : 1 ≤ f) (hodd : Odd f) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹)
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : β ^ 2 ≠ η := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, -, -, -, -⟩, hσP, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  have hΘη : Θ η = σ := hΘ η 1 1 σ (by
    rw [map_one, map_one, one_mul, one_mul]
    exact MulEquiv.ext fun g => Subtype.ext (by rw [hη, hσP]))
  obtain ⟨σ', hσ', hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf K (by rw [hK]; rfl)
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  rw [hσσ'] at hord
  have hord2 : orderOf σ = 2 := hord
  have hσ2 : σ ^ 2 = 1 := by
    rw [← hord2]
    exact pow_orderOf_eq_one σ
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  intro h
  have hδ : Θ β ^ 2 = σ := by rw [← map_pow, h, hΘη]
  obtain ⟨s, -, -, hs⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_frobenius_pow_eq (by omega) hK' (Θ β)
  have h2 : ¬ 2 * f ∣ 2 * s := fun hd => by
    have h1 := (hs 2).2 hd
    rw [hδ] at h1
    rw [h1, orderOf_one] at hord2
    exact absurd hord2 (by decide)
  have h4 : 2 * f ∣ 4 * s := (hs 4).1 (by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hδ, hσ2])
  have h4' : 2 * f ∣ 2 * (2 * s) := by
    rw [show 2 * (2 * s) = 4 * s by ring]
    exact h4
  exact h2 (mul_dvd_mul_left 2 ((Nat.coprime_two_right.2 hodd).dvd_of_dvd_mul_left
    ((mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h4')))

@[expose] def TwistedE6SecondGraphInput
    (k K : Type) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ τJ : MulAut ↥((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
      (baseChangeGL (algebraMap k K))),
    (∀ x, (τJ x : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 * x *
      (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹) → AbelianNormalInner τJ

theorem noNormalZ4OrZ2xZ4_twistedE6_second_graph_class {f : ℕ} (hf : 1 ≤ f) (k K : Type)
    [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (hF4 : InnerInvolutionInput (adjointGroup Tag.F4 k))
    (H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))
    (hIH : inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H)
    (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹)
    {α φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ)}
    (hαI : α ∉ inner (graphFixedRootGroup TwistTag.E6 K σ))
    (hφ : φ * α * φ⁻¹ = MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η)
    (hsq : (∀ β : MulAut (graphFixedRootGroup TwistTag.E6 K σ), β ^ 2 ≠ η) ∨
      TwistedE6SecondGraphInput k K) :
    NoNormalZ4OrZ2xZ4
      ↥(H ⊓ centralizer ({α} : Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have h2K : (2 : K) = 0 := by
    have := congrArg (algebraMap k K) h2
    rwa [map_ofNat, map_zero] at this
  obtain ⟨htJ, -, -⟩ := secondGraphFullCentralizer_graphFixedRootGroup hf k K hk hK σ hσ
  obtain ⟨ht2, ht1⟩ := pinnedX_e6HighestRoot_one_sq h2K
  have hF4' := fun τJ hτJ L hL => noNormalZ4OrZ2xZ4_inf_centralizer_inner_of_F4 k hF4
    (graphFixedImageF4Equiv (algebraMap k K) h2) htJ ht2 ht1 τJ hτJ L hL
  have hξ : ∀ g, ((MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η) g :
      ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
        (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
          (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ := fun g => by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη]
  have hZJ := center_eq_bot_of_mulEquiv_adjointGroup k
    (graphFixedImageF4Equiv (algebraMap k K) h2)
  have hξI := not_mem_inner_of_conj hαI hφ
  have hηI : η ∉ inner (graphFixedRootGroup TwistTag.E6 K σ) := fun ⟨c, hc⟩ =>
    hξI ⟨⟨_, ht⟩ * c, by rw [map_mul, hc]⟩
  refine NoNormalZ4OrZ2xZ4.of_conj hφ ?_
  have hIH' := inner_le_map_conj_of_le hIH φ
  refine noNormalZ4OrZ2xZ4_inf_centralizer_xi
    (secondGraphFullCentralizer_graphFixedRootGroup hf k K hk hK σ hσ) diagramMap_E6_mul_self hZJ
    η hη _ hξ hF4' _ hIH' ?_
  rcases hsq with hsq | hY
  · exact fun _ _ _ b _ => hsq b
  · exact sq_ne_of_abelianNormalInner
      (secondGraphFullCentralizer_graphFixedRootGroup hf k K hk hK σ hσ) diagramMap_E6_mul_self
      hZJ η hη hηI _ hξ hY _ hIH'

theorem outerInvolutionInput_twistedE6 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hF4 : ∀ (k : Type) [Field k], Nat.card k = 2 ^ f →
      InnerInvolutionInput (adjointGroup .F4 k))
    (hY : Even f → ∀ (k : Type) [Field k] [Algebra k K], Nat.card k = 2 ^ f →
      TwistedE6SecondGraphInput k K) :
    OuterInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom) := by
  intro H hIH α _ hαI hα
  have hk := CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hf hK
    (σ := σ.toRingHom) hσ
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨ht, η, hη, -, -, hnoninner, -, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ.toRingHom hσ
  have hnc : ∀ c, α ≠ MulAut.conj c := fun c h => hαI ⟨c, h.symm⟩
  rcases hnoninner α hα2 hnc with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact (abelianNormalCardLeTwo_twistedE6_graph_class hf
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K hk hK σ.toRingHom hσ η hη H hIH hαI
        hφ).noNormalZ4OrZ2xZ4
  · refine noNormalZ4OrZ2xZ4_twistedE6_second_graph_class hf
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K hk hK σ.toRingHom hσ (hF4 _ hk) H hIH
      ht η hη hαI hφ ?_
    rcases Nat.even_or_odd f with hev | hodd
    · exact Or.inr (hY hev _ hk)
    · exact Or.inl (sq_ne_twistedE6_graph hf hodd K hK σ hσ η hη)

theorem exceptionalHypothesisOneInputs_of_inner
    (hin : ∀ (τ : Tag) (f : ℕ) (K : Type) [Field K], 1 ≤ f → Nat.card K = 2 ^ f →
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → InnerInvolutionInput (adjointGroup τ K))
    (hinT : ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) → InnerInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom))
    (hY : ∀ (f : ℕ) (K : Type) [Field K], 1 ≤ f → Even f → Nat.card K = (2 ^ f) ^ 2 →
      ∀ (k : Type) [Field k] [Algebra k K], Nat.card k = 2 ^ f → TwistedE6SecondGraphInput k K) :
    ExceptionalHypothesisOneInputs :=
  ⟨hin, fun f K _ hf hK => outerInvolutionInput_E6 hf K hK (hin .F4 f K hf hK (.inl rfl)),
    fun f K _ σ hf hK hσ => ⟨hinT f K σ hf hK hσ,
      outerInvolutionInput_twistedE6 hf K hK σ hσ (fun k _ hk => hin .F4 f k hf hk (.inl rfl))
        fun hev k _ _ hk => hY f K hf hev hK k hk⟩⟩

theorem exceptionalHypothesisOne_of_inner
    (hin : ∀ (τ : Tag) (f : ℕ) (K : Type) [Field K], 1 ≤ f → Nat.card K = 2 ^ f →
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → InnerInvolutionInput (adjointGroup τ K))
    (hinT : ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) → InnerInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom))
    (hY : ∀ (f : ℕ) (K : Type) [Field K], 1 ≤ f → Even f → Nat.card K = (2 ^ f) ^ 2 →
      ∀ (k : Type) [Field k] [Algebra k K], Nat.card k = 2 ^ f → TwistedE6SecondGraphInput k K) :
    ExceptionalHypothesisOne :=
  exceptionalHypothesisOne_of_inputs (exceptionalHypothesisOneInputs_of_inner hin hinT hY)

end CFSG.SeitzReduction
