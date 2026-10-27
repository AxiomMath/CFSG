module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenF4
public import CFSG.LieType.Chevalley.CLSEvenE6AllInvolutionFourGroup

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Chevalley.E6SecondGraphFixed
open CFSG.LieType.Chevalley.EvenE6AllInvolution (mem_inner_of_conj_mul_rootDiagAut)

theorem pPrimeCore_eq_bot_of_isCharacteristicP {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (h : IsCharacteristicP p H) : pPrimeCore p H = ⊥ := by
  have hO : (pCore p H).Normal := pCore_normal
  have hO' : (pPrimeCore p H).Normal := pPrimeCore_normal
  have hinf : pPrimeCore p H ⊓ pCore p H = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup p (pCore p H)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (pPrimeCore_coprime_card (p := p) (G := H)).symm
  have hle : pPrimeCore p H ≤ centralizer (pCore p H : Set H) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.commute_of_normal_of_disjoint _ _ hO' hO (disjoint_iff.2 hinf) x y hx hy).symm.eq
  rw [eq_bot_iff, ← hinf]
  exact le_inf le_rfl (hle.trans h)

theorem not_isPComponent_of_isCharacteristicP {H : Type*} [Group H] [Finite H]
    (h : IsCharacteristicP 2 H) (L : Subgroup H) : ¬ IsPComponent 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hL
  obtain ⟨hs, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).1 hL
  have hcore : pPrimeCore 2 L = ⊥ := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hs
    rw [pPrimeCore_eq_bot_of_isCharacteristicP h, le_bot_iff,
      map_eq_bot_iff_of_injective _ L.subtype_injective] at h1
    exact h1
  exact RootWeightDatum.not_isComponent_of_isCharacteristicP h L
    ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)).1 hq, hs⟩

set_option linter.style.haveILetI false in
theorem isSimpleGroup_of_isPComponent_of_mulEquiv_simple {X Y : Type*} [Group X] [Finite X]
    [Group Y] [IsSimpleGroup Y] (e : X ≃* Y) {P : Subgroup X} (hP : IsPComponent 2 P) :
    IsSimpleGroup ↥P := by
  haveI : IsSimpleGroup X := e.isSimpleGroup
  have htop := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hP
  exact ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans e)).isSimpleGroup

theorem nonempty_equiv_of_isPComponent_of_derived {X G Y : Type*} [Group X] [Finite X] [Group G]
    [Finite G] [Group Y] [IsSimpleGroup Y] {F : Subgroup G} (Ψ : X ≃* F)
    (E : ↥⁅F, F⁆ ≃* Y) {P : Subgroup X} (hP : IsPComponent 2 P) :
    Nonempty (↥P ≃* Y) := by
  have hD : IsSimpleGroup (commutator ↥F) := ((commutatorSubtypeEquiv F).trans E).isSimpleGroup
  have hPeq := eq_commutator_of_isPComponent hD
    (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ hP)
  exact ⟨(P.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).trans
    ((MulEquiv.subgroupCongr hPeq).trans ((commutatorSubtypeEquiv F).trans E))⟩

theorem isSimpleGroup_of_isPComponent_of_derived {X G Y : Type*} [Group X] [Finite X]
    [Group G] [Finite G] [Group Y] [IsSimpleGroup Y] {F : Subgroup G} (Ψ : X ≃* F)
    (E : ↥⁅F, F⁆ ≃* Y) {P : Subgroup X} (hP : IsPComponent 2 P) :
    IsSimpleGroup ↥P := by
  obtain ⟨e⟩ := nonempty_equiv_of_isPComponent_of_derived Ψ E hP
  exact e.isSimpleGroup

theorem nonempty_fusionZStar_equiv_of_derived {X G Y : Type*} [Group X] [Finite X] [Group G]
    [Finite G] [Group Y] [IsSimpleGroup Y] {F : Subgroup G} (Ψ : X ≃* F) (E : ↥⁅F, F⁆ ≃* Y)
    {P : Subgroup X} (hP : IsPComponent 2 P) : Nonempty (P ⧸ Open.fusionZStar P ≃* Y) := by
  obtain ⟨e⟩ := nonempty_equiv_of_isPComponent_of_derived Ψ E hP
  exact GrSLit.nonempty_fusionZStar_equiv_of_simple hP e

theorem isCharacteristicP_centralizer_involution
    {K : Type} [Field K] [Finite K] [CharP K 2] (D : RootWeightDatum K) {c : D.group}
    (hc : c ≠ 1) (hc2 : c ^ 2 = 1) : IsCharacteristicP 2 (centralizer ({c} : Set D.group)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := zpowers c with hQ
  have hQp : IsPGroup 2 Q := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show ((2 : ℕ) : ℤ) = 2 from rfl, zpow_two, ← sq, hc2, one_zpow, Subgroup.coe_one]
  have hQ1 : Q ≠ ⊥ := fun h => hc (by
    have : c ∈ Q := Subgroup.mem_zpowers c
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hcent : centralizer (Q : Set D.group) = centralizer ({c} : Set D.group) := by
    rw [hQ, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hcent]
  exact (D.defining_characteristic_root_local_groups_component_free 2 Q hQp hQ1
    (centralizer (Q : Set D.group)) (Or.inr rfl)).1

theorem not_isPComponent_of_fixed_iff_centralizer {G H : Type*} [Group G] [Group H] [Finite H]
    {C J : Subgroup G} (hJC : J ≤ C) (e : J ≃* H) {t : G} (htJ : t ∈ J) {ξ : MulAut C}
    (hfix : ∀ g : C, ξ g = g ↔ (g : G) ∈ J ∧ t * g = g * t)
    (hH : IsCharacteristicP 2 (centralizer ({e ⟨t, htJ⟩} : Set H)))
    (L : Subgroup (fixedSubgroup ξ)) : ¬ IsPComponent 2 L := by
  set ι : H →* C := (Subgroup.inclusion hJC).comp e.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    (Subgroup.inclusion_injective hJC).comp e.symm.injective
  have hF : fixedSubgroup ξ = (centralizer ({e ⟨t, htJ⟩} : Set H)).map ι := by
    ext g
    change ξ g = g ↔ _
    rw [hfix g, Subgroup.mem_map]
    constructor
    · rintro ⟨hgJ, hgt⟩
      refine ⟨e ⟨g, hgJ⟩, ?_, ?_⟩
      · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hgt.symm
      · apply Subtype.ext
        simp [hι]
    · rintro ⟨h, hh, rfl⟩
      have hmem : ((ι h : C) : G) ∈ J := (e.symm h).2
      refine ⟨hmem, ?_⟩
      rw [mem_centralizer_singleton_iff] at hh
      have h1 : e.symm h * ⟨t, htJ⟩ = ⟨t, htJ⟩ * e.symm h := by
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hh
      exact (congrArg Subtype.val h1).symm
  intro hL
  exact not_isPComponent_of_isCharacteristicP hH _
    (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
      ((MulEquiv.subgroupCongr hF).trans
        ((centralizer ({e ⟨t, htJ⟩} : Set H)).equivMapOfInjective ι hιinj).symm) hL)

theorem lieModel_E6_of_mulEquiv
    {G : Type} [Group G] {k : Type} [Field k] [Finite k] {e : ℕ} (he : 1 ≤ e)
    (hk : Nat.card k = 2 ^ e) (E : G ≃* adjointGroup .E6 k) :
    StatedLieAdmissible .E6 0 2 e ∧ LieModel G .E6 0 2 e :=
  ⟨⟨Nat.prime_two, he, rfl⟩, Or.inr (Or.inl ⟨rfl, by decide,
    ⟨⟨Nat.prime_two, he, rfl⟩, untwistedChevalleyModel_of_mulEquiv hk E⟩⟩)⟩

theorem lieModel_twistedE6_of_mulEquiv
    {G : Type} [Group G] {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = (2 ^ e) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ e))
    (E : G ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
    StatedLieAdmissible .twistedE6 0 2 e ∧ LieModel G .twistedE6 0 2 e := by
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two he K hK σ.toRingHom
    hσ).2.2.1
  obtain ⟨e'⟩ := LieType.Chevalley.nonempty_derivedCentralQuotient_equiv hperf
    (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  have hadm : StatedLieAdmissible .twistedE6 0 2 e := ⟨Nat.prime_two, he, rfl⟩
  exact ⟨hadm, Or.inr (Or.inl ⟨rfl, by decide, hadm, K, inferInstance, inferInstance, hK,
    σ.toRingHom, hσ, ⟨E.trans e'.symm⟩⟩)⟩

theorem even_graph_actual
    {G : Type} [Group G] {C J : Subgroup G} [Finite C] {P₀ t : G} {k : Type} [Field k]
    [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hcan : CanonicalGraphFixedSubgroup C J P₀) (e : J ≃* adjointGroup Tag.F4 k)
    (hsec : SecondGraphFixedSubgroup C J P₀ t e) {η : MulAut C}
    (hη : ∀ g : C, (η g : G) = P₀ * g * P₀⁻¹) {α : MulAut C}
    (hcl : (∃ φ : MulAut C, φ * α * φ⁻¹ = η) ∨
      ∃ (htC : t ∈ C) (φ : MulAut C), φ * α * φ⁻¹ = MulAut.conj ⟨t, htC⟩ * η)
    {X : Type} [Group X] [Finite X] (Ψ : X ≃* fixedSubgroup α) {P : Subgroup X}
    (hP : IsPComponent 2 P) :
    IsSimpleGroup ↥P ∧ StatedLieAdmissible .F4 0 2 f ∧
      LieModel (P ⧸ Open.fusionZStar P) .F4 0 2 f := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : Finite (ModGL Tag.F4 k) := finite_modGL
  obtain ⟨η₀, hη₀, -, hJC, hfix₀, -, -⟩ := hcan
  have hη₀η : η₀ = η := MulEquiv.ext fun g => Subtype.ext ((hη₀ g).trans (hη g).symm)
  rw [hη₀η] at hfix₀
  obtain ⟨htJ, hJC', η₁, hη₁, -, -, -, hfix₁, -, hord, -, -⟩ := hsec
  have hη₁η : η₁ = η := MulEquiv.ext fun g => Subtype.ext ((hη₁ g).trans (hη g).symm)
  rw [hη₁η] at hfix₁
  rcases hcl with ⟨φ, hφ⟩ | ⟨htC, φ, hφ⟩
  · have hc : MulAut.congr φ α = η :=
      (MulEquiv.ext fun _ => rfl : MulAut.congr φ α = φ * α * φ⁻¹).trans hφ
    have hF : fixedSubgroup (MulAut.congr φ α) = J.subgroupOf C := by
      rw [hc]
      ext g
      exact hfix₀ g
    have := (ExcSelector.adjointGroup_F4_even hf hk).1
    let Φ₀ : X ≃* ↥(adjointGroup Tag.F4 k) :=
      (Ψ.trans (fixedSubgroupCongrEquiv φ α)).trans ((MulEquiv.subgroupCongr hF).trans
        ((Subgroup.subgroupOfEquivOfLe hJC).trans e))
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Φ₀ hP
    exact ⟨isSimpleGroup_of_isPComponent_of_mulEquiv_simple Φ₀ hP,
      lieModel_F4_of_mulEquiv hf hk E⟩
  · exfalso
    have hc : MulAut.congr φ α = MulAut.conj (⟨t, htC⟩ : C) * η :=
      (MulEquiv.ext fun _ => rfl : MulAut.congr φ α = φ * α * φ⁻¹).trans hφ
    have hfix' : ∀ g : C, (MulAut.conj (⟨t, htC⟩ : C) * η) g = g ↔
        (g : G) ∈ J ∧ t * g = g * t := hfix₁
    have hne : e ⟨t, htJ⟩ ≠ 1 := fun h => by
      rw [h, orderOf_one] at hord
      exact absurd hord (by decide)
    have hsq : (e ⟨t, htJ⟩) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have hH := isCharacteristicP_centralizer_involution (RootWeightDatum.ordinary (K := k) Tag.F4)
      hne hsq
    have hF : fixedSubgroup (MulAut.congr φ α) =
        fixedSubgroup (MulAut.conj (⟨t, htC⟩ : C) * η) := by rw [hc]
    exact not_isPComponent_of_fixed_iff_centralizer hJC e htJ hfix' hH _
      (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
        ((Ψ.trans (fixedSubgroupCongrEquiv φ α)).trans (MulEquiv.subgroupCongr hF)) hP)

theorem even_graph_lieModel
    {G : Type} [Group G] {C J : Subgroup G} [Finite C] {P₀ t : G} {k : Type} [Field k]
    [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hcan : CanonicalGraphFixedSubgroup C J P₀) (e : J ≃* adjointGroup Tag.F4 k)
    (hsec : SecondGraphFixedSubgroup C J P₀ t e) {η : MulAut C}
    (hη : ∀ g : C, (η g : G) = P₀ * g * P₀⁻¹) {α : MulAut C}
    (hcl : (∃ φ : MulAut C, φ * α * φ⁻¹ = η) ∨
      ∃ (htC : t ∈ C) (φ : MulAut C), φ * α * φ⁻¹ = MulAut.conj ⟨t, htC⟩ * η)
    {X : Type} [Group X] [Finite X] (Ψ : X ≃* fixedSubgroup α) {P : Subgroup X}
    (hP : IsPComponent 2 P) :
    StatedLieAdmissible .F4 0 2 f ∧ LieModel (P ⧸ Open.fusionZStar P) .F4 0 2 f :=
  (even_graph_actual hf hk hcan e hsec hη hcl Ψ hP).2

theorem even_E6_outer_actual_tag
    {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (β : MulAut (adjointGroup TwistTag.E6.tag k)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (adjointGroup TwistTag.E6.tag k)) {X : Type} [Group X] [Finite X]
    (Ψ : X ≃* fixedSubgroup β) {P : Subgroup X} (hP : IsPComponent 2 P) :
    IsSimpleGroup ↥P ∧ ∃ (τ' : StatedLieTag) (n' f' : ℕ),
      (τ' = .F4 ∨ τ' = .E6 ∨ τ' = .twistedE6) ∧
      StatedLieAdmissible τ' n' 2 f' ∧ LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f' := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
  obtain ⟨-, -, hexist⟩ :=
    ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) k
  obtain ⟨g, a, σ, ε, hexpr⟩ := hexist β
  by_cases hσ : σ = 1
  · subst hσ
    have hid : ∀ h : ModGL TwistTag.E6.tag k,
        Units.map (entrywiseHom (1 : k ≃+* k).toRingHom) h = h := fun h =>
      Units.ext (entrywise_id _)
    obtain ⟨ε, hε⟩ := ε
    have hε' : ε = 0 ∨ ε = 1 := by
      change ε < 2 at hε
      omega
    rcases hε' with rfl | rfl
    ·
      exfalso
      refine hβo (mem_inner_of_conj_mul_rootDiagAut hk hf g a ?_ hβ2)
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e := hexpr h
      have hQ0 : exactQ TwistTag.E6.tag k ((⟨0, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) = 1 :=
        pow_zero _
      rw [hQ0, hid, mul_one, inv_one, mul_one] at e
      rw [e, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    ·
      have hQ1 : exactQ TwistTag.E6.tag k ((⟨1, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
          diagramMap TwistTag.E6 k := pow_one _
      set M := GaloisField 2 (2 * f)
      have hM : Nat.card M = (2 ^ f) ^ 2 := by
        rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
      obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hM
      let _ : Algebra k M := ι.toAlgebra
      have hσM : ∀ c : M, iterateFrobenius M 2 f c = c ^ 2 ^ f := fun c =>
        iterateFrobenius_def (p := 2) f c
      obtain ⟨ht, η, hη, hclass, -⟩ :=
        (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 k hk
      obtain ⟨⟨hcan, -, -⟩, -⟩ :=
        even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k M hk hM _ hσM
      obtain ⟨-, -, -, -, ⟨e, -, -, hsec⟩, -⟩ :=
        even_E6_twisted_E6_second_graph_fixed_subgroup f hf k M hk hM _ hσM
      have hgraph : E6GraphFullCoset.IsOrdinaryDiagGraph k β := ⟨g, a, g.2, fun h => by
        have e := hexpr h
        rw [hQ1, hid] at e
        refine e.trans ?_
        group⟩
      obtain ⟨hPsimp, hmodel⟩ := even_graph_actual hf hk hcan e hsec hη
        ((hclass β hgraph hβ2).imp id fun ⟨φ, hφ⟩ => ⟨ht, φ, hφ⟩) Ψ hP
      exact ⟨hPsimp, .F4, 0, f, Or.inl rfl, hmodel⟩
  ·
    obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
      ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) k
    have hσ2 : σ ^ 2 = 1 := hsq β g a σ ε hexpr hβ2
    obtain ⟨hfe, hσc, -⟩ := hfacts 2 f Nat.prime_two hf hk σ hσ2 hσ
    obtain ⟨e, rfl⟩ : ∃ e, f = 2 * e := ⟨f / 2, (Nat.two_mul_div_two_of_even hfe).symm⟩
    have he : 1 ≤ e := by omega
    have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [hσc, Nat.mul_div_cancel_left e two_pos]
    have hββ : β * β = 1 := by rw [← sq]; exact hβ2
    obtain ⟨hD0, hD1⟩ :=
      even_exceptional_quadratic_field_graph_field_involution_descent he k hk σ.toRingHom hσe
    obtain ⟨hJ0, hJ1⟩ := even_E6_canonical_field_graph_field_derived_fixed_subgroups he k hk σ hσe
    obtain ⟨ε, hε⟩ := ε
    have hε' : ε = 0 ∨ ε = 1 := by
      change ε < 2 at hε
      omega
    rcases hε' with rfl | rfl
    ·
      have hQ0 : exactQ TwistTag.E6.tag k ((⟨0, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) = 1 :=
        pow_zero _
      obtain ⟨β', hβ', hβα⟩ := hD0 TwistTag.E6.tag
      obtain ⟨ψ, -, hψ, -⟩ := (hβα g a).2 β (fun u => by
        have h := hexpr u
        rw [hQ0, mul_one, inv_one, mul_one] at h
        exact h) hββ
      obtain ⟨-, hJC, hder, -, -, -⟩ := hJ0
      have hβδ : diagramConjAut TwistTag.E6 k ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ = β' :=
        MulEquiv.ext fun u => Subtype.ext ((coe_entrywiseAdjointAut _ σ u).trans (hβ' u).symm)
      rw [← hβδ] at hψ
      have hk' := ExcSelector.card_fixSubfield_of_pow he hk hσe
      have : IsSimpleGroup ↥(adjointGroup TwistTag.E6.tag (fixSubfield σ)) :=
        (ExcSelector.adjointGroup_E6_even he hk').1
      let Φ₀ := (Ψ.trans ((fixedSubgroup β).equivMapOfInjective ψ.toMonoidHom ψ.injective)).trans
          (MulEquiv.subgroupCongr hψ)
      let E₀ := (MulEquiv.subgroupCongr hder).trans
          ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm)
      have hPsimp : IsSimpleGroup ↥P := isSimpleGroup_of_isPComponent_of_derived Φ₀ E₀ hP
      obtain ⟨E⟩ := nonempty_fusionZStar_equiv_of_derived Φ₀ E₀ hP
      exact ⟨hPsimp, .E6, 0, e, Or.inr (Or.inl rfl), lieModel_E6_of_mulEquiv he hk' E⟩
    ·
      have hQ1 : exactQ TwistTag.E6.tag k ((⟨1, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
          diagramMap TwistTag.E6 k := pow_one _
      obtain ⟨β', hβ', hβα⟩ := hD1
      obtain ⟨ψ, -, hψ, -⟩ := (hβα g a).2 β (fun u => by
        have h := hexpr u
        rw [hQ1] at h
        exact h) hββ
      obtain ⟨-, hJC, hder, -, hsimp, -⟩ := hJ1
      have hβγδ : diagramConjAut TwistTag.E6 k ^ 1 * entrywiseAdjointAut TwistTag.E6.tag σ = β' :=
        MulEquiv.ext fun u => Subtype.ext (((coe_diagramConjAut TwistTag.E6 k
          (entrywiseAdjointAut TwistTag.E6.tag σ u)).trans
            (by rw [coe_entrywiseAdjointAut])).trans (hβ' u).symm)
      rw [← hβγδ] at hψ
      have hk' : Nat.card k = (2 ^ e) ^ 2 := by rw [hk, ← pow_mul, mul_comm]
      let Φ₀ := (Ψ.trans ((fixedSubgroup β).equivMapOfInjective ψ.toMonoidHom ψ.injective)).trans
          (MulEquiv.subgroupCongr hψ)
      let E₀ := (MulEquiv.subgroupCongr hder).trans (Subgroup.subgroupOfEquivOfLe hJC)
      have hPsimp : IsSimpleGroup ↥P := isSimpleGroup_of_isPComponent_of_derived Φ₀ E₀ hP
      obtain ⟨E⟩ := nonempty_fusionZStar_equiv_of_derived Φ₀ E₀ hP
      exact ⟨hPsimp, .twistedE6, 0, e, Or.inr (Or.inr rfl),
        lieModel_twistedE6_of_mulEquiv he hk' σ hσe E⟩

theorem even_E6_outer_lieModel_tag
    {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (β : MulAut (adjointGroup TwistTag.E6.tag k)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (adjointGroup TwistTag.E6.tag k)) {X : Type} [Group X] [Finite X]
    (Ψ : X ≃* fixedSubgroup β) {P : Subgroup X} (hP : IsPComponent 2 P) :
    ∃ (τ' : StatedLieTag) (n' f' : ℕ), (τ' = .F4 ∨ τ' = .E6 ∨ τ' = .twistedE6) ∧
      StatedLieAdmissible τ' n' 2 f' ∧ LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f' :=
  (even_E6_outer_actual_tag hf hk β hβ2 hβo Ψ hP).2

theorem even_E6_outer_lieModel
    {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (β : MulAut (adjointGroup TwistTag.E6.tag k)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (adjointGroup TwistTag.E6.tag k)) {X : Type} [Group X] [Finite X]
    (Ψ : X ≃* fixedSubgroup β) {P : Subgroup X} (hP : IsPComponent 2 P) :
    ∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' 2 f' ∧
      LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f' := by
  obtain ⟨τ', n', f', -, h⟩ := even_E6_outer_lieModel_tag hf hk β hβ2 hβo Ψ hP
  exact ⟨τ', n', f', h⟩

theorem even_twistedE6_outer_actual
    {M : Type} [Field M] [Finite M] {f : ℕ} (hf : 1 ≤ f) (hM : Nat.card M = (2 ^ f) ^ 2)
    (σ : M ≃+* M) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.E6 M σ.toRingHom)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom)) {X : Type} [Group X]
    [Finite X] (Ψ : X ≃* fixedSubgroup β) {P : Subgroup X} (hP : IsPComponent 2 P) :
    IsSimpleGroup ↥P ∧ StatedLieAdmissible .F4 0 2 f ∧
      LieModel (P ⧸ Open.fusionZStar P) .F4 0 2 f := by
  set k := GaloisField 2 f
  have hk : Nat.card k = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hM
  let _ : Algebra k M := ι.toAlgebra
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  obtain ⟨ht, η, hη, -, -, hclass, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 M hM σ.toRingHom hσ
  obtain ⟨-, ⟨hcan, -, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k M hk hM σ.toRingHom hσ
  obtain ⟨-, -, -, -, -, ⟨e, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k M hk hM σ.toRingHom hσ
  have hout : ∀ c, β ≠ MulAut.conj c := fun c h => hβo ⟨c, h.symm⟩
  exact even_graph_actual hf hk hcan e hsec hη
    ((hclass β hβ2 hout).imp id fun ⟨φ, hφ⟩ => ⟨ht, φ, hφ⟩) Ψ hP

theorem even_twistedE6_outer_lieModel
    {M : Type} [Field M] [Finite M] {f : ℕ} (hf : 1 ≤ f) (hM : Nat.card M = (2 ^ f) ^ 2)
    (σ : M ≃+* M) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.E6 M σ.toRingHom)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom)) {X : Type} [Group X]
    [Finite X] (Ψ : X ≃* fixedSubgroup β) {P : Subgroup X} (hP : IsPComponent 2 P) :
    StatedLieAdmissible .F4 0 2 f ∧ LieModel (P ⧸ Open.fusionZStar P) .F4 0 2 f :=
  (even_twistedE6_outer_actual hf hM σ hσ β hβ2 hβo Ψ hP).2

theorem evenOuterFamilyInput_E6
    : EvenOuterFamilyInput .E6 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hu
  have : Finite (ModGL .E6 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E6 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact Or.inl (even_E6_outer_lieModel hf hF β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP)

theorem evenOuterFamilyInput_twistedE6
    : EvenOuterFamilyInput .twistedE6 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact Or.inl ⟨.F4, 0, f,
    even_twistedE6_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP⟩

end CFSG.ComponentClassification.CatLeafProof
