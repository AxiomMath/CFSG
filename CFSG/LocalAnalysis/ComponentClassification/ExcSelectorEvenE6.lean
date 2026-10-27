module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenGFE
public import CFSG.LieType.Chevalley.CLSEvenE6AllInvolutionFourGroup
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergBNEvenInnerInvolutionOddCore

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.E6SecondGraphFixed
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Graph

variable {G : Type} [Group G] {C J : Subgroup G}

theorem not_smallType_of_fixed_iff_simple (hJC : J ≤ C) [IsSimpleGroup J]
    (hnot : ¬ SmallType J) {η : MulAut C} (hfix : ∀ g : C, η g = g ↔ (g : G) ∈ J)
    {L : Subgroup C} (hL : Assembly.IsComponentOf L (fixedSubgroup η)) : ¬ SmallType L := by
  have hF : fixedSubgroup η = J.subgroupOf C := by
    ext g
    exact hfix g
  have eJ : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  have : IsSimpleGroup (J.subgroupOf C) := (MulEquiv.isSimpleGroup_congr eJ).2 inferInstance
  rw [hF] at hL
  rw [eq_of_isComponentOf_of_isSimpleGroup hL, smallType_congr eJ]
  exact hnot

theorem not_isComponentOf_of_fixed_iff_centralizer {H : Type} [Group H] (hJC : J ≤ C)
    (e : J ≃* H) {t : G} (htJ : t ∈ J) {ξ : MulAut C}
    (hfix : ∀ g : C, ξ g = g ↔ (g : G) ∈ J ∧ t * g = g * t)
    (hH : ∀ L' : Subgroup H, ¬ Assembly.IsComponentOf L' (centralizer {e ⟨t, htJ⟩}))
    (L : Subgroup C) : ¬ Assembly.IsComponentOf L (fixedSubgroup ξ) := by
  set ι : H →* C := (Subgroup.inclusion hJC).comp e.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    (Subgroup.inclusion_injective hJC).comp e.symm.injective
  have hF : fixedSubgroup ξ = (centralizer {e ⟨t, htJ⟩}).map ι := by
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
  rw [hF] at hL
  exact hH _ (isComponentOf_comap_of_injective ι hιinj hL)

variable {k : Type} [Field k] [Finite k]

theorem graph_noSmall {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) {P t : G}
    (hcan : CanonicalGraphFixedSubgroup C J P) (e : J ≃* adjointGroup Tag.F4 k)
    (hsec : SecondGraphFixedSubgroup C J P t e) {η : MulAut C}
    (hη : ∀ g : C, (η g : G) = P * g * P⁻¹) {α : MulAut C}
    (hcl : (∃ φ : MulAut C, φ * α * φ⁻¹ = η) ∨
      ∃ (htC : t ∈ C) (φ : MulAut C), φ * α * φ⁻¹ = MulAut.conj ⟨t, htC⟩ * η)
    {L : Subgroup C} (hL : Assembly.IsComponentOf L (fixedSubgroup α))
    (hLn : (L.subgroupOf (fixedSubgroup α)).Normal) : ¬ SmallType L := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  obtain ⟨η₀, hη₀, -, hJC, hfix₀, hsimple, -⟩ := hcan
  have : IsSimpleGroup J := hsimple
  have hη₀η : η₀ = η := MulEquiv.ext fun g => Subtype.ext ((hη₀ g).trans (hη g).symm)
  rw [hη₀η] at hfix₀
  obtain ⟨htJ, hJC', η₁, hη₁, -, -, -, hfix₁, -, hord, -, -⟩ := hsec
  have hη₁η : η₁ = η := MulEquiv.ext fun g => Subtype.ext ((hη₁ g).trans (hη g).symm)
  rw [hη₁η] at hfix₁
  rcases hcl with ⟨φ, hφ⟩ | ⟨htC, φ, hφ⟩
  · refine not_smallType_of_conj hφ (fun L' hL' _ => ?_) hL hLn
    obtain ⟨-, hn⟩ := adjointGroup_F4_even hf hk
    exact not_smallType_of_fixed_iff_simple hJC
      (fun hs => hn ((smallType_congr e).1 hs)) hfix₀ hL'
  · refine not_smallType_of_conj hφ (fun L' hL' _ => ?_) hL hLn
    exfalso
    have hfix' : ∀ g : C, (MulAut.conj (⟨t, htC⟩ : C) * η) g = g ↔
        (g : G) ∈ J ∧ t * g = g * t := hfix₁
    refine not_isComponentOf_of_fixed_iff_centralizer hJC e htJ hfix' (fun L'' hL'' => ?_) L' hL'
    have hne : e ⟨t, htJ⟩ ≠ 1 := fun h => by
      rw [h, orderOf_one] at hord
      exact absurd hord (by decide)
    have hsq : (e ⟨t, htJ⟩) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    rw [← fixedSubgroup_conj] at hL''
    exact not_isComponentOf_fixedSubgroup_conj (RootWeightDatum.ordinary Tag.F4) hne hsq L'' hL''

end Graph

section Assembly

open CFSG.LieType.Chevalley.EvenE6AllInvolution (mem_inner_of_conj_mul_rootDiagAut)

theorem not_smallType_of_derived {G : Type} [Group G] {C J : Subgroup G} {α β ψ : MulAut C}
    (hψ : (fixedSubgroup α).map ψ.toMonoidHom = fixedSubgroup β) (hJC : J ≤ C) [IsSimpleGroup J]
    (hder : ⁅fixedSubgroup β, fixedSubgroup β⁆ = J.subgroupOf C) (hnot : ¬ SmallType J)
    {L : Subgroup C} (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  have eJ : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  have : IsSimpleGroup (J.subgroupOf C) := (MulEquiv.isSimpleGroup_congr eJ).2 inferInstance
  have hL' := isComponentOf_map_of_equiv ψ hL
  rw [hψ] at hL'
  have heq := eq_of_isComponentOf_of_commutator_eq hder hL'
  have e : L ≃* J := (L.equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    ((MulEquiv.subgroupCongr heq).trans eJ)
  exact fun hs => hnot ((smallType_congr e).1 hs)

variable {k : Type} [Field k] [Finite k]

theorem even_E6_noSmall {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (β : MulAut (adjointGroup TwistTag.E6.tag k)) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    {L : Subgroup (adjointGroup TwistTag.E6.tag k)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup β))
    (hLn : (L.subgroupOf (fixedSubgroup β)).Normal) : ¬ SmallType L := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  by_cases hin : β ∈ inner (adjointGroup TwistTag.E6.tag k)
  · obtain ⟨c, rfl⟩ := hin
    have hc1 : c ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    have hc2 : c ^ 2 = 1 := by
      apply mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
      rw [map_pow, hβ2, map_one]
    exact absurd hL
      (not_isComponentOf_fixedSubgroup_conj (RootWeightDatum.ordinary Tag.E6) hc1 hc2 L)
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
      refine hin (mem_inner_of_conj_mul_rootDiagAut hk hf g a ?_ hβ2)
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
      exact graph_noSmall hf hk hcan e hsec hη
        ((hclass β hgraph hβ2).imp id fun ⟨φ, hφ⟩ => ⟨ht, φ, hφ⟩) hL hLn
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
      obtain ⟨-, hJC, hder, -, hsimp, -⟩ := hJ0
      have hβδ : diagramConjAut TwistTag.E6 k ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ = β' :=
        MulEquiv.ext fun u => Subtype.ext ((coe_entrywiseAdjointAut _ σ u).trans (hβ' u).symm)
      rw [← hβδ] at hψ
      have hk' := card_fixSubfield_of_pow he hk hσe
      obtain ⟨-, hn⟩ := adjointGroup_E6_even he hk'
      exact not_smallType_of_derived hψ hJC hder
        (fun hs => hn ((smallType_congr (fixedFieldImageEquiv σ)).2 hs)) hL
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
      have hcard := Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two he hk'
        σ.toRingHom hσe
      exact not_smallType_of_derived hψ hJC hder
        (not_smallType_of_card_ordTwistedE6 (exceptional_fixed_center_trivial TwistTag.E6 k σ) he
          hcard) hL

theorem even_twistedE6_noSmall {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (hβ2 : β ^ 2 = 1)
    (hβ1 : β ≠ 1) {L : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup β))
    (hLn : (L.subgroupOf (fixedSubgroup β)).Normal) : ¬ SmallType L := by
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'
  have hσ2 : σ ^ TwistTag.E6.order = 1 := pow_eq_one_of_apply_eq_pow σ hK hσ
  by_cases hin : β ∈ inner (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  · obtain ⟨c, rfl⟩ := hin
    have hc1 : c ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
    have hc2 : c ^ 2 = 1 := by
      apply mulAut_conj_injective_of_center_eq_bot hZ
      rw [map_pow, hβ2, map_one]
    exact absurd hL
      (not_isComponentOf_fixedSubgroup_conj (RootWeightDatum.fixed TwistTag.E6 σ hσ2) hc1 hc2 L)
  set k := GaloisField 2 f
  have hk : Nat.card k = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  let _ : Algebra k K := ι.toAlgebra
  obtain ⟨ht, η, hη, -, -, hclass, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ.toRingHom hσ
  obtain ⟨-, ⟨hcan, -, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ.toRingHom hσ
  obtain ⟨-, -, -, -, -, ⟨e, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ.toRingHom hσ
  have hout : ∀ c, β ≠ MulAut.conj c := fun c h => hin ⟨c, h.symm⟩
  exact graph_noSmall hf hk hcan e hsec hη
    ((hclass β hβ2 hout).imp id fun ⟨φ, hφ⟩ => ⟨ht, φ, hφ⟩) hL hLn

end Assembly

end CFSG.ComponentClassification.ExcSelector
