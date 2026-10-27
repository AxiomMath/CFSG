module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutExc
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.Assembly.LowTwoRank

section E6Diag


@[expose] def Up34DiagE6 : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 5 ≤ ℓ → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = ℓ ^ f → ∀ x : MulAut (adjointGroup Tag.E6 K), x ^ 3 = 1 →
      x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K) →
      x ∈ e6Inndiag K → NoL34Layer x

end E6Diag

section E6


theorem noL34Layer_entrywise_e6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hcard : Nat.card (fixSubfield σ) = ℓ ^ d) :
    NoL34Layer (entrywiseAdjointAut Tag.E6 σ) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 ℓ d :=
    ⟨⟨hℓ, hd, rfl⟩, untwisted_adjointGroup hcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e6_simplicity _ ℓ d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO σ hℓ2 (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp (exists_noncomm_of_center_bot hZ)

theorem noL34Layer_of_not_mem_e6Inndiag (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) {x : MulAut (adjointGroup Tag.E6 K)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ e6Inndiag K) : NoL34Layer x := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨σ, hσo, hpf, δ, hδ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ hf K hK
    Nat.prime_three (by norm_num) hx3 hxo
  have hd : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
  have hcard : Nat.card (fixSubfield σ) = ℓ ^ (f / 3) := by
    have := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hK σ).2
    rwa [hσo] at this
  have h1 : NoL34Layer (δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹) :=
    noL34Layer_conj δ⁻¹ (noL34Layer_entrywise_e6 hO hℓ hℓ2 hd σ hcard)
  have h2 : δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹ = x := by
    rw [← hδ]
    group
  rwa [h2] at h1

theorem noL34OuterAt_e6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hD : Up34DiagE6) : NoL34OuterAt FamE6 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E6 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.E6 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  refine noL34Layer_congr θ ?_
  by_cases hdiag : MulAut.congr θ ψ ∈ e6Inndiag F
  · exact hD p f hadm.1 hp5 hf F hFcard _ hβ3 hβinn hdiag
  · exact noL34Layer_of_not_mem_e6Inndiag hO hadm.1 hp2 hf hFcard hβ3 hdiag

end E6

section TwE6


@[expose] def Up34DiagTwE6 : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 5 ≤ ℓ → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
      ∀ x : MulAut (twistedE6RootGroup K σ), x ^ 3 = 1 → x ∉ twistedE6Inn K σ →
        x ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ → NoL34Layer x

theorem noL34Layer_fieldActor_twE6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (2 * d * 3)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ (d * 3)))
    {η : K ≃+* K} (hη : orderOf η = 3) :
    NoL34Layer (fieldActor (t := TwistTag.E6) σ η) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h2d3 : 1 ≤ 2 * d * 3 := by omega
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ h2d3 hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩
  obtain ⟨T, hTdef⟩ : ∃ T, fr ^ d = T := ⟨_, rfl⟩
  have hT : ∀ c, T c = c ^ ℓ ^ d := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hfr d c
  have hT6 : T ^ (2 * 3) = 1 := by
    rw [← hTdef, ← pow_mul, show d * (2 * 3) = orderOf fr by rw [hord]; ring,
      pow_orderOf_eq_one]
  obtain ⟨ε, hεdef⟩ : ∃ ε, T ^ (3 + 1) = ε := ⟨_, rfl⟩
  have hε : ∀ c, ε c = c ^ ℓ ^ (d * (3 + 1)) := fun c => by
    rw [← hεdef, ← hTdef, ← pow_mul]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hε3 : ε ^ 3 = 1 := by
    rw [← hεdef, ← pow_mul, show (3 + 1) * 3 = 2 * 3 * 2 by norm_num, pow_mul, hT6, one_pow]
  obtain ⟨κ, hκdef⟩ : ∃ κ, T ^ 2 = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d) := fun c => by
    rw [← hκdef, ← hTdef, ← pow_mul, mul_comm]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hkcard, hJC, hδord, hderived, hsimple, hnc, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd le_rfl
      (by decide) K hK κ hκ σ hσ (fixSubfieldRestrict T κ) hσ₀ ε hε
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hεne : ε ≠ 1 := fun h => by
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact absurd hδord (by norm_num)
  have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hεne
  have hz : Subgroup.zpowers ε = Subgroup.zpowers η := by
    refine le_antisymm (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hη hε3
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hεo
        (by rw [← hη]; exact pow_orderOf_eq_one _)
  have hzA : Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ ε) =
      Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ η) := by
    have h1 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) ε
    have h2 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) η
    rw [hz] at h1
    exact h1.symm.trans h2
  have hfix := fixSubgroup_eq_of_zpowers_eq hzA.symm
  set k := fixSubfield κ with hkdef
  set σ₀ := fixSubfieldRestrict T κ with hσ₀def
  set J := subfieldRootGroupImage TwistTag.E6 k σ₀ with hJ
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  have hΓ : fixSubgroup (fieldActor (t := TwistTag.E6) σ ε) =
      MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom (MonoidHom.id C) := rfl
  have hSD : J.subgroupOf C = ⁅fixSubgroup (fieldActor (t := TwistTag.E6) σ η),
      fixSubgroup (fieldActor (t := TwistTag.E6) σ η)⁆ := by
    rw [hfix, hΓ]
    exact hderived.symm
  have e1 : ↥(J.subgroupOf C) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  haveI : IsSimpleGroup ↥J := hsimple
  have hs : IsSimpleGroup ↥(J.subgroupOf C) := e1.isSimpleGroup
  have hnab : ∃ a b : ↥(J.subgroupOf C), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply hnc
    intro a b
    have h := hcon (e1.symm a) (e1.symm b)
    apply e1.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hcardk : Nat.card k = (ℓ ^ d) ^ 2 := by rw [hkcard, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c, σ₀ c = c ^ (ℓ ^ d) := fun c => Subtype.ext (by
    rw [hσ₀ c, SubmonoidClass.coe_pow])
  haveI : Finite k := Subtype.finite
  have eJ : ↥J ≃* twistedE6RootGroup k σ₀ :=
    (Subgroup.equivMapOfInjective (twistedE6RootGroup k σ₀) _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) k.subtype)).symm
  have hM : ChevalleyExceptionalModel ↥(J.subgroupOf C) .twistedE6 ℓ d :=
    chevalleyExceptionalModel_twistedE6_of_equiv hℓ hd hcardk σ₀ hσ₀' (e1.trans eJ)
  have hX : LieModel ↥(J.subgroupOf C) .twistedE6 0 ℓ d :=
    Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  have hSle : J.subgroupOf C ≤ fixSubgroup (fieldActor (t := TwistTag.E6) σ η) := by
    rw [hSD]
    exact Subgroup.commutator_le.2 fun a ha b hb =>
      (fixSubgroup (fieldActor (t := TwistTag.E6) σ η)).mul_mem
        ((fixSubgroup (fieldActor (t := TwistTag.E6) σ η)).mul_mem
          ((fixSubgroup (fieldActor (t := TwistTag.E6) σ η)).mul_mem ha hb)
          ((fixSubgroup (fieldActor (t := TwistTag.E6) σ η)).inv_mem ha))
        ((fixSubgroup (fieldActor (t := TwistTag.E6) σ η)).inv_mem hb)
  exact noL34_of_simple_normal_comm (fieldActor (t := TwistTag.E6) σ η) (J.subgroupOf C) hSle
    hSD.ge hs hnab (not_isLThreeFour_of_lieModel_odd hO hℓ2 hX)

theorem noL34Layer_of_not_mem_twistedE6Inndiag
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {x : MulAut (twistedE6RootGroup K σ)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : NoL34Layer x := by
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  obtain ⟨hηo, ⟨d, hd⟩, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf K hK'
    σ hσ Θ hΘ Nat.prime_three (by norm_num) hx3 hxo
  have hd0 : 1 ≤ d := by omega
  subst hd
  have hKdp : Nat.card K = ℓ ^ (2 * d * 3) := by rw [hK']; ring_nf
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * 3) := fun c => by rw [hσ]; ring_nf
  have h1 := noL34Layer_conj ψ⁻¹ (noL34Layer_fieldActor_twE6 hO hℓ hℓ2 hd0 hKdp σ hσdp hηo)
  have h2 : ψ⁻¹ * fieldActor (t := TwistTag.E6) σ (Θ x) * ψ⁻¹⁻¹ = x := by
    rw [← hψ]
    group
  rwa [h2] at h1

theorem noL34OuterAt_twE6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hD : Up34DiagTwE6) : NoL34OuterAt FamTwE6 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  have hf : 1 ≤ f := hadm.2.1
  have hE : ChevalleyExceptionalModel P .twistedE6 p f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv hadm.1 hf hE.2
  let θ : P ≃* twistedE6RootGroup K σ := e.symm
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ twistedE6Inn K σ := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  refine noL34Layer_congr θ ?_
  by_cases hdiag : MulAut.congr θ ψ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ
  · exact hD p f hadm.1 hp5 hf K hK σ hσ _ hβ3 hβinn hdiag
  · exact noL34Layer_of_not_mem_twistedE6Inndiag hO hadm.1 hp2 hf hK σ hσ hβ3 hdiag

end TwE6

end CFSG.HardMathSupport.Dickson.Sec6
