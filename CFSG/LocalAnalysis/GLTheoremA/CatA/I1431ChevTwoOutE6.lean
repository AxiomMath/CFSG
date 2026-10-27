module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutEnt
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
public import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (commutator_le_innAutDerived
  mem_innAutDerived_congr)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6 (FamE6 FamTwE6)
open scoped commutatorElement

section Frobenius

theorem exists_twE6_frobenius_powers {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * d * 3)) :
    Finite (K ≃+* K) ∧ IsCyclic (K ≃+* K) ∧ ∃ T κ ε : K ≃+* K, (∀ c, T c = c ^ 2 ^ d) ∧
      (∀ c, κ c = c ^ 2 ^ (2 * d)) ∧ (∀ c, ε c = c ^ 2 ^ (d * (3 + 1))) ∧ ε ^ 3 = 1 := by
  have h2d3 : 1 ≤ 2 * d * 3 := by omega
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two h2d3 hK
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega),
    isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩, fr ^ d, fr ^ (2 * d), fr ^ (d * (3 + 1)),
    fun c => ringAut_pow_apply_of_frobenius hfr d c,
    fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c,
    fun c => ringAut_pow_apply_of_frobenius hfr (d * (3 + 1)) c, ?_⟩
  rw [← pow_mul, show d * (3 + 1) * 3 = 2 * d * 3 * 2 by ring, pow_mul, ← hord,
    pow_orderOf_eq_one, one_pow]

end Frobenius

section Entrywise


theorem fixSubgroup_fieldActor_eq_of_pow_three {K : Type} [Field K] [Finite K]
    [IsCyclic (K ≃+* K)] (σ : K ≃+* K) {ε η : K ≃+* K} (hε3 : ε ^ 3 = 1) (hεne : ε ≠ 1)
    (hη : orderOf η = 3) :
    fixSubgroup (fieldActor (t := TwistTag.E6) σ η) =
      fixSubgroup (fieldActor (t := TwistTag.E6) σ ε) := by
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun f : K ≃+* K => (f : K → K)) DFunLike.coe_injective
  have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hεne
  have hz : Subgroup.zpowers ε = Subgroup.zpowers η := by
    refine le_antisymm (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hη hε3
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hεo
        (by rw [← hη]; exact pow_orderOf_eq_one _)
  have h1 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) ε
  have h2 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) η
  rw [hz] at h1
  exact fixSubgroup_eq_of_zpowers_eq (h1.symm.trans h2).symm

end Entrywise

section Field


theorem u42Layer_entrywise_e6 {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hcard : Nat.card (fixSubfield σ) = 2 ^ d) :
    U42Layer (entrywiseAdjointAut Tag.E6 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e6_simplicity _ 2 d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hX : Blueprint.LieModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 0 2 d :=
    Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  exact u42Layer_entrywise σ hsimp (exists_noncomm_of_center_bot hZ) fun hT =>
    absurd (eq_of_catalogIs_u4two_lieModel hT hX).1 (by decide)

theorem u42Layer_of_not_mem_e6Inndiag {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {x : MulAut (adjointGroup Tag.E6 K)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ e6Inndiag K) : U42Layer x False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨σ, hσo, hpf, δ, hδ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag Nat.prime_two hf K hK
    Nat.prime_three (by norm_num) hx3 hxo
  have hd : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
  have hcard : Nat.card (fixSubfield σ) = 2 ^ (f / 3) := by
    have := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two hf hK σ).2
    rwa [hσo] at this
  have h1 : U42Layer (δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹) False :=
    u42Layer_conj δ⁻¹ (u42Layer_entrywise_e6 hd σ hcard)
  have h2 : δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹ = x := by
    rw [← hδ]
    group
  rwa [h2] at h1

theorem u42Layer_fieldActor_twE6 {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * d * 3)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ (d * 3)))
    {η : K ≃+* K} (hη : orderOf η = 3) :
    U42Layer (fieldActor (t := TwistTag.E6) σ η) False := by
  classical
  obtain ⟨hfin, hcyc, T, κ, ε, hT, hκ, hε, hε3⟩ := exists_twE6_frobenius_powers hd hK
  haveI := hfin
  haveI := hcyc
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ 2 ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hkcard, hJC, hδord, hderived, hsimple, hnc, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer Nat.prime_two hd
      le_rfl (by decide) K hK κ hκ σ hσ (fixSubfieldRestrict T κ) hσ₀ ε hε
  have hεne : ε ≠ 1 := fun h => by
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact absurd hδord (by norm_num)
  have hfix := fixSubgroup_fieldActor_eq_of_pow_three σ hε3 hεne hη
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
  have hcardk : Nat.card k = (2 ^ d) ^ 2 := by rw [hkcard, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c, σ₀ c = c ^ (2 ^ d) := fun c => Subtype.ext (by
    rw [hσ₀ c, SubmonoidClass.coe_pow])
  haveI : Finite k := Subtype.finite
  have eJ : ↥J ≃* twistedE6RootGroup k σ₀ :=
    (Subgroup.equivMapOfInjective (twistedE6RootGroup k σ₀) _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) k.subtype)).symm
  have hM : ChevalleyExceptionalModel ↥(J.subgroupOf C) .twistedE6 2 d :=
    chevalleyExceptionalModel_twistedE6_of_equiv Nat.prime_two hd hcardk σ₀ hσ₀' (e1.trans eJ)
  have hX : LieModel ↥(J.subgroupOf C) .twistedE6 0 2 d :=
    Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  exact u42Layer_of_simple_commutator (fieldActor (t := TwistTag.E6) σ η) (J.subgroupOf C) hSD
    hs hnab fun hT => absurd (eq_of_catalogIs_u4two_lieModel hT hX).1 (by decide)

theorem u42Layer_of_not_mem_twistedE6Inndiag {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {x : MulAut (twistedE6RootGroup K σ)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : U42Layer x False := by
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨hηo, ⟨d, hd⟩, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag Nat.prime_two
    hf K hK' σ hσ Θ hΘ Nat.prime_three (by norm_num) hx3 hxo
  have hd0 : 1 ≤ d := by omega
  subst hd
  have hKdp : Nat.card K = 2 ^ (2 * d * 3) := by rw [hK']; ring_nf
  have hσdp : ∀ c, σ c = c ^ 2 ^ (d * 3) := fun c => by rw [hσ]; ring_nf
  have h1 := u42Layer_conj ψ⁻¹ (u42Layer_fieldActor_twE6 hd0 hKdp σ hσdp hηo)
  have h2 : ψ⁻¹ * fieldActor (t := TwistTag.E6) σ (Θ x) * ψ⁻¹⁻¹ = x := by
    rw [← hψ]
    group
  rwa [h2] at h1

end Field

section Family


theorem u42Out_e6 : U42OuterAt FamE6 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E6 q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hm := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E6 q hv e
    have hU : UntwistedChevalleyModel S .E6 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
    rw [hq2] at hFcard
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    by_cases hdiag : MulAut.congr θ α ∈ e6Inndiag F
    · exact hα ((mem_innAutDerived_congr θ).mp
        (commutator_le_innAutDerived _ (e6Inndiag_le_commutator F hdiag)))
    · exact hp.apply (u42Layer_congr θ
        (u42Layer_of_not_mem_e6Inndiag q.exponent_pos hFcard hβ3 hdiag))
  | _ => exact hF.elim

theorem u42Out_twE6 : U42OuterAt FamTwE6 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | twistedE6 q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hm := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_twistedE6 q hv e
    have hT : TwistedChevalleyModel S TwistTag.E6 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨K, _, _, σ, hK, hσ, ⟨eK⟩⟩ := exists_twistedE6RootGroup_equiv q.prime_p q.exponent_pos hT
    rw [hq2] at hK hσ
    let θ : S ≃* twistedE6RootGroup K σ := eK.symm
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    by_cases hdiag : MulAut.congr θ α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ
    · have hC := commutator_twistedE6RootGroup_eq_top Nat.prime_two q.exponent_pos hK σ hσ
      exact hα ((mem_innAutDerived_congr θ).mp
        (commutator_le_innAutDerived _ (twistedE6Inndiag_le_commutator σ hK hσ hC hdiag)))
    · exact hp.apply (u42Layer_congr θ
        (u42Layer_of_not_mem_twistedE6Inndiag q.exponent_pos hK σ hσ hβ3 hdiag))
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
