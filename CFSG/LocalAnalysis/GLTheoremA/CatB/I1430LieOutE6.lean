module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutE6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutCharTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutEnt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (commutator_le_innAutDerived
  mem_innAutDerived_congr)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6 (FamE6 FamTwE6)
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (exists_twE6_frobenius_powers
  fixSubgroup_fieldActor_eq_of_pow_three)
open scoped commutatorElement

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}


section Field

theorem typeLayer_entrywise_e6W (hD : LieSOutTypeW T tm tf tN) {d : ℕ} (hd : 1 ≤ d) {K : Type}
    [Field K] [Finite K]
    (σ : K ≃+* K) (hcard : Nat.card (fixSubfield σ) = 2 ^ d) :
    TypeLayer T (entrywiseAdjointAut Tag.E6 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e6_simplicity _ 2 d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hX : Blueprint.LieModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 0 2 d :=
    Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  exact typeLayer_entrywise σ hsimp (exists_noncomm_of_center_bot hZ) fun hT =>
    absurd (hD.det hT hX).1 (by decide)

theorem typeLayer_of_not_mem_e6InndiagW (hD : LieSOutTypeW T tm tf tN) {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {x : MulAut (adjointGroup Tag.E6 K)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ e6Inndiag K) : TypeLayer T x False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨σ, hσo, hpf, δ, hδ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag Nat.prime_two hf K hK
    Nat.prime_three (by norm_num) hx3 hxo
  have hd : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
  have hcard : Nat.card (fixSubfield σ) = 2 ^ (f / 3) := by
    have := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two hf hK σ).2
    rwa [hσo] at this
  have h1 : TypeLayer T (δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹) False :=
    typeLayer_conj δ⁻¹ (typeLayer_entrywise_e6W hD hd σ hcard)
  have h2 : δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹ = x := by
    rw [← hδ]
    group
  rwa [h2] at h1

theorem typeLayer_fieldActor_twE6W (hD : LieSOutTypeW T tm tf tN) {d : ℕ} (hd : 1 ≤ d)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * d * 3)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ (d * 3)))
    {η : K ≃+* K} (hη : orderOf η = 3) :
    TypeLayer T (fieldActor (t := TwistTag.E6) σ η) False := by
  classical
  obtain ⟨hfin, hcyc, Tf, κ, ε, hT, hκ, hε, hε3⟩ := exists_twE6_frobenius_powers hd hK
  haveI := hfin
  haveI := hcyc
  have hσ₀ : ∀ c, (fixSubfieldRestrict Tf κ c : K) = (c : K) ^ 2 ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hkcard, hJC, hδord, hderived, hsimple, hnc, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer Nat.prime_two hd
      le_rfl (by decide) K hK κ hκ σ hσ (fixSubfieldRestrict Tf κ) hσ₀ ε hε
  have hεne : ε ≠ 1 := fun h => by
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact absurd hδord (by norm_num)
  have hfix := fixSubgroup_fieldActor_eq_of_pow_three σ hε3 hεne hη
  set k := fixSubfield κ with hkdef
  set σ₀ := fixSubfieldRestrict Tf κ with hσ₀def
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
  exact typeLayer_of_simple_commutator (fieldActor (t := TwistTag.E6) σ η) (J.subgroupOf C) hSD
    hs hnab fun hT => absurd (hD.det hT hX).1 (by decide)

theorem typeLayer_of_not_mem_twistedE6InndiagW (hD : LieSOutTypeW T tm tf tN) {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {x : MulAut (twistedE6RootGroup K σ)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : TypeLayer T x False := by
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨hηo, ⟨d, hd⟩, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag Nat.prime_two
    hf K hK' σ hσ Θ hΘ Nat.prime_three (by norm_num) hx3 hxo
  have hd0 : 1 ≤ d := by omega
  subst hd
  have hKdp : Nat.card K = 2 ^ (2 * d * 3) := by rw [hK']; ring_nf
  have hσdp : ∀ c, σ c = c ^ 2 ^ (d * 3) := fun c => by rw [hσ]; ring_nf
  have h1 := typeLayer_conj ψ⁻¹ (typeLayer_fieldActor_twE6W hD hd0 hKdp σ hσdp hηo)
  have h2 : ψ⁻¹ * fieldActor (t := TwistTag.E6) σ (Θ x) * ψ⁻¹⁻¹ = x := by
    rw [← hψ]
    group
  rwa [h2] at h1

end Field

section Family

theorem lieSOut_e6W (hD : LieSOutTypeW T tm tf tN) : TypeOuterAt T Pc FamE6 := by
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
    · exact hp.apply (typeLayer_congr θ
        (typeLayer_of_not_mem_e6InndiagW hD q.exponent_pos hFcard hβ3 hdiag))
  | _ => exact hF.elim

theorem lieSOut_twE6W (hD : LieSOutTypeW T tm tf tN) : TypeOuterAt T Pc FamTwE6 := by
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
    · exact hp.apply (typeLayer_congr θ
        (typeLayer_of_not_mem_twistedE6InndiagW hD q.exponent_pos hK σ hσ hβ3 hdiag))
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
