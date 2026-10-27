module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.ExcOuter
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerMore
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Dickson.Sec6.I923
open Up34Chev2

section Residual


@[expose] def Up34C2OutDiag_TwE6 : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
    (∀ c, σ c = c ^ (2 ^ f)) →
    ∀ ψ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ, ψ ∉ twistedE6Inn K σ →
      ¬ Up34Pumpup (twistedE6RootGroup K σ) ψ

end Residual

namespace Up34Chev2

section Field


theorem noL34Layer_fieldActor_twE6 {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * d * 3)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ (d * 3)))
    {η : K ≃+* K} (hη : orderOf η = 3) :
    NoL34Layer (fieldActor (t := TwistTag.E6) σ η) := by
  classical
  have hℓ : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have h2d3 : 1 ≤ 2 * d * 3 := by omega
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ h2d3 hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩
  obtain ⟨T, hTdef⟩ : ∃ T, fr ^ d = T := ⟨_, rfl⟩
  have hT : ∀ c, T c = c ^ 2 ^ d := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hfr d c
  have hT6 : T ^ (2 * 3) = 1 := by
    rw [← hTdef, ← pow_mul, show d * (2 * 3) = orderOf fr by rw [hord]; ring,
      pow_orderOf_eq_one]
  obtain ⟨ε, hεdef⟩ : ∃ ε, T ^ (3 + 1) = ε := ⟨_, rfl⟩
  have hε : ∀ c, ε c = c ^ 2 ^ (d * (3 + 1)) := fun c => by
    rw [← hεdef, ← hTdef, ← pow_mul]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hε3 : ε ^ 3 = 1 := by
    rw [← hεdef, ← pow_mul, show (3 + 1) * 3 = 2 * 3 * 2 by norm_num, pow_mul, hT6, one_pow]
  obtain ⟨κ, hκdef⟩ : ∃ κ, T ^ 2 = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ 2 ^ (2 * d) := fun c => by
    rw [← hκdef, ← hTdef, ← pow_mul, mul_comm]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ 2 ^ d := fun c => by
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
  have hcardk : Nat.card k = (2 ^ d) ^ 2 := by rw [hkcard, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c, σ₀ c = c ^ (2 ^ d) := fun c => Subtype.ext (by
    rw [hσ₀ c, SubmonoidClass.coe_pow])
  haveI : Finite k := Subtype.finite
  have eJ : ↥J ≃* twistedE6RootGroup k σ₀ :=
    (Subgroup.equivMapOfInjective (twistedE6RootGroup k σ₀) _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) k.subtype)).symm
  have hM : ChevalleyExceptionalModel ↥(J.subgroupOf C) .twistedE6 2 d :=
    chevalleyExceptionalModel_twistedE6_of_equiv hℓ hd hcardk σ₀ hσ₀' (e1.trans eJ)
  have hX : LieModel ↥(J.subgroupOf C) .twistedE6 0 2 d :=
    Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  exact noL34Layer_of_simple_commutator (fieldActor (t := TwistTag.E6) σ η) (J.subgroupOf C) hSD
    hs hnab fun hT => not_isLThreeFour_of_lieModel_two hX (by decide) hT

theorem noL34Layer_of_not_mem_twistedE6Inndiag {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {x : MulAut (twistedE6RootGroup K σ)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : NoL34Layer x := by
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨hηo, ⟨d, hd⟩, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag Nat.prime_two
    hf K hK' σ hσ Θ hΘ Nat.prime_three (by norm_num) hx3 hxo
  have hd0 : 1 ≤ d := by omega
  subst hd
  have hKdp : Nat.card K = 2 ^ (2 * d * 3) := by rw [hK']; ring_nf
  have hσdp : ∀ c, σ c = c ^ 2 ^ (d * 3) := fun c => by rw [hσ]; ring_nf
  have h1 := noL34Layer_conj ψ⁻¹ (noL34Layer_fieldActor_twE6 hd0 hKdp σ hσdp hηo)
  have h2 : ψ⁻¹ * fieldActor (t := TwistTag.E6) σ (Θ x) * ψ⁻¹⁻¹ = x := by
    rw [← hψ]
    group
  rwa [h2] at h1

end Field

end Up34Chev2

section Family


theorem up34C2Out_twE6_of_diag (hD : Up34C2OutDiag_TwE6) : Up34Chev2Out FamTwE6 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | twistedE6 q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_twistedE6 q hv e
    have hT : TwistedChevalleyModel S TwistTag.E6 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨K, _, _, σ, hK, hσ, ⟨eK⟩⟩ := exists_twistedE6RootGroup_equiv q.prime_p q.exponent_pos hT
    rw [hq2] at hK hσ
    let θ : S ≃* twistedE6RootGroup K σ := eK.symm
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, ((up34Pumpup_iff α).1 hp).1, map_one]
    have hβinn : MulAut.congr θ α ∉ twistedE6Inn K σ :=
      fun hin => hα ((congr_mem_inner_iff_of_equiv θ α).mp hin)
    by_cases hdiag : MulAut.congr θ α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ
    · exact hD q.exponent K σ q.exponent_pos hK hσ _ hdiag hβinn (hp.of_congr θ)
    · have h1 := noL34Layer_of_not_mem_twistedE6Inndiag q.exponent_pos hK σ hσ hβ3 hdiag
      exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr θ h1)
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6
