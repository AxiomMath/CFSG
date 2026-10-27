module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.ExcOuter
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerTransport
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ReeF4

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Lang.Coordinator CFSG.Sporadic.Schreier.Tits
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Dickson.Sec6.I923
open Up34Chev2

section Family


theorem Up34Chev2.noL34Layer_reeGammaFieldAut_F4 {a b : ℕ} (F : Type) [Field F] [Finite F]
    [CharP F ReeTag.F4.prime] (σ : F ≃+* F)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ (2 * b + 1))
    (hfix : ((ReeTag.F4.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.F4.reeGamma F a).subtype =
        (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype)) :
    NoL34Layer (ReeTag.F4.reeGammaFieldAut F a σ) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP ↥(fixSubfield σ) ReeTag.F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hk
  let C : Subgroup ↥(ReeTag.F4.reeGamma F a) :=
    (ReeTag.F4.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)
  have hCfix : fixSubgroup (ReeTag.F4.reeGammaFieldAut F a σ) = C :=
    Subgroup.ext fun _ => Iff.rfl
  let eC : ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut F a σ)) ≃*
      ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) :=
    (MulEquiv.subgroupCongr hCfix).trans
      (((C.equivMapOfInjective (ReeTag.F4.reeGamma F a).subtype
        (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hfix)).trans
        ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
          (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm)
  by_cases hb : b = 0
  · subst hb
    have hk2 : Nat.card ↥(fixSubfield σ) = 2 := by simpa using hk
    obtain ⟨c⟩ := nonempty_commutator_reeGamma_tits hk2
    obtain ⟨cc⟩ := nonempty_commutator_mulEquiv eC
    haveI : Nontrivial titsD := titsD_simple.toNontrivial
    refine noL34Layer_of_fixed_commutator_equiv _ (cc.trans c) titsD_simple
      (exists_noncomm_of_center_bot titsD_center) fun h => ?_
    have h1 := card_eq_of_isLThreeFour h
    rw [card_titsD] at h1
    exact absurd h1 (by norm_num)
  · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.2 hb
    have hrel : ReeTitsModel ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) .twistedF4 2 (2 * b + 1) :=
      ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨b, rfl⟩, by omega⟩, b, rfl,
        (reeTitsRelationModel_iff ReeTag.F4 _ (2 * b + 1) b).2
          ⟨fixSubfield σ, inferInstance, inferInstance, inferInstance, hk,
            ⟨(CFSG.RankThree.PartTwo.Census.Carrier.ReeF4.nonempty_derivedCentralQuotient_equiv
              hb1 hk).some.symm⟩⟩⟩
    obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_2f4_simplicity (h := hrel)
    have hZ : Subgroup.center ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊥ :=
      ReeTag.large_Ree_fixed_group_center_trivial b (fixSubfield σ) hk
    have hX : LieModel ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) .twistedF4 0 2 (2 * b + 1) :=
      Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hrel⟩))
    haveI : Nontrivial ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) := hsimp.toNontrivial
    exact noL34Layer_of_fixed_equiv _ eC hsimp (exists_noncomm_of_center_bot hZ) fun h =>
      not_isLThreeFour_of_lieModel_two hX (by decide) h

theorem Up34Chev2.noL34Layer_reeGamma_F4 {a : ℕ} (ha : 1 ≤ a) (F : Type) [Field F] [Finite F]
    [CharP F ReeTag.F4.prime] (hK : Nat.card F = 2 ^ (2 * a + 1))
    (β' : MulAut ↥(ReeTag.F4.reeGamma F a)) (hβ3 : β' ^ 3 = 1)
    (hβinn : β' ∉ inner ↥(ReeTag.F4.reeGamma F a)) : NoL34Layer β' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
      a ha F hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF β'
  have hΨα : Ψ ⟨x, β⟩ = β' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut ↥(ReeTag.F4.reeGamma F a) →* (F ≃+* F) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ β' = β := by
    show SemidirectProduct.rightHom (Ψ.symm β') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ 3 = 1 := by rw [← hΘα, ← map_pow, hβ3, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut F a 1 = 1 := by
    rw [← ReeTag.reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hβinn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = 3 := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK Nat.prime_three
    β hβord β' hβ3 ⟨x, hxβ⟩
  obtain ⟨b, hbp, hbcard, hfix⟩ :=
    largeRee_fixed_data_of_odd hK Nat.prime_three (by norm_num) β hβord
  refine noL34Layer_of_conj_pow (r := 1) (j := 1) (δ := (MulAut.conj g)⁻¹) (by simp) ?_
    (Up34Chev2.noL34Layer_reeGammaFieldAut_F4 F β hbcard hfix)
  rw [pow_one, hg]
  group

theorem up34C2Out_reeF4 : Up34Chev2Out FamReeF4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | reeF4 m =>
    exfalso
    have hm := blueprintLieModel_reeF4 m hv e
    have hR : ReeTitsModel S .twistedF4 2 (2 * m + 1) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
      · exact h
      · exact absurd ht' (by decide)
    have hm1 : 1 ≤ m := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
    obtain ⟨F, _, _, _, hFcard, ⟨e'⟩⟩ :
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F ReeTag.F4.prime),
          Nat.card F = 2 ^ (2 * m + 1) ∧ Nonempty (S ≃* ReeTag.F4.reeGamma F m) := by
      obtain ⟨-, -, -, -, -, -, hmain⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_model_field_outer_group_and_inner_involutions
          S 2 (2 * m + 1) hR
      obtain ⟨-, a, hfa, F, _, _, hFcard, he⟩ := hR
      have ha : a = m := by omega
      subst ha
      have : CharP F ReeTag.F4.prime := by
        have : Fintype F := Fintype.ofFinite F
        exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) (by
          rw [← Nat.card_eq_fintype_card, hFcard])
      obtain ⟨⟨e1⟩, -⟩ := hmain a F hfa hFcard he
      exact ⟨F, inferInstance, inferInstance, this, hFcard, ⟨e1⟩⟩
    haveI : Finite ↥(ReeTag.F4.reeGamma F m) := Finite.of_equiv S e'.toEquiv
    have hβ3 : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, ((up34Pumpup_iff α).1 hp).1, map_one]
    have hβinn : MulAut.congr e' α ∉ inner ↥(ReeTag.F4.reeGamma F m) := fun hin =>
      hα ((congr_mem_inner_iff_of_equiv e' α).mp hin)
    exact ((up34Pumpup_iff α).1 hp).2.2
      (noL34Layer_congr e' (Up34Chev2.noL34Layer_reeGamma_F4 hm1 F hFcard _ hβ3 hβinn))
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6
