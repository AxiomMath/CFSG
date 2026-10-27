module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderLargeRee
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Local
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Lang.Coordinator CFSG.Sporadic.Schreier.Tits

section


theorem not_typeL2_titsD {r : ℕ} (hr : 10 ≤ r) : ¬ IsTypeL2 r titsD := by
  intro hT
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card titsD hT
  have hc : Nat.card (titsD ⧸ Subgroup.center titsD) = 17971200 := by
    rw [titsD_center, ← card_titsD]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := titsD)).toEquiv
  have hr400 : ∀ m : ℕ, m ≤ 2 * 17971200 → m + r = r ^ 3 → r < 400 := by
    intro m hm h
    by_contra hcon
    have h400 : 400 ≤ r := by omega
    have h1 : 400 * 400 * r ≤ r * r * r := Nat.mul_le_mul (Nat.mul_le_mul h400 h400) le_rfl
    have h2 : r ^ 3 = r * r * r := by ring
    rw [h2] at h
    generalize r * r * r = u at h1 h
    omega
  rcases Nat.even_or_odd r with he | ho
  · have h := (heven he).1
    rw [hc] at h
    have := hr400 17971200 (by omega) h
    interval_cases r <;> omega
  · have h := hodd ho
    rw [hc] at h
    have := hr400 (2 * 17971200) le_rfl h
    interval_cases r <;> omega

theorem nonempty_commutator_reeGamma_tits {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) :
    Nonempty (↥(commutator ↥(ReeTag.F4.reeGamma k 0)) ≃* titsD) := by
  haveI : Fact (Nat.card k = 2) := ⟨hk⟩
  let g : ↥(ReeTag.F4.reeGamma k 0) ≃* ↥(reeFixed ReeTag.F4 k 0) :=
    (MulEquiv.subgroupCongr ((ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.F4) (K := k)
      (a := 0)).trans (reeFixedGroup_eq_map_reeFixed ReeTag.F4 k 0))).trans
      ((reeFixed ReeTag.F4 k 0).equivMapOfInjective (adjointGroup ReeTag.F4.tag k).subtype
        (adjointGroup ReeTag.F4.tag k).subtype_injective).symm
  obtain ⟨c⟩ := nonempty_commutator_mulEquiv g
  exact ⟨c.trans titsDerivedIso⟩

theorem noL2Layer_reeGammaFieldAut_F4 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {a b : ℕ} (F : Type) [Field F] [Finite F] [CharP F ReeTag.F4.prime] (σ : F ≃+* F)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ (2 * b + 1))
    (hfix : ((ReeTag.F4.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.F4.reeGamma F a).subtype =
        (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype)) :
    NoL2Layer (ReeTag.F4.reeGammaFieldAut F a σ) := by
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
    exact noL2Layer_of_fixed_commutator_equiv _ (cc.trans c) titsD_simple
      (exists_noncomm_of_center_bot titsD_center) fun r hr => not_typeL2_titsD hr
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
    exact noL2Layer_of_fixed_equiv _ eC hsimp (exists_noncomm_of_center_bot hZ) fun r hr =>
      not_typeL2_of_lieModel hO hX.admissible hX (by decide) (by decide) hZ hr

theorem noL2Layer_reeGamma_F4 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {a : ℕ} (ha : 1 ≤ a) (F : Type) [Field F] [Finite F] [CharP F ReeTag.F4.prime]
    (hK : Nat.card F = 2 ^ (2 * a + 1)) (β' : MulAut ↥(ReeTag.F4.reeGamma F a))
    (hβ3 : β' ^ 3 = 1) (hβinn : β' ∉ inner ↥(ReeTag.F4.reeGamma F a)) : NoL2Layer β' := by
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
  refine noL2Layer_of_conj_pow (r := 1) (j := 1) (δ := (MulAut.conj g)⁻¹) (by simp) ?_
    (noL2Layer_reeGammaFieldAut_F4 hO F β hbcard hfix)
  rw [pow_one, hg]
  group

theorem noL2OuterAt_reef4 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL2OuterAt FamReeF4 := by
  intro P _ _ t n p f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  obtain ⟨hn0, hℓ, hfodd, hf3⟩ := hadm.2.2
  subst hn0
  subst hℓ
  have hR : ReeTitsModel P .twistedF4 2 f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
  obtain ⟨a, F, _, _, _, hfa, hFcard, ⟨e⟩⟩ :
      ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F ReeTag.F4.prime),
        f = 2 * a + 1 ∧ Nat.card F = 2 ^ f ∧ Nonempty (P ≃* ReeTag.F4.reeGamma F a) := by
    obtain ⟨-, -, -, -, -, -, hmain⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_model_field_outer_group_and_inner_involutions
        P 2 f hR
    obtain ⟨-, a, hfa, F, _, _, hFcard, he⟩ := hR
    have : CharP F ReeTag.F4.prime := by
      have : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [← Nat.card_eq_fintype_card, hFcard])
    obtain ⟨⟨e⟩, -⟩ := hmain a F hfa hFcard he
    exact ⟨a, F, inferInstance, inferInstance, this, hfa, hFcard, ⟨e⟩⟩
  have ha : 1 ≤ a := by omega
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hFcard
  haveI : Finite ↥(ReeTag.F4.reeGamma F a) := Finite.of_equiv P e.toEquiv
  have hβ3 : MulAut.congr e ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr e ψ ∉ inner ↥(ReeTag.F4.reeGamma F a) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv e ψ).mp hin)
  exact noL2Layer_congr e (noL2Layer_reeGamma_F4 hO ha F hK _ hβ3 hβinn)

theorem y923_reef4_holds : Y923_ReeF4 :=
  y923_lieRestAt_of_noL2Outer
    (noL2OuterAt_reef4 CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end

end CFSG.HardMathSupport.Dickson.Sec6.I923
