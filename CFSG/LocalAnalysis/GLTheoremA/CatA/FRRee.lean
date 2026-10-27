module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderLargeRee

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.HardMathSupport.Lang.Coordinator CFSG.Assembly
open scoped commutatorElement


theorem subBody_ree {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I F : Set (MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)))) (hF : InnFree p F) :
    ∀ f ∈ F, orderOf f = p → p ∣ 2 * a + 1 ∧
      ∃ D : Subgroup (LargeEvenCenterQuot (LargeEvenTwF4H a K)), SubfieldGrp f D ∧
        (LargeEvenRecipeTwF4Inherited (((2 * a + 1) / p - 1) / 2)
            (fun R' _ _ _ => Nonempty (↥D ≃* R')) ∨ 2 * a + 1 = p) := by
  intro f hf hord
  have hR : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H a K)) .twistedF4 2 (2 * a + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl,
      CFSG.StandardType.reeTitsRelationModel_largeEven a hK⟩
  obtain ⟨-, -, -, -, -, -, hmain⟩ := large_Ree_model_field_outer_group_and_inner_involutions _ 2
    (2 * a + 1) hR
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨⟨e⟩, -⟩ := hmain a K rfl hK (CFSG.StandardType.centerQuot_twF4H_equiv K a)
  have : Fact p.Prime := ⟨hp⟩
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  set α' : MulAut (F4.reeGamma K a) := MulAut.congr e f with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hfp, map_one]
  have hα'inn : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (F4.reeGamma K a) :=
    fun h => hF f hf hord (((congr_mem_inner_iff e f).mp h))
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α'
    hα'p ⟨x, hxβ⟩
  obtain ⟨b, hbp, hbcard, hfix⟩ := largeRee_fixed_data_of_odd hK hp hp2 β hβord
  have hpn : p ∣ 2 * a + 1 := ⟨2 * b + 1, by rw [← hbp, mul_comm]⟩
  have hdiv : (2 * a + 1) / p = 2 * b + 1 := by
    rw [← hbp, Nat.mul_div_cancel _ hp.pos]
  refine ⟨hpn, FP.fixSub f, ⟨le_rfl, Subgroup.commutator_le_of_le le_rfl le_rfl, ?_⟩, ?_⟩
  · rw [Subgroup.relIndex_self]; exact odd_one
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · right
    rw [hb0] at hbp
    omega
  left
  rw [hdiv]
  have e₂ : ↥(FP.fixSub α') ≃* ↥(FP.fixSub (F4.reeGammaFieldAut K a β)) :=
    (MulEquiv.subgroupCongr (congrArg FP.fixSub hg)).trans
      (fixSubEquivConj (MulAut.conj g) (F4.reeGammaFieldAut K a β)).symm
  have e₃ : ↥(FP.fixSub (F4.reeGammaFieldAut K a β)) ≃* ↥(F4.reeGamma (fixSubfield β) b) :=
    ((((F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _)).equivMapOfInjective
      (F4.reeGamma K a).subtype (F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr hfix)).trans
      ((F4.reeGamma (fixSubfield β) b).equivMapOfInjective _
        (baseChangeGL_injective (τ := F4.tag) (fixSubfield β).subtype)).symm
  have : Finite (fixSubfield β) := Subtype.finite
  haveI : Fintype (fixSubfield β) := Fintype.ofFinite _
  haveI : CharP (fixSubfield β) F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := 2 * b + 1) (by
    rw [← Nat.card_eq_fintype_card, hbcard])
  have hR' : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H b (fixSubfield β))) .twistedF4 2
      (2 * b + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨b, rfl⟩, by omega⟩, b, rfl,
      CFSG.StandardType.reeTitsRelationModel_largeEven b hbcard⟩
  obtain ⟨-, -, -, -, -, -, hmain'⟩ := large_Ree_model_field_outer_group_and_inner_involutions _ 2
    (2 * b + 1) hR'
  obtain ⟨⟨e'⟩, -⟩ := hmain' b (fixSubfield β) rfl hbcard
    (CFSG.StandardType.centerQuot_twF4H_equiv (fixSubfield β) b)
  refine ⟨fixSubfield β, inferInstance, inferInstance, ?_, ?_⟩
  · rw [show (2 * b + 1 - 1) / 2 = b by omega]; exact hbcard
  · rw [show (2 * b + 1 - 1) / 2 = b by omega]
    exact ⟨(((fixSubEquivCongr e f).trans e₂).trans e₃).trans e'.symm⟩

end FR

end CFSG.LocalAnalysis.GLTheoremA
