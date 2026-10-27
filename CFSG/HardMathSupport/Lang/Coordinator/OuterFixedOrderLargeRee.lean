module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.RankThree.PartOne.RF4.Descent

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.RankThree.Chevalley.SteinbergBT (card_fixSubfield)


theorem reeF4_order_eq_numerator (q : ℕ) (hq : 2 ≤ q) :
    q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) =
      lieOrderNumerator .twistedF4 0 q := by
  have h1 : q ≤ q ^ 2 := by nlinarith
  have h2 : q ^ 2 ≤ q ^ 4 := by nlinarith
  have h3 : 1 ≤ q ^ 4 := by nlinarith
  have h4 : 1 ≤ q := by omega
  simp only [lieOrderNumerator]
  zify [h1, h2, h3, h4]
  ring


theorem largeRee_fixed_data_of_odd {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧ Nat.card (fixSubfield σ) = 2 ^ (2 * b + 1) ∧
      ((ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.F4.reeGamma K a).subtype =
        (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype) :=
  CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ

theorem outerFixedOrderBoundAt_twistedF4 : OuterFixedOrderBoundAt .twistedF4 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 _ _ α hαp hαin
  left
  obtain ⟨hn0, hℓ, hfodd, hf3⟩ := hadm.2.2
  subst hn0
  subst hℓ
  have hR : ReeTitsModel K .twistedF4 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
  obtain ⟨a, F, _, _, _, hfa, hFcard, ⟨e⟩⟩ :
      ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F F4.prime),
        f = 2 * a + 1 ∧ Nat.card F = 2 ^ f ∧ Nonempty (K ≃* F4.reeGamma F a) := by
    obtain ⟨-, -, -, -, -, -, hmain⟩ :=
      large_Ree_model_field_outer_group_and_inner_involutions K 2 f hR
    obtain ⟨-, a, hfa, F, _, _, hFcard, he⟩ := hR
    have : CharP F F4.prime := by
      have : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [← Nat.card_eq_fintype_card, hFcard])
    obtain ⟨⟨e⟩, -⟩ := hmain a F hfa hFcard he
    exact ⟨a, F, inferInstance, inferInstance, this, hfa, hFcard, ⟨e⟩⟩
  have ha : 1 ≤ a := by omega
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hFcard
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (F4.reeGamma F a) := Finite.of_equiv K e.toEquiv
  set α' : MulAut (F4.reeGamma F a) := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hαp, map_one]
  have hα'inn : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (F4.reeGamma F a) := fun h => hαin ((congr_mem_inner_iff e α).mp h)
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha F hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (F4.reeGamma F a) →* (F ≃+* F) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : F4.reeGammaFieldAut F a 1 = 1 := by rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α'
    hα'p ⟨x, hxβ⟩
  obtain ⟨b, hbp, hbcard, hfix⟩ := largeRee_fixed_data_of_odd hK hp hp2 β hβord
  have : Finite (fixSubfield β) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP (fixSubfield β) F4.prime := by
    have : Fintype (fixSubfield β) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hbcard])
  have hcard1 : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup α') :=
    (card_fixedSubgroup_congr e α).symm
  have hcard2 : Nat.card (fixedSubgroup α') =
      Nat.card (fixedSubgroup (F4.reeGammaFieldAut F a β)) :=
    (card_fixedSubgroup_eq_of_intertwine (MulAut.conj g : _ ≃* _) _ α' fun y => by
      rw [hg]
      simp [MulAut.mul_apply]
      group).symm
  have hFix : fixedSubgroup (F4.reeGammaFieldAut F a β) =
      (F4.reeGammaFieldAut F a β).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  have hcard3 : Nat.card (fixedSubgroup (F4.reeGammaFieldAut F a β)) =
      Nat.card (F4.reeGamma (fixSubfield β) b) := by
    rw [hFix]
    refine (Nat.card_congr (((F4.reeGammaFieldAut F a β).toMonoidHom.eqLocus
        (MonoidHom.id _)).equivMapOfInjective (F4.reeGamma F a).subtype
        (F4.reeGamma F a).subtype_injective |>.trans
        (MulEquiv.subgroupCongr hfix)).toEquiv).trans ?_
    exact Nat.card_congr ((F4.reeGamma (fixSubfield β) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := F4.tag) (fixSubfield β).subtype)).symm.toEquiv
  refine ⟨2 * b + 1, by rw [mul_comm, hbp, hfa], ?_⟩
  rw [hcard1, hcard2, hcard3]
  have hord := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    b (fixSubfield β) hbcard).1
  have hq2 : 2 ≤ 2 ^ (2 * b + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hord, reeF4_order_eq_numerator _ hq2]

end CFSG.HardMathSupport.Lang.Coordinator
