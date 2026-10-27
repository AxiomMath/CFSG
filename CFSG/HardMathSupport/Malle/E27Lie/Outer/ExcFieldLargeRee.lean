module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Arith27
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderLargeRee

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

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

open CFSG.HardMathSupport.Lang.Coordinator

section


theorem twentySeven_dvd_fixedSubgroup_largeRee {a : ℕ} (ha : 1 ≤ a) {F : Type} [Field F]
    [Finite F] [CharP F ReeTag.F4.prime] (hK : Nat.card F = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (α' : MulAut (F4.reeGamma F a)) (hα'p : α' ^ p = 1)
    (hα'inn : α' ∉ inner (F4.reeGamma F a)) : 27 ∣ Nat.card (fixedSubgroup α') := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL F4.tag F) := finite_modGL
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
  rw [hcard2, hcard3]
  have hord :=
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      b (fixSubfield β) hbcard).1
  have hq2 : 2 ≤ 2 ^ (2 * b + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hord, reeF4_order_eq_numerator _ hq2]
  refine twentySeven_dvd_numTwistedF4 _ ?_
  rw [Nat.pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num


end

end CFSG.HardMathSupport.Malle.E27Lie
