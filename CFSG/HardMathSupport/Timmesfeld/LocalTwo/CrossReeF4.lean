module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Core
public import CFSG.RankThree.PartOne.SEITZ2.Common
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderLargeRee
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

section ReeF4


theorem isLocallyBalancedAbs_two_reeGamma_F4_of_inner {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hin : InnerPlaneBalance p (ReeTag.F4.reeGamma K a)) :
    IsLocallyBalancedAbs p 2 (ReeTag.F4.reeGamma K a) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ReeTag.F4.reeGamma K a) := inferInstance
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, hcyc, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj hin ?_
  intro D hD hDc hDin
  have hDe := CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian hD
  obtain ⟨g, hg1, hgD⟩ := CFSG.RankThree.PartOne.SEITZ2.exists_conj_mem_of_plane_of_cyclic_outer
    hp hcyc D hDc
  obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
  have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘ : ∀ (y : ReeTag.F4.reeGamma K a) (β : K ≃+* K),
      Θ (MulAut.conj y * ReeTag.F4.reeGammaFieldAut K a β) = β := fun y β => by
    rw [← hΨ y β]
    change SemidirectProduct.rightHom (Ψ.symm (Ψ ⟨y, β⟩)) = β
    rw [MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨⟨x₀, β⟩, hxβ, -⟩ := hNF x
  have hΘx : Θ x = β := by rw [hxβ]; exact hΘ x₀ β
  have hβp : β ^ p = 1 := by rw [← hΘx, ← map_pow, hxp, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := map_one (ReeTag.F4.reeGammaFieldAutHom K a)
  have hβ1 : β ≠ 1 := by
    intro h
    apply hxin
    refine ⟨x₀, ?_⟩
    rw [hxβ]
    change MulAut.conj x₀ = MulAut.conj x₀ * ReeTag.F4.reeGammaFieldAut K a β
    rw [h, hone, mul_one]
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hinjφ : Function.Injective (ReeTag.F4.reeGammaFieldAutHom K a) := fun s t h => by
    have h1 := hΘ 1 s
    have h2 := hΘ 1 t
    rw [map_one, one_mul] at h1 h2
    exact h1.symm.trans ((congrArg Θ h).trans h2)
  have hδp : orderOf (ReeTag.F4.reeGammaFieldAut K a β) = p := by
    have := orderOf_injective _ hinjφ β
    rwa [hβord] at this
  obtain ⟨g₀, hg₀⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp β hβord x hxp
    ⟨x₀, hxβ⟩
  have hxh : x = MulAut.conj g₀ * ReeTag.F4.reeGammaFieldAut K a β * (MulAut.conj g₀)⁻¹ := hg₀
  have hy1 : (MulAut.conj g : MulAut (ReeTag.F4.reeGamma K a)) ≠ 1 := fun h1 =>
    hg1 (hinj (by rw [h1, map_one]))
  have hyp : (MulAut.conj g : MulAut (ReeTag.F4.reeGamma K a)) ^ p = 1 := hD.2 _ hgD
  have hcomm : (MulAut.conj g : MulAut (ReeTag.F4.reeGamma K a)) * x = x * MulAut.conj g :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hgD⟩ ⟨x, hxD⟩)
  obtain ⟨k₀, hk₀δ, hk₀ord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh ⟨g, rfl⟩ hy1
    hyp hcomm
  have hJdvd : p ∣ Nat.card ((ReeTag.F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus
      (MonoidHom.id _)) := by
    have hk₀J : k₀ ∈ (ReeTag.F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _) :=
      hk₀δ
    have : orderOf (⟨k₀, hk₀J⟩ : ↥((ReeTag.F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus
        (MonoidHom.id _))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hk₀ord
    rw [← this]
    exact orderOf_dvd_natCard _
  obtain ⟨b, hbp, hkcard, hfixed⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.largeRee_fixed_data_of_odd hK hp hp2 β hβord
  have hfc := fieldCoreAt_reeGamma_F4 ha hK hp hp3 hδp hkcard hfixed hJdvd
  refine ⟨x, hxD, hxin, fieldCoreAt_of_conj hfc (MulAut.conj g₀)⁻¹ ?_⟩
  rw [hg₀]
  group

end ReeF4

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
