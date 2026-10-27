module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeG2Core
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeG2
public import CFSG.RankThree.PartOne.SEITZ2.Common
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.AlgebraicGroups

section ReeG2


theorem isLocallyBalancedAbs_two_reeGamma_G2 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : IsLocallyBalancedAbs p 2 (ReeTag.G2.reeGamma K a) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ReeTag.G2.reeGamma K a) := inferInstance
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.center_reeGamma_G2_eq_bot hK)
  have hcyc : IsCyclic (MulAut (ReeTag.G2.reeGamma K a) ⧸ innerAut (ReeTag.G2.reeGamma K a)) :=
    isCyclic_outer_of_gen _
      (CFSG.ComponentClassification.LiteratureLocal.SmallRee.exists_eq_conj_mul_frobeniusΓ_pow
        ha hK)
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj ?_ ?_
  · intro E hEin hE hEc H hH
    refine (CFSG.LieType.SeitzGeneration.false_of_inner_plane_of_no_plane hinj
      (fun F hF hFc => ?_) hE hEc hEin).elim
    have : IsElementaryAbelian p ↥F :=
      CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian hF
    exact CFSG.LieType.SeitzGeneration.no_plane_reeGamma_G2 ha hK hp hp3
      (E := F.map (ReeTag.G2.reeGamma K a).subtype) (Subgroup.map_subtype_le F)
      (IsElementaryAbelian.map _)
      (by rw [Subgroup.card_map_of_injective (ReeTag.G2.reeGamma K a).subtype_injective, hFc])
  · intro D hD hDc hDin
    have hDe := CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian hD
    obtain ⟨g, hg1, hgD⟩ := CFSG.RankThree.PartOne.SEITZ2.exists_conj_mem_of_plane_of_cyclic_outer
      hp hcyc D hDc
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
    have hxp : x ^ p = 1 := hD.2 x hxD
    have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
    obtain ⟨hpf, δ', σ, hσ, hconj, hcard, hfixed⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hp hp2 x
        hxp (fun ⟨y, hy⟩ => hxin ⟨y, hy⟩)
    have hδp : orderOf (ReeTag.G2.reeGammaFieldAut K a σ) = p := by
      rw [← hconj]
      exact (MulEquiv.orderOf_eq (MulAut.conj δ') x).trans hxord
    have hxh : x = δ'⁻¹ * ReeTag.G2.reeGammaFieldAut K a σ * δ'⁻¹⁻¹ := by
      rw [← hconj]; group
    have hy1 : (MulAut.conj g : MulAut (ReeTag.G2.reeGamma K a)) ≠ 1 := fun h1 =>
      hg1 (hinj (by rw [h1, map_one]))
    have hyp : (MulAut.conj g : MulAut (ReeTag.G2.reeGamma K a)) ^ p = 1 := hD.2 _ hgD
    have hcomm : (MulAut.conj g : MulAut (ReeTag.G2.reeGamma K a)) * x =
        x * MulAut.conj g :=
      congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hgD⟩ ⟨x, hxD⟩)
    obtain ⟨k₀, hk₀δ, hk₀ord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh ⟨g, rfl⟩ hy1
      hyp hcomm
    have hJdvd : p ∣ Nat.card ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus
        (MonoidHom.id _)) := by
      have hk₀J : k₀ ∈ (ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus
          (MonoidHom.id _) := hk₀δ
      have : orderOf (⟨k₀, hk₀J⟩ : ↥((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus
          (MonoidHom.id _))) = p := by
        rw [Subgroup.orderOf_mk]
        exact hk₀ord
      rw [← this]
      exact orderOf_dvd_natCard _
    obtain ⟨d, hd⟩ := hpf
    have hd' : (2 * a + 1) / p = d := by rw [hd, Nat.mul_div_cancel_left _ hp.pos]
    have hdodd : Odd d := by
      have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
      exact (Nat.odd_mul.1 h1).2
    obtain ⟨b, hb⟩ := hdodd
    have hbd : ((2 * a + 1) / p - 1) / 2 = b := by rw [hd', hb]; omega
    rw [hbd] at hfixed
    have hkcard : Nat.card (fixSubfield σ) = 3 ^ (2 * b + 1) := by rw [hcard, hd', hb]
    have hfc := fieldCoreAt_reeGamma_G2 ha hK hp hp3 hδp hkcard hfixed hJdvd
    exact ⟨x, hxD, hxin, fieldCoreAt_of_conj hfc δ' hconj⟩

end ReeG2

section Family


theorem crossCharTwoFamCat_reeG2 : CrossCharTwoFamCat .reeG2 := by
  rintro ⟨d, hv⟩ ⟨m, rfl⟩ p hp hp5 _ _
  have hp3 : 3 < p := by omega
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat_G2 hv
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_two_reeGamma_G2 hm1 hX hp hp3)

end Family

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
