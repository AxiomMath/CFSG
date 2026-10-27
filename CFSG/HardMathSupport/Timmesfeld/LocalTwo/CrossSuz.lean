module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzMain
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_injective)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Suzuki


theorem isLocallyBalancedAbs_two_suzukiGroup {a : ℕ} (ha : 1 ≤ a) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    IsLocallyBalancedAbs p 2 (suzukiGroup a F) := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (MulAut.conj : suzukiGroup a F →* MulAut (suzukiGroup a F)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hF)
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj ?_ ?_
  · intro E hEin hE hEc H hH
    exact (suzuki_no_inner_plane ha hF hp hp2 hE hEc hEin).elim
  · intro D hD hDc hDin
    have hDe := CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian hD
    obtain ⟨g, hg1, hgD⟩ := CFSG.RankThree.PartOne.SEITZ2.exists_conj_mem_of_plane_suzuki hp ha hF D
      hDc
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
    have hxp : x ^ p = 1 := hD.2 x hxD
    have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
    obtain ⟨σ, h, b, k, _, _, hσp, hbp, hkc, hconj, ⟨eH⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha F hF p hp hp2 x hxord
        (fun ⟨y, hy⟩ => hxin ⟨y, hy⟩)
    set δ := szFieldAut a F σ with hδ
    have hδp : orderOf δ = p := by
      rw [hδ, orderOf_injective (szFieldAut a F) szFieldAut_injective, hσp]
    have hxh : x = (MulAut.conj h)⁻¹ * δ * (MulAut.conj h)⁻¹⁻¹ := by
      rw [← hconj]; group
    have hy1 : (MulAut.conj g : MulAut (suzukiGroup a F)) ≠ 1 := fun h1 =>
      hg1 (hinj (by rw [h1, map_one]))
    have hyp : (MulAut.conj g : MulAut (suzukiGroup a F)) ^ p = 1 := hD.2 _ hgD
    have hcomm : (MulAut.conj g : MulAut (suzukiGroup a F)) * x = x * MulAut.conj g :=
      congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hgD⟩ ⟨x, hxD⟩)
    obtain ⟨k₀, hk₀δ, hk₀ord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh ⟨g, rfl⟩ hy1
      hyp hcomm
    have hJdvd : p ∣ Nat.card ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) := by
      have hk₀J : k₀ ∈ (szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _) := hk₀δ
      have : orderOf (⟨k₀, hk₀J⟩ : ↥((szFieldAut a F σ).toMonoidHom.eqLocus
          (MonoidHom.id _))) = p := by
        rw [Subgroup.orderOf_mk]
        exact hk₀ord
      rw [← this]
      exact orderOf_dvd_natCard _
    have hb1 : 1 ≤ b := by
      by_contra hb0
      have hb0' : b = 0 := by omega
      subst hb0'
      have h20 : Nat.card ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) = 20 := by
        rw [Nat.card_congr eH.toEquiv, CFSG.LieType.Ree.suzuki_order hkc]
        norm_num
      rw [h20] at hJdvd
      have hle : p ≤ 20 := Nat.le_of_dvd (by norm_num) hJdvd
      interval_cases p <;> omega
    obtain ⟨-, hnt, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple hb1 hkc
    have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot hb1 hkc
    have : IsSimpleGroup ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) :=
      eH.isSimpleGroup
    have hJq : CFSG.IsQuasisimple ((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) :=
      isQuasisimple_of_simple_nonabelian fun hc => by
        have hcen : Subgroup.center (suzukiGroup b k) = ⊤ :=
          Subgroup.eq_top_iff' _ |>.2 fun z => Subgroup.mem_center_iff.2 fun w => by
            have := congrArg eH (hc (eH.symm w) (eH.symm z))
            rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
            exact this
        obtain ⟨z, hz⟩ := exists_ne (1 : suzukiGroup b k)
        have hz' : z ∈ Subgroup.center (suzukiGroup b k) := by rw [hcen]; trivial
        rw [hZ] at hz'
        exact hz (Subgroup.mem_bot.1 hz')
    refine ⟨x, hxD, hxin, ?_⟩
    refine fieldCoreAt_of_canonical_conj_primeFaithful hp hinj hδp hJq (fun z => Iff.rfl) ?_ hxh
      ⟨g, rfl⟩ hy1 hyp hcomm
    intro g' hgr hgp hc' hfix
    exact suzuki_prime_faithful ha hF hp hp5 hσp hbp hkc eH hJdvd g' hgr hgp hc' hfix

theorem crossCharTwoFamCat_suzuki : CrossCharTwoFamCat .suzuki := by
  rintro ⟨d, hv⟩ ⟨m, hd⟩ p hp hp5 _ _
  change d = _ at hd
  subst hd
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.suzukiModel_cat hv
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_two_suzukiGroup ha hF' hp hp5)

end Suzuki

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
