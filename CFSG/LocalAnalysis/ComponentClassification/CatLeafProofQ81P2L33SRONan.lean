module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.Sporadic.ONOddCore.CertifiedSimple
public import CFSG.Sporadic.ONOddCore.FullGroup

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.ONSchreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem on_centralizer_not_isPGroup
    {t : Pv} (ht : orderOf t = 2) : ¬ IsPGroup 2 ↥(centralizer ({t} : Set Pv)) := by
  obtain ⟨g, hg, hga⟩ := CFSG.Sporadic.ONOddCore.cti_on_all_involutions_conjugate
    (t : Equiv.Perm (Fin N)) t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
  set gP : Pv := ⟨g, hg⟩
  have hφt : MulAut.conj gP⁻¹ t = zP := by
    apply Subtype.ext
    show (g⁻¹ * (t : Equiv.Perm (Fin N)) * g⁻¹⁻¹) = onz
    rw [hga]
    group
  have e := CFSG.Sporadic.ONOddCore.centralizerCongr (MulAut.conj gP⁻¹) t
  rw [hφt, CFSG.Sporadic.ONOddCore.centralizer_zP] at e
  exact not_isPGroup_of_mulEquiv (e.trans (Subgroup.subgroupOfEquivOfLe onM_le))
    (not_isPGroup_of_three_dvd (by rw [card_onM]; norm_num))

@[expose] def ONOuterNoTwoFix :
    Prop :=
  ∀ α : MulAut Pv, α ∉ (MulAut.conj : Pv →* MulAut Pv).range → α * α = 1 →
    ¬ IsPGroup 2 ↥(fixedSubgroup α)

theorem sporNoTwoFix_ONan_of_outer
    (hout : ONOuterNoTwoFix) : SporNoTwoFix .ONan := by
  refine sporNoTwoFix_of_mulEquiv (P := ↥Pv) onEquivPv fun a ha => ?_
  have hs : IsSimpleGroup Pv := @MulEquiv.isSimpleGroup _ _ _ _
    CFSG.Sporadic.ONOddCore.fam_on_certified_simplicity.2 onEquivPv.symm
  have hZ : center Pv = ⊥ := center_eq_bot_of_not_prime hs card_Pv (by norm_num)
  by_cases hin : a ∈ (MulAut.conj : Pv →* MulAut Pv).range
  · obtain ⟨t, rfl⟩ := hin
    exact not_isPGroup_fixedPoints_conj hZ (fun t ht => on_centralizer_not_isPGroup ht) ha
  · exact hout a hin (by rw [← sq, ← ha, pow_orderOf_eq_one])

end CFSG.ComponentClassification.HarrisLit.L33.SR
