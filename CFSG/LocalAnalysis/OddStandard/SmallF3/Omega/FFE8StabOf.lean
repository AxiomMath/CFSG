module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Stab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8StabOfAux2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771In
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8StabOfAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem asc82E8Stab_of (hP : Asc82Tab6P) : Asc82E8Stab := by
  intro G _ _ K P hK hPsyl E z ν hE hEK hzP hzE hνK hν3 hνN hfix hbad Y hY hYC hYK hYP hYE
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ⟩ := ff6p_exists_model_P hK hPsyl
  have hz0 : Subgroup.center ↥K = ⊥ := by
    have h1 := hP.center_triv G K hK
    rw [centerIn] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h1
  haveI := ffOutFFE8Tr_finite_projSim Q
  have hρ : Function.Injective (ffOutFFE8TrRho hQ e) := ffOutFFE8TrRho_injective hQ hz0 e
  have hzK : z ∈ K := hEK hzE
  have hPK : P ≤ K := hPsyl.1
  have hρz : ffOutFFE8TrRho hQ e ⟨z, hzK⟩ = ffZ0Sim hQ fr :=
    ffOutFFE8TrStab_rho_z hQ hdim hsgn hz0 e fr hPφ hzP hzK
      (ffOutFFE8TrStab_ne_one hE hν3 hνN hfix)
  have hzT : SimHasType (ffOutFFE8TrRho hQ e ⟨z, hzK⟩) 4 1 := by
    rw [hρz]
    exact ffZ0s_hasType hQ fr
  have h := ffOutFFE8Tr_sdata hQ hdim hsgn hz0 e hE hEK hzE hνK hν3 hνN hfix hzT
  have hPimg := ffOutFFE8TrStab_thetaImg_P hQ hdim hsgn e fr hPK hPφ
  have hbad' : ¬ ffP1Sim hQ fr ≤
      normalizer (ffThetaImg (ffTheta6P hQ hdim hsgn e) E : Set (ProjSim Q)) := by
    rw [← hPimg, ffOutFFE8TrThetaImg_eq hQ hdim hsgn e hPK,
      ffOutFFE8TrThetaImg_eq hQ hdim hsgn e hEK]
    exact ffOutFFE8TrStab_not_le_normalizer hρ hPK hEK hbad
  have hθY := ffOutFFE8TrStab_restrict_injective hK hQ hdim hsgn e hYK hYC
  have hrangeY := ffOutFFE8TrStab_range_comp (ffTheta6P hQ hdim hsgn e) hYK
  have hcardY : Nat.card (ffThetaImg (ffTheta6P hQ hdim hsgn e) Y) = 128 := by
    rw [ffThetaImg, ← hrangeY, ← Nat.card_congr (MonoidHom.ofInjective hθY).toEquiv]
    exact hY
  have hYP' : ffThetaImg (ffTheta6P hQ hdim hsgn e) Y ≤ normalizer (ffP1Sim hQ fr : Set _) := by
    rw [← hPimg]
    exact ffOutFFE8TrMap_le_normalizer _ hYP
  have hYE' : ffThetaImg (ffTheta6P hQ hdim hsgn e) Y ≤
      normalizer (ffThetaImg (ffTheta6P hQ hdim hsgn e) E : Set (ProjSim Q)) :=
    ffOutFFE8TrMap_le_normalizer _ hYE
  obtain ⟨B', hB', y', hy', hy'B, hy'c⟩ :=
    ffE8_model_stab hQ hdim hsgn fr h hρz hbad' hcardY hYP' hYE'
  rw [ffThetaImg, ← hrangeY] at hB' hy'
  exact ffOutFFE8TrStab_pull_back hθY hB' hy' hy'B hy'c

end CFSG.OddStandard.SmallF3.Omega
