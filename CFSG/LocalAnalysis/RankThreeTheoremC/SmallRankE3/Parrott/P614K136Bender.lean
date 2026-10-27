module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Layer
public import CFSG.CGT.PushingUpLit.C2L.StrongTI
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136

open CFSG.Open Subgroup

theorem false_of_bender {K : Type} [Group K] [Finite K] (hB : fusionIsBenderGroup K)
    {R : Subgroup K} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRi : 2 ∣ R.index)
    (hRc : pCoreOf 2 (normalizer (R : Set K)) = R) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hRT⟩ := hR.exists_le_sylow
  have hsyl : ∀ S : Sylow 2 K, CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup K) ⊤ := fun S =>
    CFSG.ABGLocalTools.isSylowOf_iff.2
      ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hNT : normalizer (R : Set K) ≤ normalizer ((T : Subgroup K) : Set K) := by
    intro g hg
    by_contra hgT
    have hne : (T : Subgroup K) ≠ ((g • T : Sylow 2 K) : Subgroup K) := by
      intro h
      exact hgT (Sylow.smul_eq_iff_mem_normalizer.1 (Sylow.ext h).symm)
    have hbot :=
      CFSG.CGT.PushingUpLit.C2L.StrongTI.bender_sylow_inf_eq_bot hB (hsyl T) (hsyl (g • T)) hne
    apply hR1
    rw [eq_bot_iff, ← hbot]
    refine le_inf hRT fun r hr => ?_
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hr' : g⁻¹ * r * g ∈ R := by
      have := (mem_normalizer_iff.1 (inv_mem hg) r).1 hr
      simpa using this
    have := hRT hr'
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using this
  have hTN : (T : Subgroup K) ⊓ normalizer (R : Set K) ≤ R := by
    refine le_trans ?_ hRc.le
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (T.isPGroup'.to_le inf_le_left)
    intro g hg
    have hgT := hNT hg
    rw [mem_normalizer_iff] at hgT ⊢
    intro h
    rw [mem_inf, mem_inf, ← hgT h]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_mem (mul_mem hg h2) (inv_mem hg)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := mul_mem (mul_mem (inv_mem hg) h2) hg
      simpa [mul_assoc] using this
  have hRTeq : R = T := eq_of_inf_normalizer_le hRT T.isPGroup' hTN
  exact T.not_dvd_index (hRTeq ▸ hRi)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136
