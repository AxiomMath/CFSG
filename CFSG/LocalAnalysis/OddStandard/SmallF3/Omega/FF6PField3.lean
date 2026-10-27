module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSSwap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff6p_i1_cent (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L →
    ∀ y : G, orderOf y = 2 → y ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L y 6 1 1 α) →
        ∃ l ∈ L, ∃ B : Subgroup G, IsNormalE16In P B ∧
          ∀ n ∈ L ⊓ normalizer (B : Set G), (l⁻¹ * y * l) * n = n * (l⁻¹ * y * l) := by
  intro G _ _ L hL P hP y hy2 hyN hty
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ⟩ := ff6p_exists_model_P hL hP
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc hL
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6p_odd_center hL
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e hodd
  obtain ⟨α', hα'⟩ := ff6p_kind2 hc hL hQ hdim hsgn e hy2 hyN hty
  rcases ff6p_i1_cases hQ hdim fr hα' with ⟨nn, hnn⟩ | ⟨nn, hnn⟩
  · obtain ⟨l0, hl0⟩ := ff6mPhi_surjective e nn
    have hB1le : ffB1p hQ fr ≤ ffImg (ff6mPhi e) P := by
      rw [hPφ]
      exact ffB1p_le_ffP1p hQ fr
    obtain ⟨B, hBP, hBφ⟩ :=
      ff_cover_exists_of_le_img (B' := ffB1p hQ fr) hφ hP.1 hP.2.1 hB1le
    have hBnorm : IsNormalE16In P B := by
      refine (ff_cover_normalE16_iff hφ hP.1 hP.2.1 hBP).mpr ?_
      rw [hBφ, hPφ]
      exact ffB1p_normalE16 hQ hπ fr
    refine ⟨(l0 : G), l0.2, B, hBnorm, ?_⟩
    have hl0N : (l0 : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l0.2
    have hyyN : (l0 : G)⁻¹ * y * (l0 : G) ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (mul_mem ((Subgroup.normalizer (L : Set G)).inv_mem hl0N) hyN) hl0N
    have hmul : (⟨(l0 : G)⁻¹ * y * (l0 : G), hyyN⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨(l0 : G), Subgroup.le_normalizer l0.2⟩⁻¹ * ⟨y, hyN⟩ *
          ⟨(l0 : G), Subgroup.le_normalizer l0.2⟩ := Subtype.ext rfl
    have hθyy : ffTheta6P hQ hdim hsgn e ⟨(l0 : G)⁻¹ * y * (l0 : G), hyyN⟩ = ffTs fr := by
      rw [hmul, map_mul, map_mul, map_inv, ffTheta6P_of_mem, hl0, hnn]
      group
    intro m hm
    refine (ff6p_commute_normalizer_iff hQ hdim hsgn hz e hyyN (hBP.trans hP.1)).mpr ?_ m hm
    intro w hw
    rw [hBφ] at hw
    rw [hθyy]
    exact ffTs_comm_normalizer hQ h2 hπ fr hw
  · obtain ⟨l0, hl0⟩ := ff6mPhi_surjective e nn
    obtain ⟨y0, hy0G, hy0⟩ := ff6p_exists_y0 hQ hdim hsgn h2 fr
    have hB2le : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y0).toMonoidHom ≤ ffP1p hQ fr :=
      (ff6p_map_normalE16 hQ h2 fr hy0 (ffB1p_normalE16 hQ hπ fr)).1
    have hB2le' : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y0).toMonoidHom ≤
        ffImg (ff6mPhi e) P := by
      rw [hPφ]
      exact hB2le
    obtain ⟨B, hBP, hBφ⟩ := ff_cover_exists_of_le_img
      (B' := (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y0).toMonoidHom) hφ hP.1 hP.2.1 hB2le'
    have hBnorm : IsNormalE16In P B := by
      refine (ff_cover_normalE16_iff hφ hP.1 hP.2.1 hBP).mpr ?_
      rw [hBφ, hPφ]
      exact ff6p_map_normalE16 hQ h2 fr hy0 (ffB1p_normalE16 hQ hπ fr)
    refine ⟨(l0 : G), l0.2, B, hBnorm, ?_⟩
    have hl0N : (l0 : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l0.2
    have hyyN : (l0 : G)⁻¹ * y * (l0 : G) ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (mul_mem ((Subgroup.normalizer (L : Set G)).inv_mem hl0N) hyN) hl0N
    have hmul : (⟨(l0 : G)⁻¹ * y * (l0 : G), hyyN⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨(l0 : G), Subgroup.le_normalizer l0.2⟩⁻¹ * ⟨y, hyN⟩ *
          ⟨(l0 : G), Subgroup.le_normalizer l0.2⟩ := Subtype.ext rfl
    have hθyy : ffTheta6P hQ hdim hsgn e ⟨(l0 : G)⁻¹ * y * (l0 : G), hyyN⟩ =
        ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) := by
      rw [hmul, map_mul, map_mul, map_inv, ffTheta6P_of_mem, hl0, hnn]
      group
    intro m hm
    refine (ff6p_commute_normalizer_iff hQ hdim hsgn hz e hyyN (hBP.trans hP.1)).mpr ?_ m hm
    intro w hw
    rw [hBφ] at hw
    rw [hθyy]
    exact ff6p_tsz0_comm_normalizer_B2 hQ hdim hsgn h2 fr hy0G hy0 hw

end CFSG.OddStandard.SmallF3.Omega
