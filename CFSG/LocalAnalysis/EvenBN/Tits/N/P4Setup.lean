module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Mod
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Y
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Setup

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem x5_ne_one (hd : d.Hyp) : d.x₅ ≠ 1 := by
  intro h
  have := hd.s56_orderOf_x5
  rw [h, orderOf_one] at this
  omega

theorem isFrob_G (hd : d.Hyp) (hz : d.S56Z0 z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) : IsFrob d.x₅ y₁ :=
  ⟨by rw [← hd.s56_orderOf_x5]; exact pow_orderOf_eq_one _, x5_ne_one hd, hy.pow_four hd hz,
    hy.conj_x5 hd⟩

theorem y1_mem_normalizer_Xg (hd : d.Hyp) (hz : d.S56Z0 z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    y₁ ∈ normalizer ((Xg d : Subgroup G) : Set G) :=
  (isFrob_G hd hz hy).y_mem_normalizer

theorem isF20_Us (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hU : IsElemAbelian 2 (Us d)) (hU16 : Nat.card (Us d) = 16) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    IsF20 (Us d) (star d d.x₅) (star d y₁) := by
  have hfrob := hy.isFrob h49 hd hz h10
  refine isF20_of_data hU hU16 (star_x5_mem_normalizer_Us h49 hd)
    (star_mem_normalizer_Us h49 hd (hy.mem_CMt hd) (y1_mem_normalizer_Xg hd hz hy))
    hfrob.x5 hfrob.y4 hfrob.yx ?_
  intro u hu hfix
  obtain ⟨q, hq, rfl⟩ := (mem_Us_iff h49 hd hz h10).1 hu
  obtain ⟨hqQ, hqM, hqt⟩ := mem_Qp_iff.1 hq
  have hxM : d.x₅ ∈ d.M := hd.s56_x5_mem_M
  have hxQ : d.x₅ ∈ normalizer (d.s56Q : Set G) := hd.s56_M_le_normalizer_Q h49 hxM
  have hxN : d.x₅ ∈ normalizer (d.s56V : Set G) := x5_mem_Hg h49 hd
  have hqN : q ∈ normalizer (d.s56V : Set G) := Qp_le_Hg h49 hd hq
  have hxq : d.x₅ * q * d.x₅⁻¹ ∈ normalizer (d.s56V : Set G) :=
    mul_mem (mul_mem hxN hqN) (inv_mem hxN)
  have hstar : actFun d.s56V (d.x₅ * q * d.x₅⁻¹) = actFun d.s56V q := by
    rw [actFun_conj d.s56V hxN hqN]
    exact hfix
  have hcv : (d.x₅ * q * d.x₅⁻¹)⁻¹ * q ∈ centralizer (d.s56V : Set G) :=
    (actFun_eq_iff d.s56V hxq hqN).1 hstar
  have hxqQ : d.x₅ * q * d.x₅⁻¹ ∈ d.s56Q := (mem_normalizer_iff.1 hxQ q).1 hqQ
  have hwV : (d.x₅ * q * d.x₅⁻¹)⁻¹ * q ∈ d.s56V := by
    rw [← Q_inf_Cv h49 hd h10]
    exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hxqQ) hqQ, hcv⟩
  have hz1 : q⁻¹ * (d.x₅ * q * d.x₅⁻¹) ∈ d.s56V := by
    have := inv_mem hwV
    simpa [mul_assoc] using this
  have h5 : ¬ 5 ∣ Nat.card d.s56V := by
    rw [h10.card_V]
    norm_num
  obtain ⟨e, he, hfix2⟩ := CFSG.LocalAnalysis.EvenBN.Tits.S56.exists_fixed_point_of_conj_stable_coset
    hd.s56_orderOf_x5 hxN hz1 h5
  have hqe : q * e ∈ d.s56Q ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem hqQ (V_le_Q he), ?_⟩
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := hg
    have hc : d.x₅ * (q * e) = (q * e) * d.x₅ := by
      calc d.x₅ * (q * e) = (d.x₅ * (q * e) * d.x₅⁻¹) * d.x₅ := by group
        _ = (q * e) * d.x₅ := by rw [hfix2]
    exact ((Commute.zpow_left (show Commute d.x₅ (q * e) from hc) n).eq)
  rw [hd.s56_CQX_eq h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.dich] at hqe
  have hqeV : q * e ∈ d.s56V := Zz_le_V hd h49 hz hqe
  have hqV : q ∈ d.s56V := by
    have : q = (q * e) * e⁻¹ := by group
    rw [this]
    exact mul_mem hqeV (inv_mem he)
  show star d q = 1
  exact star_V h10 hqV

theorem P_eq (h49 : d.Thm49Statement) (hd : d.Hyp) (y₁ : G) :
    Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) = IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) := by
  rw [IsF20.Pgrp_eq, img_Xg h49 hd]

end Setup

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
