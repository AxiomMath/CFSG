module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18Basic
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18Rk
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18Sub
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Alt2D
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Five
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
open CFSG.LocalAnalysis.EvenBN.Tits.N.P4 CFSG.Goldschmidt

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem card_zpowers_le_two_of_mul_self {X : Type*} [Group X] {a : X} (h : a * a = 1) :
    Nat.card (zpowers a) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h))

theorem card_commImg_pv7_le (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hκ : d.S56Kappa) (h10 : Node10 d z₀) : Nat.card (commImg (star d (d.pv 7))) ≤ 8 := by
  obtain ⟨-, hab, hcard, -, -, -, -, hVN, -⟩ := id h10
  have hH7 : d.pv 7 ∈ Hg d := (pv7_star h49 hd hz h10).2.2
  exact card_commImg_le_eight (V := d.s56V) (N := d.N) (U11 := d.s56U11) (f := d.pv 7) hab hcard
    hVN (Data.s56_card_U11 d) hH7 fun x hx => hκ x hx (d.pv 7) hd.s56_pv7_mem_F

theorem card_fixSub_x5_le_four (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h10 : Node10 d z₀) : Nat.card (fixSub (star d d.x₅)) ≤ 4 := by
  obtain ⟨-, hab, -⟩ := id h10
  have hzV : d.z ∈ d.s56V := hd.s56_E_le_V h49 hd.s56_z_mem_E
  have hzz : d.z * d.z = 1 := hab.mul_self_eq_one hzV
  have hz0z0 : z₀ * z₀ = 1 := hab.mul_self_eq_one hz.mem_V
  have hzz0 : d.z * z₀ = z₀ * d.z := hab.comm hzV hz.mem_V
  have hnorm : zpowers d.z ≤ normalizer ((zpowers z₀ : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    rintro g ⟨n, rfl⟩
    exact (Commute.zpow_left (show Commute z₀ d.z from hzz0.symm) n).eq
  have hprod := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hnorm
  have hpos : 0 < Nat.card ↥(zpowers d.z ⊓ zpowers z₀) := Nat.card_pos
  have hZ : Nat.card ↥(zpowers d.z ⊔ zpowers z₀) ≤ 4 := by
    calc Nat.card ↥(zpowers d.z ⊔ zpowers z₀)
        ≤ Nat.card ↥(zpowers d.z ⊔ zpowers z₀) * Nat.card ↥(zpowers d.z ⊓ zpowers z₀) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card (zpowers d.z) * Nat.card (zpowers z₀) := hprod
      _ ≤ 2 * 2 := Nat.mul_le_mul (card_zpowers_le_two_of_mul_self hzz)
          (card_zpowers_le_two_of_mul_self hz0z0)
  refine card_fixSub_le_four (V := d.s56V) (Z := zpowers d.z ⊔ zpowers z₀) (x := d.x₅)
    (x5_mem_Hg h49 hd) hZ ?_
  intro w hw hxw
  have hvc : w ∈ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    rintro g ⟨n, rfl⟩
    exact (Commute.zpow_left (show Commute d.x₅ w from hxw) n).eq
  have hmem : w ∈ d.s56Q ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨hw.1, hvc⟩
  rw [hd.s56_CQX_eq h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.dich] at hmem
  exact hmem

theorem step18_of_top (hTop : TopStatement) : Step18 := by
  intro G _ _ d z₀ h49 hd hz hκ h09 h10 h14 h17s h17
  obtain ⟨y₁, hy⟩ := exists_V1_of_node09 h09
  obtain ⟨hF, hCe, hinf, hcomm⟩ := C_data h49 hd hz h10 h17s hy
  obtain ⟨htU, htnU⟩ := t_comm_and_not_mem h49 hd hz h10 h17s hy
  have htt := star_t_mul_self h49 hd
  have htH : d.t ∈ Hg d := t_mem_Hg h49 hd
  have hstarH : ∀ h ∈ Hg d, star d h ∈ Hs d := fun h hh => actFun_mem_imgIn hh hh
  have hH_of : ∀ g ∈ Hs d, ∃ h ∈ Hg d, star d h = g := fun g hg => by
    obtain ⟨h, hh, -, hhg⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 hg
    exact ⟨h, hh, hhg⟩
  refine node18_of_surj h49 hd hz h09 h10 h17s h17 ?_
  have hCt : ∀ g ∈ Hs d, g * star d d.t = star d d.t * g →
      g ∈ zpowers (star d d.t) ⊔ IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) := by
    intro g hg hgt
    rw [← hCe, h17.2.2.2.1]
    exact ⟨mem_centralizer_singleton_iff.2 hgt, hg⟩
  have hnotU : ∀ g ∈ Hs d, g * star d d.t * g⁻¹ ∉ Us d := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := hH_of g hg
    rw [← star_conj_of_mem hh htH]
    exact h17.2.2.2.2.2 h hh
  have h66 : ∃ u ∈ Us d, u ≠ 1 ∧ ∃ g ∈ Hs d, g * star d d.t * g⁻¹ = star d d.t * u := by
    obtain ⟨g, hg, u, hu, hu1, hgt⟩ := fusion_t_pv7 h49 hd hz h10 h14.2.1.2
    exact ⟨u, hu, hu1, g, hg, hgt⟩
  have hv2C : star d (d.pv 2) ∈ img d (CMt d) :=
    actFun_mem_imgIn (sylT_le_CMt hd (pv2_mem_sylT hd)) (pv2_mem_Hg h49 hd)
  have hv2N : star d (d.pv 2) ∈ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) := by
    rw [hCe] at hv2C
    refine (sup_le ?_ (hF.Pgrp_le_normalizer)) hv2C
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro u hu
    exact (hcomm u (IsF20.U_le_Pgrp _ _ _ hu)).symm
  have hv2t : star d (d.pv 2) * star d d.t = star d d.t * star d (d.pv 2) := by
    have h := hv2C
    rw [h17.2.2.2.1] at h
    exact mem_centralizer_singleton_iff.1 h.1
  have h67 : ∃ w g : MulAut ↥d.s56V, w ∈ Hs d ∧ g ∈ Hs d ∧
      w ∈ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) ∧
      w * star d d.t = star d d.t * w ∧ w * star d d.x₅ * w⁻¹ = (star d d.x₅)⁻¹ ∧
      g * star d d.t * g⁻¹ = star d d.t * w := by
    obtain ⟨h, hh, hst⟩ := h14.2.2.2
    refine ⟨star d (d.pv 2), star d h, hstarH _ (pv2_mem_Hg h49 hd), hstarH _ hh, hv2N, hv2t,
      star_pv2_inv_x5 h49 hd, ?_⟩
    rw [← star_conj_of_mem hh htH, hst, star_eq, star_eq, star_eq,
      actFun_mul d.s56V htH (pv2_mem_Hg h49 hd)]
  obtain ⟨-, hab, hcard, -⟩ := id h10
  have hc : ∀ a b : ↥d.s56V, a * b = b * a := fun a b => Subtype.ext (hab.comm a.2 b.2)
  have h2 : ∀ w : ↥d.s56V, w * w = 1 := fun w => Subtype.ext (hab.mul_self_eq_one w.2)
  have hrk4 : ∀ y ∈ Hs d, ∀ g ∈ Hs d, y * y = 1 →
      y * (g * star d d.x₅ * g⁻¹) * y⁻¹ = (g * star d d.x₅ * g⁻¹)⁻¹ →
        16 ≤ Nat.card (commImg y) := by
    intro y _ g _ hy hyx
    have hx5 : (g * star d d.x₅ * g⁻¹) ^ 5 = 1 := by
      rw [conj_pow, hF.x5]
      group
    have hfix : Nat.card (fixSub (g * star d d.x₅ * g⁻¹)) ≤ 4 := by
      rw [card_fixSub_conj]
      exact card_fixSub_x5_le_four h49 hd hz h10
    exact sixteen_le_card_commImg hc h2 hy hx5 hyx hcard hfix
  obtain ⟨hu7, hu71, -⟩ := pv7_star h49 hd hz h10
  have hfin := delta_surj_sub hTop (H := Hs d) (U := Us d) (x := star d d.x₅) (v := star d y₁)
    (t := star d d.t) (fun y => Nat.card (commImg y)) (Us_le_Hs h49 hd hz h10)
    (hstarH _ (x5_mem_Hg h49 hd)) (hstarH _ (y1_mem_Hg h49 hd hy)) (hstarH _ htH) hF htt htnU hcomm
    hinf hCt hnotU h66 h67 (fun g _ y _ => card_commImg_conj g y)
    ⟨star d (d.pv 7), hu7, hu71, card_commImg_pv7_le h49 hd hz hκ h10⟩ hrk4
  intro u hu
  obtain ⟨g, hg, hgt⟩ := hfin u hu
  obtain ⟨h, hh, rfl⟩ := hH_of g hg
  refine ⟨mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hu), h, hh, ?_⟩
  rw [star_conj_of_mem hh htH]
  exact hgt

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
