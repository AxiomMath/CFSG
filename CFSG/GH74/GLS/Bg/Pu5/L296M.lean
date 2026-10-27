module

public import CFSG.GH74.GLS.Bg.Pu5.L296Core
public import CFSG.GH74.GLS.Bg.Pu5.L293Step0

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem claimM_finish (h293 : L293) (h44 : II4_44) {z t : G} {S K U : Subgroup G}
    (h : Cfg295 G z t S K U) {L : Subgroup G} (hL : IsRigidRankOneComp t L) {t' : G}
    (ht'2 : orderOf t' = 2) (ht'L : t' ∈ L) (ht'z : z * t' = t' * z) (ht'K : t' ∈ cSec K) :
    False :=
  h293 G z t S h.cfg t' ht'2 (Subgroup.mem_centralizer_singleton_iff.2 ht'z.symm)
    ((rr_pcomp hL).1 ht'L) K h.hK ht'K L hL (rr_inv_mem_cSec h44 h.cfg.simple hL ht'L ht'2)

theorem claimM (h295 : L295) (h293 : L293) (hrec : Bg.B_reciprocity) (h2A7 : II4_2A7)
    (h44 : II4_44) (hquat : II4_4_quat) {z t : G} {S K U : Subgroup G}
    (h : Cfg295 G z t S K U) : False := by
  have hG : IsKProperSimple G := h.cfg.simple
  have hgen := h.cfg.gen4
  have hz2 : orderOf z = 2 := h.cfg.hz
  have ht2 : orderOf t = 2 := h.cfg.t_orderOf
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  by_cases hcase : ∃ y ∈ S ⊓ K, orderOf y = 2 ∧ y ≠ z
  ·
    obtain ⟨y, hySK, hy2, hyz⟩ := hcase
    obtain ⟨L, hL⟩ := rigid_nonempty ht2 h.cfg.t_mem_rigidProduct
    obtain ⟨u, v, t', huU, huz, hu2, hvL, hvz, hvP, hv4, ht'2, ht'L, ht'z, n, hn⟩ :=
      claimM_core h295 h293 h2A7 h44 h hL
    have hy1 : y ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    have hyU : y ∈ U := h.hzi y hySK hy2
    have hyZ : y ∈ zStar (rigidProduct z) :=
      mem_zStar_rigidProduct_of_involution h44 hG h.hK hySK.2 hy2
    have hzZ : z ∈ zStar (rigidProduct z) := self_mem_zStar_rigidProduct h.cfg.hzK
    have huZ : u ∈ zStar (rigidProduct z) := by
      rcases h.hU.eq_enum h.hzU hyU hz1 hy1 hyz.symm u huU with h1 | h1 | h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact hzZ
      · rw [h1]; exact hyZ
      · rw [h1]; exact mul_mem hzZ hyZ
    have hvC : v ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hvz.symm
    have hvN : v ∈ normalizer ((zStar (rigidProduct z) : Subgroup G) : Set G) :=
      normalizes_zStar_rigidProduct hvC
    have hcZ : v * u * v⁻¹ * u⁻¹ ∈ zStar (rigidProduct z) :=
      mul_mem ((mem_normalizer_iff.mp hvN u).mp huZ) (inv_mem huZ)
    have ht'Z : t' ∈ zStar (rigidProduct z) := by
      rw [hn]
      exact pow_mem hcZ n
    have ht'K : t' ∈ cSec K :=
      mem_cSec_of_mem_zStar h44 hquat hG hgen ht'Z (exists_two_pow_eq_one_of_orderOf ht'2) h.hK
    exact claimM_finish h293 h44 h hL ht'2 ht'L ht'z ht'K
  ·
    push Not at hcase
    obtain ⟨w₀, hw₀SK, hw₀2⟩ := exists_involution_inf hquat hG h.hK h.cfg.sylow
    have hzK : z ∈ K := by
      rw [← hcase w₀ hw₀SK hw₀2]
      exact hw₀SK.2
    obtain ⟨c₀, hc₀⟩ := isConj_iff.1 h.cfg.conj
    have hL : IsRigidRankOneComp t (cmap c₀ K) := by
      rw [← hc₀]
      exact ⟨isPRigid_cmap h.hK.1 c₀, by rw [pRank_cmap]; exact h.hK.2⟩
    have htL : t ∈ cmap c₀ K := by
      rw [← hc₀]
      exact conj_mem_cmap' hzK c₀
    obtain ⟨u, v, t', huU, huz, hu2, hvL, hvz, hvP, hv4, ht'2, ht'L, ht'z, n, hn⟩ :=
      claimM_core h295 h293 h2A7 h44 h hL
    obtain ⟨ha, -, -⟩ := h295 G z t S h.cfg K h.hK U h.hU h.hUle h.hzU h.hzi
    have hzN : z ∈ normalizer ((cmap c₀ K : Subgroup G) : Set G) := ha _ hL h.hzU
    have hzt : Commute z t := (Subgroup.mem_centralizer_singleton_iff.1 h.cfg.tC).symm
    obtain ⟨-, hrec2⟩ := hrec G hG z t hz2 ht2 hzt K (cmap c₀ K)
      ⟨rr_pcomp h.hK, h.hK.2, hzK⟩ ⟨rr_pcomp hL, hL.2, htL⟩
    have hvnot : v ∉ zpowers t := by
      intro hv
      have h1 : orderOf v ∣ orderOf t := orderOf_dvd_of_mem_zpowers hv
      rw [ht2] at h1
      have h2 : 4 ∣ 2 := hv4.trans h1
      omega
    have hvK : v ∈ normalizer (K : Set G) := hrec2 hzN v hvL hvP hvnot hvz.symm
    have hcK : v * u * v⁻¹ * u⁻¹ ∈ cSec K :=
      mul_mem (C3.Layer1.PumpCalc.conj_mem_cSec hvK (h.mem_cSec huU)) (inv_mem (h.mem_cSec huU))
    have ht'K : t' ∈ cSec K := by
      rw [hn]
      exact pow_mem hcK n
    exact claimM_finish h293 h44 h hL ht'2 ht'L ht'z ht'K

end CFSG.GH74.GLS.Bg.Pu5
