module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue5
public import CFSG.GH74.Uniqueness.SU.SU1BgMaxClass
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9CaseA

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem Std4r1.F_eq (h : Std4r1 G z S K F) (hQF : Qz S z = F) : F = S ⊓ cSec K := by
  rw [← hQF, h.Qz_eq]

theorem cfg1K_Q (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (h : Std4r1 G z S K F) (hQF : Qz S z = F) :
    R1.Cfg1K G z S (S ⊓ K) (S ⊓ cSec K) (S ⊓ cSec K) (fun s => InducesFAut s K) := by
  have hF := h.F_eq hQF
  have := cfg1K_of_std hII hq hdiag h19 hsd hsdq hqc hrn h
  rw [hF] at this
  exact this

theorem caseA_std (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (hZsq : Z_not_sq) (hshape : Bg.B_two_maximalClass_shape) (h : Std4r1 G z S K F) (hQF : Qz S z = F)
    (hquat : ∃ n, IVK.IsQuaternionTwoGroup ↥F n)
    (hcase : ∀ t ∈ Rz S z, IsConj z t → t = z) : False := by
  have hF := h.F_eq hQF
  have hcfg := cfg1K_Q hII hq hdiag h19 hsd hsdq hqc hrn h hQF
  obtain ⟨nQ, hnQ⟩ : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n := hF ▸ hquat
  refine hcfg.caseA hnQ ?_ ?_
    CFSG.GH74.Uniqueness.SU.SU1.b_maximalClass_of_small_centralizer hshape h.hZ ?_
  · intro y hyS hy2 hyR hzy w hw
    exact hZsq G z S K F h hQF y hyS hzy (by rw [h.Rz_eq]; exact hyR) w hw
  · intro y hy2 hyQ hyn hSD v hv hvy
    exact (hsd G (S ⊓ cSec K) z y ⟨nQ, hnQ⟩ (h.z_mem_Q hII) h.z_sq h.z_ne hy2 hyQ hyn hSD).2 v hv hvy
  · intro w hwR hw2 hw1 hwz hconj
    exact hwz (hcase w (by rw [h.Rz_eq]; exact hwR) hconj)

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
