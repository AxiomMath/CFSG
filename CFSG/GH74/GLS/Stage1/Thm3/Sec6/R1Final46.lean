module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46d
public import CFSG.GH74.Uniqueness.SU.SU1BgMaxClass

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

namespace Std4r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem hasSL2_of_cyclic (h : Std4r1 G z S K F) (h44 : II4_44)
    (hc : R1.Cfg1K G z S (S ⊓ K) (S ⊓ cSec K) F (fun s => InducesFAut s K)) (hF : IsCyclic ↥F) :
    HasSL2Model (HatT K) Odd := by
  have hsl : IsSL2Or2A7 (↥K ⧸ pPrimeCore 2 ↥K) :=
    h44 G h.simple z h.orderOf_z K h.comp_isPCompIn h.comp_pRank
  rcases hsl.1 with ⟨Fq, hF', hfin, hodd, hiso⟩ | h2A7
  · exact ⟨Fq, hF', hfin, hodd.1, hiso⟩
  · exfalso
    have hS := h.eq_of_2A7 h2A7
    obtain ⟨E, hES, hEx, hE8⟩ := h.hasE8
    have hEPF : E ≤ S ⊓ K ⊔ F := by rw [← h.Pz_eq, ← hS]; exact hES
    have := hc.toCfg1.card_PF_le hF hEPF hEx
    omega

omit [Finite G] in
theorem four_of (U : Subgroup G) (hU : IVK.IsFourSubgroup U) : R1.Four U := by
  refine ⟨fun a ha => ?_, hU.2⟩
  have := hU.1
  have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a ha
  simpa [pow_two] using h2

end Std4r1

theorem prop_4_6 (hII : II4_4_4_center) (h44 : II4_44) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr)
    (hrn : Rnormal4) (h119 : IVK_1_19_V) (hSR : IVK_SR_abelian) (hCR : II4_ord4_R) : Prop4_6 := by
  intro G _ _ z S K F h hF
  have hc := cfg1K_of_std hII hq hdiag h19 hsd hsdq hqc hrn h
  have hsl := h.hasSL2_of_cyclic h44 hc hF
  have h119' : ∀ s ∈ S ⊓ K ⊔ F, s ∉ S ⊓ K ⊔ S ⊓ cSec K → ∀ V : Subgroup G, V ≤ S ⊓ K →
      IsCyclic ↥V → V.relIndex (S ⊓ K) = 2 → ∃ v ∈ V, s * v ≠ v * s := by
    intro s hs hsR V hV hVc hVi
    exact h119 G z S K F h hF hsl s (by rwa [h.Pz_eq]) (by rw [h.Rz_eq]; exact hsR) V
      (by rwa [h.Pz_eq]) hVc (by rwa [h.Pz_eq])
  have hSR' : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ S ⊓ K ⊔ S ⊓ cSec K := by
    intro a ha b hb
    have := hSR G z S K F h a ha b hb
    rwa [h.Rz_eq] at this
  have hCR' : ∀ w ∈ S ⊓ K ⊔ S ⊓ cSec K, ∀ w' ∈ S ⊓ K ⊔ S ⊓ cSec K, w * w = 1 → w' * w' = 1 →
      w ≠ 1 → w ≠ z → w' ≠ 1 → w' ≠ z → IsConj w w' := by
    intro w hw w' hw' hw2 hw'2 hw1 hwz hw'1 hw'z
    exact hCR G z S K F h hF w (by rw [h.Rz_eq]; exact hw) w' (by rw [h.Rz_eq]; exact hw')
      hw2 hw'2 hw1 hwz hw'1 hw'z
  exact hc.prop46 hF CFSG.GH74.Uniqueness.SU.SU1.b_maximalClass_of_small_centralizer h119'
    h.hThompson h.hTransfer h.hZ hSR' hCR'

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
