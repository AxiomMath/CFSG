module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenPair
public import Certificates.Certificate125560
public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.RankThree.PartOne.CTP.Fus CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.Gen13
open scoped commutatorElement

private theorem gw_eq_of_agreeC
    {w₁ w₂ : List Native.Gen}
    (h : agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) w₁ w₂ = true) : gw w₁ = gw w₂ :=
  agree_sound (by rwa [agreeC_eq] at h)

theorem thirteen_eligible_check : thirteenEligibleCheck () = true :=
  Certificates.certificate125560

theorem gw_eq_of_wordLin {w₁ w₂ : List Native.Gen} (h : wordLin w₁ = wordLin w₂) : gw w₁ = gw w₂ :=
  Subtype.ext h

theorem thirteen_gw_facts :
    gw thirteenX ^ 13 = 1 ∧ gw thirteenY ^ 13 = 1 ∧
      ⁅gw thirteenX, gw thirteenY⁆ = gw thirteenZ ∧ gw thirteenZ ≠ 1 ∧
      Commute (gw thirteenZ) (gw thirteenX) ∧ Commute (gw thirteenZ) (gw thirteenY) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, h8⟩ := thirteen_relations
  have hx : gw thirteenX ^ 13 = 1 := Subtype.ext (by simpa using thirteen_x_pow)
  have hxi : gw thirteenXi = (gw thirteenX)⁻¹ := by
    have := gw_eq_of_wordLin h1
    rw [gw_append, gw_nil] at this
    exact eq_inv_of_mul_eq_one_left this
  have hki : gw thirteenKi = (gw thirteenK)⁻¹ := by
    have := gw_eq_of_wordLin h2
    rw [gw_append, gw_nil] at this
    exact eq_inv_of_mul_eq_one_left this
  have hy : gw thirteenY = gw thirteenK * gw thirteenX * (gw thirteenK)⁻¹ := by
    simp only [thirteenY, gw_append, hki, mul_assoc]
  have hyi : gw thirteenYi = gw thirteenK * (gw thirteenX)⁻¹ * (gw thirteenK)⁻¹ := by
    simp only [thirteenYi, gw_append, hki, hxi, mul_assoc]
  have hcomm : ⁅gw thirteenX, gw thirteenY⁆ = gw thirteenZ := by
    rw [← gw_eq_of_wordLin h3, hy]
    simp only [gw_append, hy, hyi, hxi, commutatorElement_def]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hzx : Commute (gw thirteenZ) (gw thirteenX) := by
    have := gw_eq_of_wordLin h4
    simp only [gw_append] at this
    exact this
  have hza : Commute (gw thirteenZ) (gw thirteenK) := by
    have := gw_eq_of_wordLin h5
    simp only [gw_append] at this
    exact this
  have hzy : Commute (gw thirteenZ) (gw thirteenY) := by
    rw [hy]
    exact (hza.mul_right hzx).mul_right hza.inv_right
  refine ⟨hx, ?_, hcomm, fun h => h8 (by simpa using congrArg Subtype.val h), hzx, hzy⟩
  rw [hy, conj_pow, hx, mul_one, mul_inv_cancel]

theorem thirteen_commute_facts :
    Commute (gw gen13W0) (gw thirteenX) ∧ Commute (gw gen13W1) (gw thirteenX) ∧
    Commute (gw thirteenK) (gw thirteenZ) ∧ Commute (gw gen13W5) (gw thirteenZ) ∧
    Commute (gw gen13W6) (gw thirteenZ) ∧ Commute (gw gen13W7) (gw thirteenZ) ∧
    Commute (gw thirteenT0) (gw thirteenZ) := by
  have h := thirteen_eligible_check
  simp only [thirteenEligibleCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := gw_eq_of_agreeC h1; simp only [gw_append] at this; exact this.symm
  · have := gw_eq_of_agreeC h2; simp only [gw_append] at this; exact this.symm
  · have := gw_eq_of_agreeC h3; simp only [gw_append] at this; exact this.symm
  · have := gw_eq_of_agreeC h4; simp only [gw_append] at this; exact this.symm
  · have := gw_eq_of_agreeC h5; simp only [gw_append] at this; exact this.symm
  · have := gw_eq_of_agreeC h6; simp only [gw_append] at this; exact this.symm
  · have := gw_eq_of_agreeC h7; simp only [gw_append] at this; exact this.symm

end CFSG.AGLEmbedding.Norton.MON11_13
