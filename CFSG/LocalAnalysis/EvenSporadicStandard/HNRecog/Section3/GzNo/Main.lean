module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Five
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Partner
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Centralize
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.EndgameA
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Endgame
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_false (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    (hCls : Vert GzClassFacts a z) (x : ↥(Gx z)) (hx2 : (x : G) ^ 2 = 1)
    (hsh : IsShapeTwoTwoTimesA5 ↥(CbarCent z x)) : False := by
  have hxs := gzNo_special hC h hF3 hOrb hCls.self x hx2 hsh
  obtain ⟨-, ρ, hρ5, hρx, hρQ, hρsh⟩ := gzNo_five hC h hOrb.self hCls.self x hx2 hsh
  obtain ⟨y, hy2, hysh, hyx, hyρ, hxyQ⟩ :=
    gzNo_partner h x ρ hx2 hsh hxs.not_mem hρ5 hρx hρQ hρsh
  have hys := gzNo_special hC h hF3 hOrb hCls.self y hy2 hysh
  have hρxG : (ρ : G) * x = x * ρ := congrArg Subtype.val hρx
  have hρ5G : orderOf (ρ : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hρ5
  have hDy : Qz z ⊓ Gx (x : G) ≤ Gx (y : G) :=
    gzNo_centralize h x.2 y.2 ρ.2 hyx hy2 hρxG hyρ.symm hρ5G hρQ hxs.card_cent
      hxs.card_inter hxs.sq_inter
  obtain ⟨z₁, hz₁, hz₁y, hz₁1⟩ := gzNo_exists_z1 hxs hys hDy
  have hz₁Q : z₁ ∈ Qz z := (Subgroup.mem_inf.mp hz₁).1
  have hz₁z : z₁ ∈ Gx z := gzNo_Qz_le z hz₁Q
  have hz₁2 : z₁ ^ 2 = 1 := hxs.sq_inter z₁ hz₁
  have hxz₁ : (x : G) * z₁ = z₁ * x :=
    mem_Gx.mp (gzNo_Qz_le (x : G) (Subgroup.mem_inf.mp hz₁).2)
  have hw2 : ((x * ⟨z₁, hz₁z⟩ : ↥(Gx z)) : G) ^ 2 = 1 := by
    change ((x : G) * z₁) ^ 2 = 1
    calc ((x : G) * z₁) ^ 2 = (x : G) ^ 2 * z₁ ^ 2 := by
          rw [sq, sq, sq, mul_assoc, ← mul_assoc z₁, ← hxz₁, mul_assoc, mul_assoc]
      _ = 1 := by rw [hx2, hz₁2, one_mul]
  have hwsh : IsShapeTwoTwoTimesA5 ↥(CbarCent z (x * ⟨z₁, hz₁z⟩)) := by
    rw [gzNo_cbarCent_mul x ⟨z₁, hz₁z⟩ hz₁Q]
    exact hsh
  have hws := gzNo_special hC h hF3 hOrb hCls.self (x * ⟨z₁, hz₁z⟩) hw2 hwsh
  exact gzNo_endgame hC h hOrb x.2 y.2 hxs hys hws hx2 hy2 hyx hxyQ hDy hz₁ hz₁y hz₁1

theorem gzNo_of_hyps (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    (hCls : Vert GzClassFacts a z) : GzNoFacts a z :=
  ⟨fun ⟨x, hx2, hsh⟩ => gzNo_false hC h hF3 hOrb hCls x hx2 hsh⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
