module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Bar
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.QzBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableIII_card_Gxy {a z a' : G} (hX : XStruct a z a') :
    Nat.card ↥(Gxy a' z) = 30720 :=
  card_of_isShapeTwoTwoSixS5 hX.shape

theorem tableIII_card_bar_Gxy (hI : TwoHSInterface) [Finite G] {a z a' : G}
    (h : IsF5Type a z) (hX : XStruct a z a') (ha'Q : a' ∈ Qz z) (ha' : IsConj a a') :
    Nat.card ↥(tableIIIBar z (Gxy a' z)) = 120 := by
  obtain ⟨-, ha'1, ha'z, -, -, -, -, -⟩ := tableIII_basic hI h ha'Q ha'
  have hle : Gxy a' z ≤ Gx z := fun g hg => (mem_Gxy.1 hg).2
  have hcard := tableIII_card_eq_card_inf_mul_card_bar hle
  rw [tableIII_card_Gxy hX, Gxy_inf_Qz_eq, tableIII_card_Qz_inf_Gx h ha'Q ha'1 ha'z] at hcard
  norm_num at hcard
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
