module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.SectionRank

variable {G : Type} [Group G]

theorem IsStronglyQuasithin.subgroup [Finite G] (hG : IsStronglyQuasithin G) (H : Subgroup G) :
    IsStronglyQuasithin H := by
  rw [isStronglyQuasithin_iff] at hG ⊢
  intro q hq hq2
  exact (pRank_top_le_of_injective hq.one_lt H.subtype H.subtype_injective).trans (hG q hq hq2)

theorem isStronglyQuasithin_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) (h : IsStronglyQuasithin H) : IsStronglyQuasithin G := by
  have : Finite H := Finite.of_equiv _ e.toEquiv
  rw [isStronglyQuasithin_iff] at h ⊢
  intro q hq hq2
  rw [pRank_top_eq_of_mulEquiv hq.one_lt e]
  exact h q hq hq2

theorem IsSQTKCat.subgroup [Finite G] (hG : IsSQTKCat G) (H : Subgroup G) : IsSQTKCat H :=
  ⟨IsStronglyQuasithin.subgroup hG.1 H, IsKGroupCat.subgroup hG.2 H⟩

theorem IsSQTKCat.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] (hY : IsSQTKCat Y)
    (e : X ≃* Y) : IsSQTKCat X :=
  ⟨isStronglyQuasithin_of_mulEquiv e hY.1, hY.2.of_mulEquiv e⟩

theorem IsSQTKCat.of_le [Finite G] {H L : Subgroup G} (hLH : L ≤ H) (hH : IsSQTKCat H) :
    IsSQTKCat L :=
  (hH.subgroup (L.subgroupOf H)).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH).symm

end CFSG.SectionRank
