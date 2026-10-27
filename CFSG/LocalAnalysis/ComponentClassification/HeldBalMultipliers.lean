module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalCentre
import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem centreTwoPartLe_he (h : TBLit.HeldTrivialMultiplier) :
    CentreTwoPartLe Blueprint.NativeSporadic.He 1 := by
  intro L _ _ hq e S
  have hZ : Subgroup.center L = ⊥ := h L hq e
  have h1 : Nat.card (Subgroup.center L) = 1 := by
    rw [hZ]
    exact Subgroup.card_bot
  exact (Subgroup.card_le_card_group S).trans h1.le

theorem centreTwoPartLe_psl_three_sixteen (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type}
    [Group X] (hX : Blueprint.LieModel X .PSL 3 2 4) : CentreTwoPartLe X 1 := by
  intro L _ _ hq ⟨e⟩ S
  have : Group.IsPerfect L := hq.1
  have hmodel : Blueprint.LieModel (L ⧸ Subgroup.center L) .PSL 3 2 4 :=
    LieType.CurtisTits.lieModel_of_mulEquiv e.symm hX
  have hcl := CatLeaf.statedClassicalModel_of_lieModel_psl hmodel
  have hm : Models.LieModel (L ⧸ Subgroup.center L) .PSL 3 2 4 := ⟨hcl.1, .inl hcl⟩
  obtain ⟨-, ⟨e'⟩⟩ := hGA _ .PSL 3 2 4 hm
  have h1 := ComponentClassification.FooteLit.card_center_dvd_card_hopfMultiplier (Q := L)
    (MulEquiv.refl (L ⧸ Subgroup.center L))
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
    Nat.card_congr e'.toEquiv] at h1
  have hcard : Nat.card (Blueprint.Multiplier.generic .PSL 3 2 4 ×
      Blueprint.Multiplier.exceptional .PSL 3 2 4) = 3 := by
    simp only [Blueprint.Multiplier.generic, Blueprint.Multiplier.exceptional, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _), Nat.card_zmod]
    simp [Blueprint.Multiplier.genericOrders, Blueprint.Multiplier.exceptionalOrders]
  rw [hcard] at h1
  have hS : Nat.card S ∣ 3 := (Subgroup.card_subgroup_dvd_card S).trans h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (S.isPGroup' : IsPGroup 2 S)
  rw [hk] at hS ⊢
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
    have := h2.trans hS
    omega
  subst hk0
  simp

end CFSG.ComponentClassification.GrSLit
