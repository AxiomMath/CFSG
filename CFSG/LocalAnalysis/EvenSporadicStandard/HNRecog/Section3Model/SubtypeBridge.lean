module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3 Subgroup

theorem map_subtype_inf_Gx {M : Type} [Group M] (P : Subgroup M) (y c : ↥P) :
    (Gx y ⊓ Gx c).map P.subtype =
      P ⊓ centralizer ({(y : M)} : Set M) ⊓ centralizer ({(c : M)} : Set M) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_Gx, Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, ⟨hxy, hxc⟩, rfl⟩
    exact ⟨⟨x.2, by simpa using congrArg Subtype.val hxy⟩, by simpa using congrArg Subtype.val hxc⟩
  · rintro ⟨⟨hgP, hgy⟩, hgc⟩
    exact ⟨⟨g, hgP⟩, ⟨Subtype.ext (by simpa using hgy), Subtype.ext (by simpa using hgc)⟩, rfl⟩

@[expose] noncomputable def infGxSubtypeEquiv {M : Type} [Group M] (P : Subgroup M) (y c : ↥P) :
    ↥(Gx y ⊓ Gx c) ≃* ↥(P ⊓ centralizer ({(y : M)} : Set M) ⊓ centralizer ({(c : M)} : Set M)) :=
  ((Gx y ⊓ Gx c).equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_subtype_inf_Gx P y c))

theorem natCard_inf_Gx_subtype {M : Type} [Group M] (P : Subgroup M) (y c : ↥P) :
    Nat.card ↥(Gx y ⊓ Gx c) =
      Nat.card ↥(P ⊓ centralizer ({(y : M)} : Set M) ⊓ centralizer ({(c : M)} : Set M)) :=
  Nat.card_congr (infGxSubtypeEquiv P y c).toEquiv

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
