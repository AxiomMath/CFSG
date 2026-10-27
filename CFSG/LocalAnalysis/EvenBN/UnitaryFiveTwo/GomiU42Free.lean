module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Aut
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Spor
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

@[expose] def GomiU42Free (P : (D : Type) → [Group D] → Prop) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → P D →
    ∀ (α : MulAut D) (S : Subgroup D), ¬ IsU42Root α S

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.isSimpleGroup_J (h : GomiU42Data X J D E a) : IsSimpleGroup J :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h.lieModel

theorem GomiU42Data.card_J (h : GomiU42Data X J D E a) : Nat.card J = 25920 := by
  have := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
    (h.lieModel.statedClassicalModel (by decide))
  rw [this]
  decide

theorem GomiU42Data.nonabelian_J (h : GomiU42Data X J D E a) : ∃ x y : J, x * y ≠ y * x := by
  by_contra hne
  push Not at hne
  haveI := h.isSimpleGroup_J
  letI : CommGroup J := { (inferInstance : Group J) with mul_comm := fun x y => (hne x y) }
  have hp := IsSimpleGroup.prime_card (α := J)
  rw [h.card_J] at hp
  exact absurd hp (by norm_num)

theorem GomiU42Data.isU42Root_conjNormal (h : GomiU42Data X J D E a) :
    haveI := h.normal
    IsU42Root (MulAut.conjNormal a : MulAut D) (J.subgroupOf D) := by
  haveI := h.normal
  obtain ⟨hα, hle, hnorm, -⟩ := h.fixedRoot_conjNormal
  have e := Subgroup.subgroupOfEquivOfLe h.lt.le
  haveI := h.isSimpleGroup_J
  refine ⟨hα, hle, hnorm, e.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := h.nonabelian_J
    refine ⟨e.symm x, e.symm y, fun h' => hxy ?_⟩
    have h'' := congrArg e h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h''
  · rw [Nat.card_congr e.toEquiv]
    exact h.card_J

theorem GomiU42Data.isU42Root (h : GomiU42Data X J D E a) :
    ∃ α : MulAut D, IsU42Root α (J.subgroupOf D) := by
  haveI := h.normal
  exact ⟨_, h.isU42Root_conjNormal⟩

theorem GomiU42Selector.of_free {P : (D : Type) → [Group D] → Prop} (hf : GomiU42Free P) :
    GomiU42Selector P := by
  intro X _ _ J D E a h hP
  obtain ⟨α, hroot⟩ := h.isU42Root
  exact (hf D h.simple hP α _ hroot).elim

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
