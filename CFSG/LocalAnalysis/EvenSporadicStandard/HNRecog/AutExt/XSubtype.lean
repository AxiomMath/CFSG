module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XBase

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G]

theorem exists_mulEquiv_Gx_Gxy {p q : G} (x : ↥(Gx p)) (hx : (x : G) = q) :
    ∃ e : ↥(Gx x) ≃* ↥(Gxy p q),
      ∀ y : ↥(Gx x), ((e y : ↥(Gxy p q)) : G) = ((y : ↥(Gx p)) : G) :=
  ⟨(Subgroup.equivMapOfInjective (Gx x) (Gx p).subtype (Subgroup.subtype_injective (Gx p))).trans
    (MulEquiv.subgroupCongr (Gxy_eq_map_of_eq hx).symm), fun _ => rfl⟩

theorem natCard_centralizer_eq_Gxy_inf {p q : G} (x : ↥(Gx p)) (hx : (x : G) = q)
    (T : ↥(Gx x)) :
    Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(Gx x))) =
      Nat.card ↥(Gxy p q ⊓ Gx (((T : ↥(Gx p)) : G))) := by
  have h1 : Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(Gx x))) =
      Nat.card ↥(Gx x ⊓ Gx (T : ↥(Gx p))) :=
    Nat.card_congr
      { toFun := fun y => ⟨(y.1 : ↥(Gx p)), y.1.2,
          mem_Gx.2 (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2)).symm⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩,
          Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (mem_Gx.1 w.2.2).symm)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : Gxy p q ⊓ Gx (((T : ↥(Gx p)) : G)) =
      (Gx x ⊓ Gx (T : ↥(Gx p))).map (Gx p).subtype := by
    rw [← Gxyz_eq_inf]
    exact Gxyz_eq_map_of_eq hx (T : ↥(Gx p))
  rw [h1, h2]
  exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective (Gx p))).symm

end CFSG.EvenSporadicStandard.HNRecog.Section4
