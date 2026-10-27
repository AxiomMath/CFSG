module

public import Certificates.Certificate22230
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ComponentClassification.GSThmB.U52

open Subgroup

theorem card_centralizer_congr {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X) :
    Nat.card (centralizer ({x} : Set X)) = Nat.card (centralizer ({φ x} : Set Y)) := by
  refine Nat.card_congr (φ.toEquiv.subtypeEquiv fun y => ?_)
  simp only [mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, φ.injective.eq_iff]

theorem card_centralizer_subtype {M : Type*} [Group M] (H : Subgroup M) (a : H) :
    Nat.card (centralizer ({a} : Set H)) = Nat.card ↥(H ⊓ centralizer ({(a : M)} : Set M)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨g.1, g.1.2, mem_centralizer_singleton_iff.mpr ?_⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  · exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp g.2)
  · exact mem_centralizer_singleton_iff.mp g.2.2

theorem card_centralizer_of_orderOf_eq_two
    {x : X₀} (hx : orderOf x = 2) :
    Nat.card (Subgroup.centralizer ({x} : Set X₀)) = 82944 ∨
      Nat.card (Subgroup.centralizer ({x} : Set X₀)) = 4608 :=
  Certificates.certificate22230 x hx

end CFSG.ComponentClassification.GSThmB.U52
