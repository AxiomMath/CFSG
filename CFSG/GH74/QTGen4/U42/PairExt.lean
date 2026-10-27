module

public import CFSG.GH74.QTGen4.U42.CentralExt

public section

namespace CFSG.GH74.QTGen4.U42

structure PairCore {G : Type*} [Group G] (H B T U : Subgroup G) : Prop where
  U_le_T : U ≤ T
  T_le_B : T ≤ B
  B_le_H : B ≤ H
  U_normal : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U
  T_two : IsPGroup 2 T
  T_odd_index : ¬ 2 ∣ (T.subgroupOf H).index
  centralizes : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h ∈ U
  card_eq : Nat.card H = 9 * Nat.card T

@[expose] def restrictEquiv {G G' : Type*} [Group G] [Group G'] (S : Subgroup G) (S' : Subgroup G')
    (f : G ≃* G') (hS : ∀ x : G, x ∈ S ↔ f x ∈ S') : ↥S ≃* ↥S' where
  toFun x := ⟨f x, (hS x).mp x.2⟩
  invFun y := ⟨f.symm y, (hS (f.symm y)).mpr (by simp)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
theorem restrictEquiv_apply {G G' : Type*} [Group G] [Group G'] (S : Subgroup G)
    (S' : Subgroup G') (f : G ≃* G') (hS : ∀ x : G, x ∈ S ↔ f x ∈ S') (x : ↥S) :
    ((restrictEquiv S S' f hS x : ↥S') : G') = f (x : G) :=
  rfl

end CFSG.GH74.QTGen4.U42

end
