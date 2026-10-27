module

public import CFSG.GH74.KGroups.M11Tables
public import CFSG.GH74.KGroups.L28Tables
public import CFSG.GH74.KGroups.L33Tables
public import CFSG.GH74.KGroups.U33Tables
public import CFSG.GH74.AS16.E2.Data2

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem outTrivial_M11 : OutTrivial ShapeM11 :=
  fun _ _ _ hK φ => CFSG.GH74.KGroups.M11.out_trivial hK φ

theorem l28Data : L28Data where
  out_inner := fun _ _ _ hK φ n hφ => CFSG.GH74.KGroups.L28.out_inner hK φ n hφ
  sylow_comm := fun _ _ _ hK Q hQ hQi => CFSG.GH74.KGroups.L28.sylow_comm hK Q hQ hQi

theorem smallTable_of_kgroups {K : Type} [Group K] {Q : Subgroup K}
    (h : (∀ x ∈ Q, x ^ 2 = 1 → ∃ k : K, k⁻¹ * x * k ∈ Q ∧
        ∀ y ∈ Q, y * (k⁻¹ * x * k) = (k⁻¹ * x * k) * y) ∧
      (∀ a ∈ Q, (∀ y ∈ Q, y * a = a * y) → a ^ 2 = 1 → a ∈ ⁅Q, Q⁆) ∧
      (∃ s : K, ∀ a ∈ Q, (∀ y ∈ Q, y * a = a * y) → a ^ 2 = 1 → a = 1 ∨ a = s)) :
    SmallTable (⊤ : Subgroup K) Q :=
  ⟨fun x hx hx2 => by
    obtain ⟨k, hk1, hk2⟩ := h.1 x hx hx2
    exact ⟨k, trivial, hk1, hk2⟩, h.2.1, h.2.2⟩

theorem smallData_M11 :
    SmallData ShapeM11 where
  sylow := by
    intro K _ _ hK Q hQ hQi
    obtain ⟨e⟩ := CFSG.GH74.KGroups.M11.equiv_of_sporadic hK
    exact smallTable_of_kgroups (CFSG.GH74.KGroups.M11.smallTable e Q hQ hQi)

theorem smallData_L33 :
    SmallData ShapeL33 where
  sylow := by
    intro K _ _ hK Q hQ hQi
    obtain ⟨e⟩ := CFSG.GH74.KGroups.L33.equiv_of_lieModel hK
    exact smallTable_of_kgroups (CFSG.GH74.KGroups.L33.smallTable e Q hQ hQi)

theorem smallData_U33 :
    SmallData ShapeU33 where
  sylow := by
    intro K _ _ hK Q hQ hQi
    obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hK
    exact smallTable_of_kgroups (CFSG.GH74.KGroups.U33.smallTable e Q hQ hQi)

end CFSG.GH74.AS16.E2
