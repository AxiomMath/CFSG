module

public import CFSG.Quasithin.Recognition.G23TypeDefs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Quasithin.G23Type

variable {G : Type} [Group G]

theorem G23One.mul_comm_of_mem_inf {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂)
    {h z : G} (hh : h ∈ H) (hz : z ∈ H₁ ⊓ H₂) : h * z = z * h := by
  have h1 : h ∈ Subgroup.centralizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := by
    rw [← hH.eq_centralizer]; exact hh
  exact (Subgroup.mem_centralizer_iff.mp h1) z hz |>.symm

theorem G23One.inf_le {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) : H₁ ⊓ H₂ ≤ H :=
  inf_le_left.trans hH.le_one

theorem G23One.exists_unique_inf {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) :
    ∃ z : G, z ∈ H₁ ⊓ H₂ ∧ z ≠ 1 ∧ ∀ y ∈ H₁ ⊓ H₂, y = 1 ∨ y = z := by
  obtain ⟨a, ha, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(H₁ ⊓ H₂))).mp hH.card_inf
  refine ⟨a, a.2, fun h => ha (Subtype.ext (by simpa using h)), fun y hy => ?_⟩
  · by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      have h1 := huniq ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
      exact congrArg Subtype.val h1

end CFSG.GH74.QTGen4.Recog.G23
