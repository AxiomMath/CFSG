module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.GoldschmidtM22EndN4b

public section
namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

omit [CFSG.GH74.QTGen4.Finite4 G] in
theorem mem_sup_zpowers_iff_F4 {L : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (ha2 : a * a = 1) {x : G} : x ∈ L ⊔ Subgroup.zpowers a ↔ x ∈ L ∨ ∃ l ∈ L, x = l * a := by
  constructor
  · intro hx
    obtain ⟨l, hl, b, hb, rfl⟩ := exists_mul_of_mem_sup (Subgroup.zpowers_le.mpr ha) hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      have : a ^ (2 * n) = 1 := by
        rw [zpow_mul, show a ^ (2 : ℤ) = 1 by rw [zpow_two]; exact ha2, one_zpow]
      rw [this, mul_one]
      exact hl
    · right
      have : a ^ (2 * n + 1) = a := by
        rw [zpow_add, zpow_mul, show a ^ (2 : ℤ) = 1 by rw [zpow_two]; exact ha2, one_zpow,
          one_mul, zpow_one]
      exact ⟨l, hl, by rw [this]⟩
  · rintro (hx | ⟨l, hl, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · exact (L ⊔ Subgroup.zpowers a).mul_mem (Subgroup.mem_sup_left hl)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))

end CFSG.Quasithin.H13.GM22
