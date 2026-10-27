module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitElem

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SD

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.HSFLit

variable {G : Type*} [Group G]

variable {G : Type*} [Group G]

theorem closure_four_eq (a b c d : G) :
    closure ({a, b, c, d} : Set G) = zpowers a ⊔ zpowers b ⊔ zpowers c ⊔ zpowers d := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_zpowers _)))
    · exact mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_right (mem_zpowers _)
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [zpowers_le] <;>
      exact subset_closure (by simp)

theorem exists_pow_mem_of_mem_sup {P : Subgroup G} {u g : G} (hu : u ^ 2 = 1)
    (hc : P ≤ centralizer ({u} : Set G)) (hg : g ∈ P ⊔ zpowers u) :
    ∃ e : ℕ, e < 2 ∧ g * u ^ e ∈ P := by
  have hN : u ∈ normalizer (P : Set G) := by
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hc ha)
  rcases mem_or_mul_mem_of_mem_sup_zpowers hu hN hg with h | h
  · exact ⟨0, by norm_num, by simpa using h⟩
  · exact ⟨1, by norm_num, by simpa using h⟩

theorem pow_inv_of_sq {u : G} (hu : u ^ 2 = 1) {e : ℕ} (he : e < 2) : (u ^ e)⁻¹ = u ^ e := by
  interval_cases e
  · simp
  · rw [pow_one, inv_eq_iff_mul_eq_one, ← pow_two, hu]

theorem mem_closure_four {a b c d : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hd : d ^ 2 = 1) (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c) {g : G}
    (hg : g ∈ closure ({a, b, c, d} : Set G)) :
    ∃ i j k l : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧ l < 2 ∧ g = a ^ i * b ^ j * c ^ k * d ^ l := by
  rw [closure_four_eq] at hg
  have mc : ∀ {x y : G}, x * y = y * x → x ∈ centralizer ({y} : Set G) := fun h =>
    mem_centralizer_singleton_iff.mpr h
  obtain ⟨l, hl, hgl⟩ := exists_pow_mem_of_mem_sup hd
    (sup_le (sup_le (zpowers_le.mpr (mc had)) (zpowers_le.mpr (mc hbd))) (zpowers_le.mpr (mc hcd)))
    hg
  obtain ⟨k, hk, hgk⟩ := exists_pow_mem_of_mem_sup hc
    (sup_le (zpowers_le.mpr (mc hac)) (zpowers_le.mpr (mc hbc))) hgl
  obtain ⟨j, hj, hgj⟩ := exists_pow_mem_of_mem_sup hb (zpowers_le.mpr (mc hab)) hgk
  have hi : ∃ i : ℕ, i < 2 ∧ g * d ^ l * c ^ k * b ^ j = a ^ i := by
    rcases eq_one_or_eq_of_mem_zpowers ha hgj with h | h
    · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
    · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
  obtain ⟨i, hi, hgi⟩ := hi
  refine ⟨i, j, k, l, hi, hj, hk, hl, ?_⟩
  have hcd' : Commute c d := hcd
  have hbc' : Commute b c := hbc
  have hbd' : Commute b d := hbd
  calc g = g * d ^ l * c ^ k * b ^ j * (b ^ j)⁻¹ * (c ^ k)⁻¹ * (d ^ l)⁻¹ := by group
    _ = a ^ i * b ^ j * c ^ k * d ^ l := by
      rw [hgi, pow_inv_of_sq hb hj, pow_inv_of_sq hc hk, pow_inv_of_sq hd hl]

end CFSG.OddStandard.SmallF3.L33.KD.SD
