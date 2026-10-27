module

public import CFSG.ClassicalInvolution.Q3.Q3VFrameLayer

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Frame

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {m : ℕ} {G : Type} [Group G]

theorem commutes_map_pairEmbed_range {K : Type} [Field K] {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    {Y : Type} [Group Y] (Θ : StatedSp n K →* Y) :
    Commutes ((pairEmbed K hij).range.map Θ) ((pairEmbed K hkl).range.map Θ) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  rw [range_pairEmbed hij] at hx
  rw [range_pairEmbed hkl] at hy
  have hsub : coords k ∪ coords l ⊆ (coords i ∪ coords j)ᶜ := by
    intro t ht hmem
    rcases ht with h | h <;> rcases hmem with h' | h'
    · exact coords_subset_compl hik.symm h h'
    · exact coords_subset_compl hjk.symm h h'
    · exact coords_subset_compl hil.symm h h'
    · exact coords_subset_compl hjl.symm h h'
  rw [(commute_suppGroup_compl hx (suppGroup_mono hsub hy)).eq]

theorem exists_ne_four (hm : 4 ≤ m) (a b c d : Fin (m + 1)) :
    ∃ l, l ≠ a ∧ l ≠ b ∧ l ≠ c ∧ l ≠ d := by
  classical
  have h : ({a, b, c, d} : Finset (Fin (m + 1))).card <
      (Finset.univ : Finset (Fin (m + 1))).card := by
    have : ({a, b, c, d} : Finset (Fin (m + 1))).card ≤ 4 := Finset.card_le_four
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  exact ⟨l, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2⟩

theorem commutes_layerSub_layerSub (hm : 4 ≤ m) {Ω : Set (Subgroup G)}
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {K : Fin (m + 1) → Subgroup G}
    (hK : IsMemberFrame Ω K) {Θ : Fin (m + 1) → (StatedSp m (GaloisField 3 1) →* G)}
    (hΘ : ∀ l, IsLabLift m Ω K l (Θ l)) {a b c d : Fin (m + 1)} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commutes (layerSub Ω K a b) (layerSub Ω K c d) := by
  obtain ⟨l, hla, hlb, hlc, hld⟩ := exists_ne_four hm a b c d
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hla.symm
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hlb.symm
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hlc.symm
  obtain ⟨n, rfl⟩ := Fin.exists_succAbove_eq hld.symm
  have inj : ∀ {x y : Fin m}, l.succAbove x ≠ l.succAbove y → x ≠ y := fun h e => h (by rw [e])
  have hm3 : 3 ≤ m := by omega
  rw [IsLabLift.layerSub_eq hm3 hnonab hK (hΘ l) (inj hab) rfl rfl,
    IsLabLift.layerSub_eq hm3 hnonab hK (hΘ l) (inj hcd) rfl rfl]
  exact commutes_map_pairEmbed_range (inj hab) (inj hcd) (inj hac) (inj had) (inj hbc) (inj hbd)
    (Θ l)

end CFSG.ClassicalInvolution.Q3.Q3V.Frame
