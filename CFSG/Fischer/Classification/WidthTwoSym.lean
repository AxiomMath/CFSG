module

public import CFSG.GroupTheory.SymmetricWidth

public section

namespace CFSG.Fischer.Classification

open CFSG.OddTranspositions
open CFSG.GroupTheory

theorem isSolvable_perm_three : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  haveI : Group.IsSolvable ↥(alternatingGroup (Fin 3)) :=
    Group.isSolvable_of_comm (by decide)
  exact Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact le_rfl)

theorem widthLe_image_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {D : Set G}
    {n : ℕ} (h : WidthLe D n) : WidthLe (φ '' D) n := by
  intro S hS hcomm
  let S' : Finset G := S.map ⟨φ.symm, φ.symm.injective⟩
  have hS' : (↑S' : Set G) ⊆ D := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hyD : y ∈ φ '' D := hS hy
    obtain ⟨d, hd, hdy⟩ := hyD
    have : φ.symm y = d := by
      rw [← hdy]
      simp
    change (φ.symm y) ∈ D
    rw [this]
    exact hd
  have hcomm' : ∀ x ∈ S', ∀ y ∈ S', x ≠ y → Commute x y := by
    intro x hx y hy hxy
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Finset.mem_map.mp hy
    exact (Commute.map (hcomm x0 hx0 y0 hy0 (fun hh => hxy (by rw [hh]))) φ.symm.toMonoidHom)
  have := h S' hS' hcomm'
  rwa [Finset.card_map] at this

theorem sym_width_two_m_eq_five {G : Type*} [Group G] {D : Set G} {m : ℕ}
    (hm : m = 3 ∨ 5 ≤ m) (φ : G ≃* Equiv.Perm (Fin m))
    (hφ : ∀ g : G, g ∈ D ↔ (φ g).IsSwap) (hW : WidthLe D 2)
    (hns : ¬ Group.IsSolvable G) : m = 5 := by
  have hm2 : 2 ≤ m := by omega
  have himg : φ '' D = transpositionsFin m := by
    ext σ
    constructor
    · rintro ⟨d, hd, rfl⟩
      simpa [transpositionsFin] using (hφ d).1 hd
    · intro hσ
      refine ⟨φ.symm σ, ?_, by simp⟩
      rw [hφ]
      simpa [transpositionsFin] using hσ
  have hW' : WidthLe (transpositionsFin m) 2 := by
    rw [← himg]
    exact widthLe_image_mulEquiv φ hW
  have hm5 : m ≤ 5 := (widthLe_transpositionsFin_iff hm2).1 hW'
  rcases hm with rfl | hm5'
  · exfalso
    haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := isSolvable_perm_three
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := φ.toMonoidHom) φ.injective)
  · omega

end CFSG.Fischer.Classification
