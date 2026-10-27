module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section A₂Coord

variable {g g' : hypSU h 2 1}

theorem A₂_rel (hg : g ∈ A₂sub h) :
    mat g ιf₂ ιf₁ = h.bar (mat g ιe₁ ιe₂) ∧ mat g ιz ιf₁ = h.bar (mat g ιe₁ ιz) ∧
      mat g ιe₂ ιf₁ = h.bar (mat g ιe₁ ιf₂) := by
  obtain ⟨hgU, a1, -, a3⟩ := mem_A₂sub.1 hg
  obtain ⟨r1, -, r3, r4, -⟩ := U_rel hgU
  refine ⟨r1, ?_, ?_⟩
  · rw [r3, a1, map_zero, mul_zero, add_zero]
  · rw [r4, a1, a3, mul_zero, mul_zero, add_zero, add_zero]

theorem A₂_mul (hg : g ∈ A₂sub h) (hg' : g' ∈ A₂sub h) :
    mat (g * g') ιe₁ ιe₂ = mat g ιe₁ ιe₂ + mat g' ιe₁ ιe₂ ∧
      mat (g * g') ιe₁ ιz = mat g ιe₁ ιz + mat g' ιe₁ ιz ∧
      mat (g * g') ιe₁ ιf₂ = mat g ιe₁ ιf₂ + mat g' ιe₁ ιf₂ ∧
      mat (g * g') ιe₁ ιf₁ = mat g ιe₁ ιf₁ + mat g' ιe₁ ιf₁ +
        mat g ιe₁ ιe₂ * h.bar (mat g' ιe₁ ιf₂) + mat g ιe₁ ιz * h.bar (mat g' ιe₁ ιz) +
        mat g ιe₁ ιf₂ * h.bar (mat g' ιe₁ ιe₂) := by
  have hgU := A₂sub_le_U hg
  have hgU' := A₂sub_le_U hg'
  obtain ⟨-, b1, b2, b3⟩ := mem_A₂sub.1 hg'
  obtain ⟨c1, c2, c3⟩ := A₂_rel hg'
  refine ⟨mul_e₁e₂ hgU hgU', ?_, ?_, ?_⟩
  · rw [mul_e₁z hgU hgU', b1, mul_zero, add_zero]
  · rw [mul_e₁f₂ hgU hgU', b2, b3, mul_zero, mul_zero, add_zero, add_zero]
  · rw [mul_e₁f₁ hgU hgU', c1, c2, c3]

theorem A₂_inv_mul (hg : g ∈ A₂sub h) (hg' : g' ∈ A₂sub h) :
    mat (g⁻¹ * g') ιe₁ ιe₂ = mat g ιe₁ ιe₂ + mat g' ιe₁ ιe₂ ∧
      mat (g⁻¹ * g') ιe₁ ιz = mat g ιe₁ ιz + mat g' ιe₁ ιz ∧
      mat (g⁻¹ * g') ιe₁ ιf₂ = mat g ιe₁ ιf₂ + mat g' ιe₁ ιf₂ := by
  obtain ⟨m1, m2, m3, -⟩ := A₂_mul (inv_mem hg) hg'
  obtain ⟨c1, c2, c3⟩ := A₂_rel hg
  rw [m1, m2, m3, mat_inv_apply, mat_inv_apply, mat_inv_apply]
  simp only [hypPartner_inl, hypPartner_inr_inl, hypPartner_inr_inr]
  rw [c1, c2, c3, h.bar_bar, h.bar_bar, h.bar_bar]
  exact ⟨rfl, rfl, rfl⟩

theorem mem_Z₂Psub_of_A₂ (hg : g ∈ A₂sub h) (h1 : mat g ιe₁ ιe₂ = 0) (h2 : mat g ιe₁ ιz = 0) :
    g ∈ Z₂Psub h := by
  obtain ⟨hgU, a1, a2, a3⟩ := mem_A₂sub.1 hg
  obtain ⟨c1, c2, -⟩ := A₂_rel hg
  exact mem_Z₂Psub.2 ⟨hgU, h1, by rw [c1, h1, map_zero], h2, by rw [c2, h2, map_zero], a1, a2,
    a3⟩

theorem mem_ZPsub_of_A₂ (hg : g ∈ A₂sub h) (h1 : mat g ιe₁ ιe₂ = 0) (h2 : mat g ιe₁ ιz = 0)
    (h3 : mat g ιe₁ ιf₂ = 0) : g ∈ ZPsub h := by
  obtain ⟨hgU, a1, a2, a3⟩ := mem_A₂sub.1 hg
  obtain ⟨c1, c2, c3⟩ := A₂_rel hg
  exact mem_ZPsub.2 ⟨hgU, h1, by rw [c1, h1, map_zero], h2, by rw [c2, h2, map_zero], a1, a2, h3,
    by rw [c3, h3, map_zero], a3⟩

theorem A₂_mul_comm_iff (hg : g ∈ A₂sub h) (hg' : g' ∈ A₂sub h) :
    g * g' = g' * g ↔ mat g ιe₁ ιe₂ * h.bar (mat g' ιe₁ ιf₂) +
      mat g ιe₁ ιz * h.bar (mat g' ιe₁ ιz) + mat g ιe₁ ιf₂ * h.bar (mat g' ιe₁ ιe₂) =
      mat g' ιe₁ ιe₂ * h.bar (mat g ιe₁ ιf₂) + mat g' ιe₁ ιz * h.bar (mat g ιe₁ ιz) +
        mat g' ιe₁ ιf₂ * h.bar (mat g ιe₁ ιe₂) := by
  have hgU := A₂sub_le_U hg
  have hgU' := A₂sub_le_U hg'
  have he := (commutator_mem_ZPsub_iff hgU hgU').1 (elemAbMod_ZPsub_A₂sub.2 g hg g' hg')
  have e1 := (A₂_mul hg hg').2.2.2
  have e2 := (A₂_mul hg' hg).2.2.2
  constructor
  · intro hc
    rw [hc] at e1
    linear_combination e2 - e1
  · intro h0
    refine eq_of_U_entries (mul_mem hgU hgU') (mul_mem hgU' hgU) fun a b hab => ?_
    by_cases hne : (a, b) = (ιe₁, ιf₁)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hne
      rw [e1, e2]
      linear_combination h0
    · exact he a b hab hne

end A₂Coord

section A₂Lines

theorem exists_A₂sub_coord (h : UnitaryFieldData 2 f K) (a u c : K) :
    ∃ g ∈ A₂sub h, mat g ιe₁ ιe₂ = a ∧ mat g ιe₁ ιz = u ∧ mat g ιe₁ ιf₂ = c := by
  have := h.charP
  obtain ⟨d, hd⟩ := trace_surj (hK := h) (a := u * h.bar u) (by rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨g, hg, e1, e2, e3, -, e5, -, e7⟩ := exists_U_of_coord h a ![u, 0]
    !![d, c; h.bar c, 0] (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [vecMulVec, hd, h.bar_bar, CharTwo.neg_eq, CharTwo.add_self_eq_zero])
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] at e2 e3 e5 e7
  exact ⟨g, mem_A₂sub.2 ⟨hg, e3, by rw [(U_rel hg).2.1, e3, map_zero], e7⟩, e1, e2, e5⟩

variable {b κ : K} (hκ : κ + h.bar κ = b * h.bar b)
include hκ

end A₂Lines

end CFSG.LocalAnalysis.EvenBN.U5
