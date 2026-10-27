module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT2

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem eq_E_of_elem_le_TE {E : Subgroup X} (hE : ElemAbelianTwo E) (hET : E ≤ S.TE)
    (hcard : Nat.card E = 16) : E = S.E S.y ∨ E = S.E (S.x * S.y) := by
  obtain ⟨a, haE, haB⟩ : ∃ a ∈ E, a ∉ S.B := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show E ≤ S.B from hall)
    rw [hcard, card_B] at this
    omega
  obtain ⟨r, hr, i, j, -, -, hra⟩ := exists_eq_of_mem_TE S (hET haE)
  have hβ : t ^ i * S.k ^ j ∈ S.B := mul_mem (pow_mem Frame.t_mem_B i) (pow_mem Frame.k_mem_B j)
  have hra' : a = r * (t ^ i * S.k ^ j) := by rw [hra]; group
  have hr1 : r ≠ 1 := fun h => haB (by rw [hra', h, one_mul]; exact hβ)
  have hrz : r ≠ S.z := fun h => haB (by rw [hra', h]; exact mul_mem Frame.z_mem_B hβ)
  have hr2 : r ^ 2 = 1 := by
    have ha2 := hE.sq_eq_one a haE
    have hcomm : (t ^ i * S.k ^ j) * r = r * (t ^ i * S.k ^ j) := B_comm_R S hβ hr
    rw [hra', pow_two, show r * (t ^ i * S.k ^ j) * (r * (t ^ i * S.k ^ j)) =
      r * r * ((t ^ i * S.k ^ j) * (t ^ i * S.k ^ j)) by
        rw [mul_assoc r, ← mul_assoc (t ^ i * S.k ^ j) r, hcomm]; group,
      ← pow_two (t ^ i * S.k ^ j), sq_of_mem_B S hβ, mul_one] at ha2
    rw [pow_two]; exact ha2
  have hrefl := isRefl_of_sq S hr hr2 hr1 hrz
  have hle : E ≤ S.E r := by
    intro g hg
    refine mem_E_of_comm S hrefl (hET hg) ?_
    have h1 : g * a = a * g := hE.comm g hg a haE
    rw [hra'] at h1
    have h2 : (t ^ i * S.k ^ j) * g = g * (t ^ i * S.k ^ j) := central_of_mem_B S hβ (hET hg)
    have h3 : g * r * (t ^ i * S.k ^ j) = r * g * (t ^ i * S.k ^ j) := by
      calc g * r * (t ^ i * S.k ^ j) = g * (r * (t ^ i * S.k ^ j)) := by group
        _ = r * (t ^ i * S.k ^ j) * g := h1
        _ = r * ((t ^ i * S.k ^ j) * g) := by group
        _ = r * g * (t ^ i * S.k ^ j) := by rw [h2]; group
    exact mul_right_cancel h3
  have heq : E = S.E r := Subgroup.eq_of_le_of_card_ge hle (by rw [card_E S hrefl, hcard])
  rw [heq]
  exact E_refl S hrefl

theorem elemAbelianTwo_E {r : X} (h : IsRefl S r) : ElemAbelianTwo (S.E r) :=
  (frameOf h (Or.inl rfl)).elemAbelianTwo_E

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
