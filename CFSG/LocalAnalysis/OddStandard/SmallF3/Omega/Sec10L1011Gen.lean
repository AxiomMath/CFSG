module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Core

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A : Type} [Group A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

theorem Sec1011Core.eq_of_eq (h : Sec1011Core B t K φ) {α β : MulAut A}
    (hB : ∀ b ∈ B, α b = β b) (ht : α t = β t) : α = β := by
  ext a
  rcases h.split a with ha | ha
  · exact hB a ha
  · have hat : t * (t * a) = a := by rw [← mul_assoc, h.t_sq, one_mul]
    calc α a = α (t * (t * a)) := by rw [hat]
      _ = α t * α (t * a) := map_mul α t (t * a)
      _ = β t * β (t * a) := by rw [ht, hB _ ha]
      _ = β (t * (t * a)) := (map_mul β t (t * a)).symm
      _ = β a := by rw [hat]

theorem Sec1011Core.fixB_of_fixW4 (h : Sec1011Core B t K φ) (α : MulAut A)
    (hα : ∀ i, α (φ (sec1011_wfour i)) = φ (sec1011_wfour i)) : ∀ b ∈ B, α b = b := by
  intro b hb
  obtain ⟨v, hv, rfl⟩ := (h.mem_B b).1 hb
  rcases even_weight_cases_five v hv with h0 | h2 | h4
  · subst h0
    rw [h.map_zero]
    exact map_one α
  · obtain ⟨i, j, -, rfl⟩ := sec1011_exists_wfour_add v h2
    rw [h.hom _ _ (sec1011_wfour_even i) (sec1011_wfour_even j), map_mul, hα i, hα j]
  · obtain ⟨i, rfl⟩ := sec1011_exists_wfour v h4
    exact hα i

theorem Sec1011Core.eq_one_of_fix (h : Sec1011Core B t K φ) {α : MulAut A}
    (hB : ∀ b ∈ B, α b = b) (ht : α t = t) : α = 1 :=
  h.eq_of_eq (fun b hb => by rw [hB b hb]; rfl) (by rw [ht]; rfl)

end CFSG.OddStandard.SmallF3.Omega
