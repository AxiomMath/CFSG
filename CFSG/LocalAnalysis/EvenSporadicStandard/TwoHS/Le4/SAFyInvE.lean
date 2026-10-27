module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarInvol
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyAtlas

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Invol


theorem hsInvolutionClasses : HSInvolutionClasses := by
  intro E _ _ hperf hZ hq z hz hz1 a b ha hb hanc hbnc
  obtain ⟨M⟩ := exists_coverModel hperf hZ hq
  have htz : M.tE = z := by
    rcases (M.mem_center_iff hZ).1 hz with h | h
    · exact absurd h hz1
    · exact h.symm
  have htc : ∀ y : E, M.tE * y = y * M.tE := fun y =>
    ((Subgroup.mem_center_iff.1 M.tE_mem_center) y).symm
  have htt : M.tE * M.tE = 1 := by rw [← pow_two]; exact M.tE_sq
  have hcl : ∀ u : E, u * u = 1 → u ∉ center E →
      ∃ e : E, e * u * e⁻¹ = M.z1E ∨ e * u * e⁻¹ = M.tE * M.z1E := by
    intro u hu hunc
    refine M.exists_conj_of_involution hZ (by rw [pow_two]; exact hu) ?_ ?_
    · rintro rfl
      exact hunc (one_mem _)
    · rintro rfl
      exact hunc M.tE_mem_center
  obtain ⟨e₁, h₁⟩ := hcl a ha hanc
  obtain ⟨e₂, h₂⟩ := hcl b hb hbnc
  have hmv : ∀ x y : E, x * (M.tE * y) = M.tE * (x * y) := by
    intro x y
    rw [← mul_assoc, ← htc x, mul_assoc]
  have key : e₁ * a * e₁⁻¹ = e₂ * b * e₂⁻¹ ∨ e₁ * a * e₁⁻¹ = M.tE * (e₂ * b * e₂⁻¹) := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂]
    · exact Or.inl rfl
    · exact Or.inr (by rw [← mul_assoc, htt, one_mul])
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hg : (e₂⁻¹ * e₁) * a * (e₂⁻¹ * e₁)⁻¹ = e₂⁻¹ * (e₁ * a * e₁⁻¹) * e₂ := by group
  refine ⟨e₂⁻¹ * e₁, ?_⟩
  rw [hg]
  rcases key with h | h
  · left
    rw [h]
    group
  · right
    rw [h, ← htz]
    calc e₂⁻¹ * (M.tE * (e₂ * b * e₂⁻¹)) * e₂ = M.tE * (e₂⁻¹ * (e₂ * b * e₂⁻¹)) * e₂ := by
          rw [hmv]
      _ = M.tE * b := by group
      _ = b * M.tE := htc b

end Invol

end CFSG.EvenSporadicStandard.TwoHS
