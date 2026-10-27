module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open Matrix
open scoped MatrixGroups
open CFSG.ClassicalInvolution.Q3.Q3T6

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1000 in
private theorem co_aux : ∀ g h : Matrix (Fin 2) (Fin 2) (ZMod 3),
    (∃ u : ZMod 3, g.det * u = 1) → (∃ u : ZMod 3, h.det * u = 1) →
    (g * g = 1 ∨ g * g = -1) → ¬ (g = 1 ∨ g = -1) →
    (h * g = g * h ∨ h * g = -(g * h)) → (h * h * h = 1 ∨ h * h * h = -1) →
    h = 1 ∨ h = -1 := by
  decide +kernel

private theorem gl_center_iff (g : GL (Fin 2) (ZMod 3)) :
    conjAut g = 1 ↔ g = 1 ∨ g = -1 := by
  rw [← MonoidHom.mem_ker, conjAut3_ker, Aut.mem_center_gl3_iff]

theorem mulAut_eq_one_of_odd_commute_involution (τ α : MulAut SL(2, ZMod 3)) (hτ2 : τ * τ = 1)
    (hτ1 : τ ≠ 1) (hcomm : α * τ = τ * α) (hodd : Odd (orderOf α)) : α = 1 := by
  obtain ⟨g, rfl⟩ := conjAut3_surjective τ
  obtain ⟨h, rfl⟩ := conjAut3_surjective α
  have hg2 : g * g = 1 ∨ g * g = -1 := by
    rw [← gl_center_iff, map_mul]
    exact hτ2
  have hg1 : ¬ (g = 1 ∨ g = -1) := fun hg => hτ1 ((gl_center_iff g).mpr hg)
  have hhg : h * g = g * h ∨ h * g = -(g * h) := by
    have h1 : conjAut (h * g) = conjAut (g * h) := by
      rw [map_mul, map_mul]
      exact hcomm
    have h1' : conjAut ((g * h)⁻¹ * (h * g)) = 1 := by
      rw [map_mul, map_inv, h1]
      exact inv_mul_cancel _
    rcases (gl_center_iff _).mp h1' with h2 | h2
    · left
      calc h * g = (g * h) * ((g * h)⁻¹ * (h * g)) := by group
        _ = g * h := by rw [h2, mul_one]
    · right
      calc h * g = (g * h) * ((g * h)⁻¹ * (h * g)) := by group
        _ = -(g * h) := by rw [h2, mul_neg, mul_one]
  have hh3 : h * h * h = 1 ∨ h * h * h = -1 := by
    have hd : orderOf (conjAut h) ∣ 24 := by
      have := orderOf_dvd_natCard (conjAut h)
      rwa [sl2Three_card_mulAut] at this
    have h3 : orderOf (conjAut h) ∣ 3 := by
      have hodd' := hodd
      have key : ∀ d ∈ Nat.divisors 24, Odd d → d ∣ 3 := by decide
      exact key _ (Nat.mem_divisors.mpr ⟨hd, by norm_num⟩) hodd'
    have h4 : conjAut (h * h * h) = 1 := by
      rw [map_mul, map_mul, ← pow_three']
      exact orderOf_dvd_iff_pow_eq_one.mp h3
    exact (gl_center_iff _).mp h4
  have hgdet : ∃ u : ZMod 3, (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det * u = 1 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).exists_right_inv
  have hhdet : ∃ u : ZMod 3, (h : Matrix (Fin 2) (Fin 2) (ZMod 3)).det * u = 1 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).exists_right_inv
  have hg2' : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g = 1 ∨
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g = -1 := by
    rcases hg2 with h' | h'
    · left; simpa using congrArg Units.val h'
    · right; simpa using congrArg Units.val h'
  have hg1' : ¬ ((g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1) := by
    rintro (h' | h')
    · exact hg1 (Or.inl (Units.ext (by simpa using h')))
    · exact hg1 (Or.inr (Units.ext (by simpa using h')))
  have hhg' : (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g = g * h ∨
      (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g = -(g * h) := by
    rcases hhg with h' | h'
    · left; simpa using congrArg Units.val h'
    · right; simpa using congrArg Units.val h'
  have hh3' : (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * h * h = 1 ∨
      (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * h * h = -1 := by
    rcases hh3 with h' | h'
    · left; simpa using congrArg Units.val h'
    · right; simpa using congrArg Units.val h'
  rcases co_aux _ _ hgdet hhdet hg2' hg1' hhg' hh3' with h' | h'
  · rw [(gl_center_iff h).mpr (Or.inl (Units.ext (by simpa using h')))]
  · rw [(gl_center_iff h).mpr (Or.inr (Units.ext (by simpa using h')))]

end CFSG.ClassicalInvolution.Q3.Q3T6B
