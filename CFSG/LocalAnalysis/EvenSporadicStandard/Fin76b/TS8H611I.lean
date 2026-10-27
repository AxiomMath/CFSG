module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611E

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem theta_mul {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {w w' : G}
    (hw : w ∈ Wsub h hα (zpowers α))
    (hw' : w' ∈ Wsub h hα (zpowers α)) :
    (w * w') * (z * (w * w') * z⁻¹) = (w * (z * w * z⁻¹)) * (w' * (z * w' * z⁻¹)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, -, -, -, -, -, -⟩ :=
    h.lemma611Cl_of_pairing hα hF hM hp
  have hc : w' * (z * w * z⁻¹) = (z * w * z⁻¹) * w' := hcomm w' hw' _ (h.conj_z_W1 hα hw)
  calc (w * w') * (z * (w * w') * z⁻¹) = w * (w' * (z * w * z⁻¹)) * (z * w' * z⁻¹) := by group
    _ = w * ((z * w * z⁻¹) * w') * (z * w' * z⁻¹) := by rw [hc]
    _ = (w * (z * w * z⁻¹)) * (w' * (z * w' * z⁻¹)) := by group

theorem theta_inv {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {w : G}
    (hw : w ∈ Wsub h hα (zpowers α)) :
    w⁻¹ * (z * w⁻¹ * z⁻¹) = (w * (z * w * z⁻¹))⁻¹ := by
  have h1 := h.theta_mul hα hF hM hp hw (inv_mem hw)
  have h2 : (w * w⁻¹) * (z * (w * w⁻¹) * z⁻¹) = 1 := by group
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem theta_eq_one_iff {α : G} (hα : AlphaSpec S z t α) {w : G}
    (hw : w ∈ Wsub h hα (zpowers α)) : w * (z * w * z⁻¹) = 1 ↔ w = 1 ∨ w = t := by
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hw2 : z * w * z⁻¹ ∈ Wsub h hα (zpowers (α * t)) := h.conj_z_W1 hα hw
    have hinv : z * w * z⁻¹ = w⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hwW2 : w ∈ Wsub h hα (zpowers (α * t)) := by
      have h3 : w⁻¹ ∈ Wsub h hα (zpowers (α * t)) := by rw [← hinv]; exact hw2
      simpa using inv_mem h3
    have hZ := h.W1_inf_W2 hα hw hwW2
    have hsq := h.Zg_sq hα hZ
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hsq
    rcases (h.mem_Zg hα).1 hZ with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exfalso
      have h3 : z * w * z⁻¹ = w := by rw [hinv, hwi]
      rw [e, h.z_conj_alpha hα] at h3
      exact h.t_ne (by simpa using h3)
    · exfalso
      have h3 : z * w * z⁻¹ = w := by rw [hinv, hwi]
      have hzαt : z * (α * t) * z⁻¹ = α := by
        calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
          _ = α * t * t := by rw [h.z_conj_alpha hα, h.z_conj_t]
          _ = α := by rw [mul_assoc, h.t_sq, mul_one]
      rw [e, hzαt] at h3
      exact h.t_ne (by simpa using h3.symm)
  · rcases h1 with rfl | rfl
    · group
    · rw [h.z_conj_t, h.t_sq]

theorem theta_eq_iff {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {w w' : G}
    (hw : w ∈ Wsub h hα (zpowers α))
    (hw' : w' ∈ Wsub h hα (zpowers α)) :
    w * (z * w * z⁻¹) = w' * (z * w' * z⁻¹) ↔ w' = w ∨ w' = w * t := by
  have hm := h.theta_mul hα hF hM hp (inv_mem hw) hw'
  have hi := h.theta_inv hα hF hM hp hw
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have h2 : (w⁻¹ * w') * (z * (w⁻¹ * w') * z⁻¹) = 1 := by
      rw [hm, hi, h1]; group
    rcases (h.theta_eq_one_iff hα (mul_mem (inv_mem hw) hw')).1 h2 with e | e
    · left; rw [← mul_inv_cancel_left w w', e]; group
    · right; rw [← mul_inv_cancel_left w w', e]
  · rcases h1 with rfl | rfl
    · rfl
    · have h2 := h.theta_mul hα hF hM hp hw (h.Zg_mem_Wsub hα _ (h.t_mem_Zg hα))
      rw [h2, h.z_conj_t, h.t_sq, mul_one]

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
