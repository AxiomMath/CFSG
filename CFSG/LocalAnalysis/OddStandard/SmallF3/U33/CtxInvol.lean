module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G]

theorem exists_conj_of_involution_sup {t z : G} {P L : Subgroup G}
    (hI : ∀ g ∈ L, g * g = 1 → g ≠ 1 → ∃ c ∈ L, c * z * c⁻¹ = g)
    (hPL : P ⊓ L = ⊥) (hcomm : ∀ a ∈ P, ∀ b ∈ L, a * b = b * a)
    (hP2 : ∀ x ∈ P, x ^ 2 = 1 → x = 1 ∨ x = t) (htP : t ∈ P)
    (hLt : ∀ b ∈ L, t * b = b * t) {g : G} (hg : g ∈ P ⊔ L) (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    ∃ h ∈ invCent t, h * g * h⁻¹ = t ∨ h * g * h⁻¹ = z ∨ h * g * h⁻¹ = t * z := by
  obtain ⟨a, ha, l, hl, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hg
  have hcomm_al : a * l = l * a := hcomm a ha l hl
  have hsq : (a * a) * (l * l) = 1 := by
    have h1 : (a * l) * (a * l) = (a * a) * (l * l) := by
      calc (a * l) * (a * l) = a * (l * a) * l := by group
        _ = a * (a * l) * l := by rw [hcomm_al]
        _ = (a * a) * (l * l) := by group
    rw [← h1]
    exact hg2
  have ha2L : a * a ∈ L := by
    have ha2_eq : a * a = (l * l)⁻¹ := by rw [eq_inv_of_mul_eq_one_right hsq, inv_inv]
    rw [ha2_eq]
    exact inv_mem (mul_mem hl hl)
  have ha2 : a * a = 1 := by
    have hmem : a * a ∈ (⊥ : Subgroup G) := by
      rw [← hPL]
      exact Subgroup.mem_inf.mpr ⟨mul_mem ha ha, ha2L⟩
    exact Subgroup.mem_bot.mp hmem
  have hl2 : l * l = 1 := by
    have h := hsq
    rw [ha2, one_mul] at h
    exact h
  have ha_cases : a = 1 ∨ a = t := hP2 a ha (by rw [pow_two]; exact ha2)
  have hL_invCent : L ≤ invCent t := fun b hb => by
    rw [invCent, Subgroup.mem_centralizer_singleton_iff]
    exact (hLt b hb).symm
  by_cases hl1 : l = 1
  · have hg1' : a ≠ 1 := by
      intro ha1
      exact hg1 (by rw [ha1, hl1, mul_one])
    rcases ha_cases with ha1 | hat
    · exact absurd ha1 hg1'
    · refine ⟨1, (invCent t).one_mem, Or.inl ?_⟩
      have hg_eq : a * l = t := by rw [hl1, mul_one, hat]
      rw [hg_eq]
      group
  · obtain ⟨c, hc, hcz⟩ := hI l hl hl2 hl1
    have hc_inv : c⁻¹ ∈ invCent t := inv_mem (hL_invCent hc)
    have hcomm_ac : a * c = c * a := hcomm a ha c hc
    have h_a : c⁻¹ * a * c = a := by
      calc c⁻¹ * a * c = c⁻¹ * (a * c) := by group
        _ = c⁻¹ * (c * a) := by rw [hcomm_ac]
        _ = a := by group
    have h_l : c⁻¹ * l * c = z := by
      rw [← hcz]
      group
    have h_g : c⁻¹ * (a * l) * c = a * z := by
      calc c⁻¹ * (a * l) * c = (c⁻¹ * a * c) * (c⁻¹ * l * c) := by group
        _ = a * z := by rw [h_a, h_l]
    rcases ha_cases with ha1 | hat
    · refine ⟨c⁻¹, hc_inv, Or.inr (Or.inl ?_)⟩
      simpa [inv_inv, ha1] using h_g
    · refine ⟨c⁻¹, hc_inv, Or.inr (Or.inr ?_)⟩
      simpa [inv_inv, hat] using h_g

theorem involution_reps_distinct {t z : G} {P L : Subgroup G} (hPL : P ⊓ L = ⊥) (htP : t ∈ P)
    (ht1 : t ≠ 1) (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hLnorm : ∀ h ∈ invCent t, ∀ b ∈ L, h * b * h⁻¹ ∈ L) :
    (∀ h ∈ invCent t, h * t * h⁻¹ ≠ z) ∧ (∀ h ∈ invCent t, h * t * h⁻¹ ≠ t * z) ∧
      (∀ h ∈ invCent t, h * z * h⁻¹ ≠ t * z) := by
  have ht_ne_z : t ≠ z := by
    intro htz
    have htL : t ∈ L := by rw [htz]; exact hzL
    have hmem : t ∈ (⊥ : Subgroup G) := by
      rw [← hPL]
      exact Subgroup.mem_inf.mpr ⟨htP, htL⟩
    exact ht1 (Subgroup.mem_bot.mp hmem)
  have hconj_t : ∀ h ∈ invCent t, h * t * h⁻¹ = t := by
    intro h hh
    have hht : h * t = t * h := by
      rwa [invCent, Subgroup.mem_centralizer_singleton_iff] at hh
    rw [hht]
    group
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    rw [hconj_t h hh]
    exact ht_ne_z
  · intro h hh
    rw [hconj_t h hh]
    intro htz
    have h1z : (1 : G) = z := mul_left_cancel (a := t) (by rw [mul_one]; exact htz)
    exact hz1 h1z.symm
  · intro h hh hconj
    have hz_norm : h * z * h⁻¹ ∈ L := hLnorm h hh z hzL
    have htz : (h * z * h⁻¹) * z⁻¹ = t := by
      rw [hconj]
      group
    have htL : t ∈ L := by
      rw [← htz]
      exact mul_mem hz_norm (inv_mem hzL)
    have hmem : t ∈ (⊥ : Subgroup G) := by
      rw [← hPL]
      exact Subgroup.mem_inf.mpr ⟨htP, htL⟩
    exact ht1 (Subgroup.mem_bot.mp hmem)

end CFSG.OddStandard.SmallF3.HarrisU33
