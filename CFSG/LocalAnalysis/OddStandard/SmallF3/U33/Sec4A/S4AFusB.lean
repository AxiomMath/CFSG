module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AFusA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZStar

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem exists_outer_involution_conj_t (hG : IsSimpleGroup G) (h4 : 4 ∣ Nat.card G)
    (h : Ctx t L S x₁ x₂ lam rho tau) (hS : ¬ 2 ∣ S.index) :
    ∃ p ∈ twoCore t, ∃ g : G, (p * tau) * (p * tau) = 1 ∧ g * (p * tau) * g⁻¹ = t := by
  obtain ⟨S', hS'⟩ := exists_sylow_coe_eq h.isPGroup hS
  have htS : t ∈ S := by
    rw [h.S_eq]
    exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  have hcommS : ∀ s ∈ S, s * t = t * s :=
    fun s hs => mem_invCent_iff.mp (h.le_invCent hs)
  obtain ⟨g₀, hg₀S, hg₀ne⟩ :=
    exists_conj_mem_sylow_ne_of_isSimpleGroup hG h4 S'
      (by rw [hS']; exact htS) h.hyp.ord_t
      (by intro s hs; rw [hS'] at hs; exact hcommS s hs)
  set u : G := g₀⁻¹ * t * g₀ with hu_def
  have huS : u ∈ S := by rw [hu_def, ← hS']; exact hg₀S
  have hu_ne_t : u ≠ t := by rw [hu_def]; exact hg₀ne
  have hu2 : u * u = 1 := by
    rw [hu_def]
    calc (g₀⁻¹ * t * g₀) * (g₀⁻¹ * t * g₀)
        = g₀⁻¹ * (t * t) * g₀ := by group
      _ = 1 := by rw [t_mul_self h.hyp]; group
  have hu_ne_one : u ≠ 1 := by
    intro hu1
    refine t_ne_one h.hyp ?_
    rw [hu_def] at hu1
    calc t = g₀ * (g₀⁻¹ * t * g₀) * g₀⁻¹ := by group
      _ = g₀ * 1 * g₀⁻¹ := by rw [hu1]
      _ = 1 := by group
  have hu_invCent : u ∈ invCent t := h.le_invCent huS
  have hu_not_PL : u ∉ twoCore t ⊔ L := by
    intro huPL
    obtain ⟨h', hh', hcases⟩ := h.invol_PL u huPL hu2 hu_ne_one
    have key : h' * u * h'⁻¹ = (h' * g₀⁻¹) * t * (h' * g₀⁻¹)⁻¹ := by
      rw [hu_def]; group
    rcases hcases with heq | heq | heq
    ·
      have hht : h' * t = t * h' := mem_invCent_iff.mp hh'
      have hconj : h'⁻¹ * t * h' = t := by
        rw [mul_assoc, hht.symm, ← mul_assoc, inv_mul_cancel, one_mul]
      have h1 : u = h'⁻¹ * (h' * u * h'⁻¹) * h' := by group
      exact hu_ne_t (by rw [h1, heq, hconj])
    · exact not_conj_t_z h hS (h' * g₀⁻¹) (by rw [← key, heq])
    · exact not_conj_t_tz h hS (h' * g₀⁻¹) (by rw [← key, heq])
  have hu_sq : u ^ 2 ∈ twoCore t := by
    rw [pow_two, hu2]
    exact Subgroup.one_mem _
  obtain ⟨h₁, _hh₁, p, hp, hpt⟩ := h.invol_outer u hu_invCent hu_not_PL hu_sq
  refine ⟨p, hp, g₀ * h₁⁻¹, ?_, ?_⟩
  · rw [← hpt]
    calc (h₁ * u * h₁⁻¹) * (h₁ * u * h₁⁻¹)
        = h₁ * (u * u) * h₁⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  · rw [← hpt, hu_def]
    group

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
