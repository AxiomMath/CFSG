module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem exists_conj_of_involution_conj_z (h : Ctx0 t L S x₁ x₂ lam rho)
    (htz : ∀ g : G, g * t * g⁻¹ ≠ (x₁ * x₂) ^ 2)
    (hztz : ∀ g : G, g * (x₁ * x₂) ^ 2 * g⁻¹ ≠ t * (x₁ * x₂) ^ 2)
    {f : G} (hf : f ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam) (hf2 : f * f = 1) {g : G}
    (hg : g * (x₁ * x₂) ^ 2 * g⁻¹ = f) : ∃ c ∈ L, c * (x₁ * x₂) ^ 2 * c⁻¹ = f := by
  have hzne : (x₁ * x₂) ^ 2 ≠ 1 := (z_mul_self_ne_one h).2
  have hWL : wreathGrp x₁ x₂ lam ≤ L := by
    rw [← h.inf_eq]
    exact inf_le_right
  have hcomm : ∀ a ∈ twoCore t, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a :=
    fun a ha b hb => twoCore_commute h.hyp a ha b (hWL hb)
  obtain ⟨p, hp, x, hx, hfx⟩ := (mem_sup_iff_of_commute hcomm).mp hf
  have hxL : x ∈ L := hWL hx
  have hxp : x * p = p * x := (hcomm p hp x hx).symm
  rw [hfx] at hf2
  have hrew : (p * x) * (p * x) = (p * p) * (x * x) := by
    calc (p * x) * (p * x)
        = p * (x * (p * x)) := by rw [mul_assoc]
      _ = p * ((x * p) * x) := by rw [← mul_assoc x p x]
      _ = p * ((p * x) * x) := by rw [hxp]
      _ = p * (p * (x * x)) := by rw [mul_assoc p x x]
      _ = (p * p) * (x * x) := by rw [← mul_assoc p p (x * x)]
  have hppxx : (p * p) * (x * x) = 1 := by rw [← hrew]; exact hf2
  have hpp_eq : p * p = (x * x)⁻¹ := eq_inv_of_mul_eq_one_left hppxx
  have hpp_mem_L : p * p ∈ L := by
    rw [hpp_eq]
    exact Subgroup.inv_mem L (Subgroup.mul_mem L hxL hxL)
  have hpp1 : p * p = 1 := by
    have hmem : p * p ∈ twoCore t ⊓ L := ⟨Subgroup.mul_mem _ hp hp, hpp_mem_L⟩
    rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at hmem
    exact hmem
  have hxx1 : x * x = 1 := by
    rw [hpp1, one_mul] at hppxx
    exact hppxx
  have hpcases : p = 1 ∨ p = t := h.hyp.eq_one_or_eq p hp (by rwa [pow_two])
  have hfne : f ≠ 1 := by
    intro hf1
    apply hzne
    have h' : g * (x₁ * x₂) ^ 2 * g⁻¹ = 1 := by rw [hg, hf1]
    calc (x₁ * x₂) ^ 2 = g⁻¹ * (g * (x₁ * x₂) ^ 2 * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h']
      _ = 1 := by group
  rcases hpcases with hp1 | hpt
  ·
    have hxne : x ≠ 1 := by
      intro hx1
      exact hfne (by rw [hfx, hp1, hx1, mul_one])
    obtain ⟨c, hcL, hcz⟩ := h.invol_L x hxL hxx1 hxne
    exact ⟨c, hcL, by rw [hcz, hfx, hp1, one_mul]⟩
  · by_cases hx1 : x = 1
    ·
      exfalso
      apply htz g⁻¹
      have hgt : g * (x₁ * x₂) ^ 2 * g⁻¹ = t := by rw [hg, hfx, hpt, hx1, mul_one]
      rw [← hgt]
      group
    ·
      obtain ⟨c, hcL, hcz⟩ := h.invol_L x hxL hxx1 hx1
      exfalso
      apply hztz (c⁻¹ * g)
      have htc : t * c = c * t := (mem_invCent_iff.mp (L_le_invCent h.hyp hcL)).symm
      have hconj_t : c⁻¹ * t * c = t := by
        rw [mul_assoc, htc, ← mul_assoc, inv_mul_cancel, one_mul]
      have hg' : g * (x₁ * x₂) ^ 2 * g⁻¹ = t * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by
        rw [hg, hfx, hpt, ← hcz]
      calc (c⁻¹ * g) * (x₁ * x₂) ^ 2 * (c⁻¹ * g)⁻¹
          = c⁻¹ * (g * (x₁ * x₂) ^ 2 * g⁻¹) * c := by group
        _ = c⁻¹ * (t * (c * (x₁ * x₂) ^ 2 * c⁻¹)) * c := by rw [hg']
        _ = t * (x₁ * x₂) ^ 2 := by
            rw [show c⁻¹ * (t * (c * (x₁ * x₂) ^ 2 * c⁻¹)) * c =
                  (c⁻¹ * t * c) * (x₁ * x₂) ^ 2 * (c⁻¹ * c) by group,
              hconj_t, inv_mul_cancel, mul_one]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
