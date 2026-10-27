module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaG
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameD0

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem cD₀_conj_inv (σ : Perm (Fin 10)) :
    cD₀ * (cD₀ * σ * cD₀⁻¹) * cD₀⁻¹ = σ := by
  have hinv : cD₀⁻¹ * cD₀⁻¹ = 1 := by
    rw [← mul_inv_rev cD₀ cD₀, cD₀_mul_self, inv_one]
  calc cD₀ * (cD₀ * σ * cD₀⁻¹) * cD₀⁻¹
      = (cD₀ * cD₀) * σ * (cD₀⁻¹ * cD₀⁻¹) := by group
    _ = σ := by rw [cD₀_mul_self, hinv, mul_one, one_mul]

private theorem sign_conj_cD₀ (σ : Perm (Fin 10)) :
    sign (cD₀ * σ * cD₀⁻¹) = sign σ := by
  rcases Int.units_eq_one_or (sign cD₀) with h | h <;>
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, h] <;>
    simp

private theorem mem_stab2_cD₀_conj {σ : Perm (Fin 10)} (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    cD₀ * σ * cD₀⁻¹ ∈ stab2 8 9 := by
  rw [mem_stab2]
  have hinv : cD₀⁻¹ = cD₀ := inv_eq_of_mul_eq_one_right cD₀_mul_self
  have hc8 : cD₀ 8 = 0 := by decide
  have hc9 : cD₀ 9 = 1 := by decide
  have hc0 : cD₀ 0 = 8 := by decide
  have hc1 : cD₀ 1 = 9 := by decide
  constructor
  · rw [hinv]
    simp only [Equiv.Perm.mul_apply]
    rw [hc8, h0, hc0]
  · rw [hinv]
    simp only [Equiv.Perm.mul_apply]
    rw [hc9, h1, hc1]

theorem exists_frame_at_conj (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (c : Perm (Fin 10)) :
    ∃ κ : Perm (Fin 10) →* G, CentData (ι (c * τ₀ * c⁻¹)) κ ∧ κ τ₀ = z ∧
      (pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1 →
        ∀ ρ : Perm (Fin 8), κ (liftS8 ρ) = ι (c * liftS8 ρ * c⁻¹)) ∧
      (pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2 →
        ∀ ρ : Perm (Fin 8), κ (liftS8 ρ) =
          ι (c * liftS8 ρ * c⁻¹) * (if sign ρ = 1 then 1 else z * ι (c * τ₀ * c⁻¹))) := by
  classical
  obtain ⟨g, hg⟩ := exists_gElt (centData_frameConj hC c)
    (isConj_z_frameConj_τ₀ hC hx c) (not_isConj_z_mul_frameConj hC hP2 c)
  obtain ⟨κ, hκC, hκτ, hκσ⟩ := GElt.exists_twist_frame (centData_frameConj hC c) hg
  refine ⟨κ, ?_, hκτ, ?_, ?_⟩
  · rw [frameConj_apply] at hκC
    exact hκC
  · intro h1 ρ
    have h1c : pairOrder ((frameConj ι c) τ₀) ((frameConj ι c) (swap 0 1)) = N10 1 :=
      (pairOrder_frameConj ι c).trans h1
    have hcomm := (GElt.pairOrder_eq_N10_one_iff (centData_frameConj hC c) hg).1 h1c ρ
    rw [hκσ (liftS8 ρ), hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact frameConj_apply ι c (liftS8 ρ)
  · intro h2 ρ
    have h2c : pairOrder ((frameConj ι c) τ₀) ((frameConj ι c) (swap 0 1)) = N10 2 :=
      (pairOrder_frameConj ι c).trans h2
    have htw := (GElt.pairOrder_eq_N10_two_iff (centData_frameConj hC c) hg).1 h2c ρ
    rw [hκσ (liftS8 ρ), htw]
    simp only [frameConj_apply]

theorem exists_frame_at_d (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) :
    ∃ ιd : Perm (Fin 10) →* G, CentData (ι (swap 0 1)) ιd ∧ ιd (swap 0 1) = z ∧
      (pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1 →
        ∀ σ : Perm (Fin 10), σ 0 = 0 → σ 1 = 1 → ιd σ = ι σ) ∧
      (pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2 →
        ∀ σ : Perm (Fin 10), σ 0 = 0 → σ 1 = 1 →
          ιd σ = ι σ * (if sign σ = 1 then 1 else z * ι (swap 0 1))) := by
  classical
  obtain ⟨κ, hκC, hκτ, h1, h2⟩ := exists_frame_at_conj hC hx hP2 cD₀
  have hκC' : CentData (ι (swap 0 1)) κ := by
    rw [cD₀_conj_τ₀] at hκC
    exact hκC
  refine ⟨frameConj κ cD₀, ?_, ?_, ?_, ?_⟩
  · exact centData_comp_conj hκC' cD₀
  · rw [frameConj_apply, cD₀_conj_swap, hκτ]
  · intro hN1 σ hσ0 hσ1
    obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 (mem_stab2_cD₀_conj hσ0 hσ1)
    have hιd : (frameConj κ cD₀) σ = κ (liftS8 ρ) := by
      rw [frameConj_apply, hρ]
    have hmul : cD₀ * liftS8 ρ * cD₀⁻¹ = σ := by
      rw [hρ]; exact cD₀_conj_inv σ
    rw [hιd, h1 hN1 ρ, hmul]
  · intro hN2 σ hσ0 hσ1
    obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 (mem_stab2_cD₀_conj hσ0 hσ1)
    have hιd : (frameConj κ cD₀) σ = κ (liftS8 ρ) := by
      rw [frameConj_apply, hρ]
    have hmul : cD₀ * liftS8 ρ * cD₀⁻¹ = σ := by
      rw [hρ]; exact cD₀_conj_inv σ
    have hsgn : sign ρ = sign σ := by
      rw [← sign_liftS8 ρ, hρ, sign_conj_cD₀]
    rw [hιd, h2 hN2 ρ, hmul, cD₀_conj_τ₀, hsgn]

end CFSG.OddStandard.AltStdSec.SwapPartner
