module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NE

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace ZNW4

variable (hw : ZNW4 t L S x₁ x₂ lam rho tau)
include hw

theorem comm_tau_mem_Y :
    ∀ w ∈ ctxWN t tau x₁ x₂ rho, tau * w * tau⁻¹ * w⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  intro w hwW
  have hconj : tau * w * tau⁻¹ ∈ ctxWN t tau x₁ x₂ rho := hw.tau_conj_ctxWN hwW
  have htheta : tau * w * tau⁻¹ * w⁻¹ ∈ ctxWN t tau x₁ x₂ rho :=
    mul_mem hconj (inv_mem hwW)
  have hw2Y : w ^ 2 ∈ ctxYq t tau x₁ x₂ rho := by
    refine (hw.mem_Y_iff (w ^ 2)).mpr ⟨hw.W_sq_mem_Q w hwW, ?_⟩
    calc (w ^ 2) ^ 2 = w ^ 4 := by group
      _ = 1 := hw.W_pow_four w hwW
  have hcent : tau * w ^ 2 * tau⁻¹ = w ^ 2 := by
    rw [hw.tau_cent_Y (w ^ 2) hw2Y, mul_assoc, mul_inv_cancel, mul_one]
  have hu : w ^ 2 * w ^ 2 = 1 := by
    calc w ^ 2 * w ^ 2 = (w ^ 2) ^ 2 := by group
      _ = w ^ 4 := by group
      _ = 1 := hw.W_pow_four w hwW
  have hcomm : Commute (tau * w * tau⁻¹) w⁻¹ :=
    (commute_iff_eq _ _).mpr (hw.W_comm _ hconj _ (inv_mem hwW))
  have ha2 : (tau * w * tau⁻¹) ^ 2 = w ^ 2 := by
    calc (tau * w * tau⁻¹) ^ 2 = tau * w ^ 2 * tau⁻¹ := by
          rw [pow_two, pow_two]; group
      _ = w ^ 2 := hcent
  have hb2 : (w⁻¹) ^ 2 = w ^ 2 := by
    calc (w⁻¹) ^ 2 = (w ^ 2)⁻¹ := by group
      _ = w ^ 2 := inv_eq_of_mul_eq_one_right hu
  have hsq : (tau * w * tau⁻¹ * w⁻¹) ^ 2 = 1 := by
    rw [hcomm.mul_pow, ha2, hb2, hu]
  exact hw.W_invol_mem_Y (w := tau * w * tau⁻¹ * w⁻¹) htheta hsq

theorem comm_tau_surj :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∃ w ∈ ctxWN t tau x₁ x₂ rho, tau * w * tau⁻¹ * w⁻¹ = a := by
  obtain ⟨N, hNW, hmemN, hsurjN, hcardN⟩ :=
    S4B.exists_comm_image (A := ctxWN t tau x₁ x₂ rho) hw.W_comm
      (g := tau) (fun a ha => hw.tau_conj_ctxWN ha)
  have hWY : ctxWN t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G) = ctxYq t tau x₁ x₂ rho := by
    apply le_antisymm
    · intro w hwint
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hwint.2
      refine hw.cent_tau_ctxWN hwint.1 ?_
      calc tau * w * tau⁻¹ = w * tau * tau⁻¹ := by rw [← hc]
        _ = w := by group
    · intro w hwY
      exact ⟨hw.Y_le_ctxWN hwY,
        Subgroup.mem_centralizer_singleton_iff.mpr (hw.tau_cent_Y w hwY).symm⟩
  have hNcard : Nat.card N = 16 := by
    have h := hcardN
    rw [hWY, hw.card_ctxWN, hw.card_Y] at h
    omega
  have hNY : N ≤ ctxYq t tau x₁ x₂ rho := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := hsurjN n hn
    have h := hw.comm_tau_mem_Y a ha
    rw [show a * tau * a⁻¹ * tau⁻¹ = (tau * a * tau⁻¹ * a⁻¹)⁻¹ from by group]
    exact inv_mem h
  have hNYeq : N = ctxYq t tau x₁ x₂ rho :=
    Subgroup.eq_of_le_of_card_ge hNY (by rw [hw.card_Y, hNcard])
  intro a ha
  have haN : a⁻¹ ∈ N := by rw [hNYeq]; exact inv_mem ha
  obtain ⟨w, hwW, hweq⟩ := hsurjN a⁻¹ haN
  refine ⟨w, hwW, ?_⟩
  rw [show tau * w * tau⁻¹ * w⁻¹ = (w * tau * w⁻¹ * tau⁻¹)⁻¹ from by group, ← hweq, inv_inv]

end ZNW4

end CFSG.OddStandard.SmallF3.HarrisU33
