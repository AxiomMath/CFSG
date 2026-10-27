module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6DN

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6DN

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

@[expose] def V3AE6CentE (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      ∀ x ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y),
        (∀ e ∈ ae6E Ω[R] (u₁ * u₂), x * e = e * x) →
          ∀ g ∈ rLayer Ω[R] (u₁ * u₂), x * g * x⁻¹ * g⁻¹ ∈ ae6E Ω[R] (u₁ * u₂)

theorem v3AE6DNorm_of (hE : V3AE6E n) (hC : V3AE6EComm n) (hCE : V3AE6CentE n) : V3AE6DNorm n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  refine ⟨ae6D_sq_eq_one hE hC H fr, ?_⟩
  have hEdat := hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  have hcomm := hC Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  set E := ae6E Ω[R] (u₁ * u₂) with hEdef
  set D := ae6D Ω[R] W (u₁ * u₂) with hDdef
  set Yu := rLayer Ω[R] (u₁ * u₂) with hYudef
  have hED : E ≤ D := by
    rw [hDdef]
    unfold ae6D
    refine le_trans ?_ (le_iSup _ (1 : ↥(MGrp Ω[R] W)))
    simp only [OneMemClass.coe_one, conjSub_one]
    exact le_rfl
  have hDC : D ≤ Subgroup.centralizer (E : Set Y) := by
    rw [hDdef]
    unfold ae6D
    refine iSup_le fun m => ?_
    intro x hx
    rw [mem_conjSub_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h := hcomm (m : Y) m.2 e he _ hx
    have e1 : (m : Y) * ((m : Y)⁻¹ * x * (m : Y)) * (m : Y)⁻¹ = x := by group
    rw [e1] at h
    exact h.eq
  have hmem : ∀ g ∈ Yu, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    have hdE : ∀ e ∈ E, d * e = e * d := fun e he =>
      ((Subgroup.mem_centralizer_iff.mp (hDC hd)) e he).symm
    have hdu : d ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hdE _ hEdat.2.1
    have hc := hCE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr d hdu hdE g hg
    have e1 : g * d * g⁻¹ = (d * g * d⁻¹ * g⁻¹)⁻¹ * d := by group
    rw [e1]
    exact D.mul_mem (D.inv_mem (hED hc)) hd
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · exact hmem g hg d
  · intro hd
    have h := hmem g⁻¹ (Yu.inv_mem hg) _ hd
    have e1 : g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d := by group
    rwa [e1] at h

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6DN
