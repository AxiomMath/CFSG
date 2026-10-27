module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gTwist
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eCross
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gGood

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE



local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
  (aeBar8 vq vq_mul vq_eq_iff conj_vq vq_inv vq_empty E8Pkg A6eCtx)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}

theorem exists_std (hD : V3AE6D n) (hDN : V3AE6DNorm n) (hI : V3AE6I n)
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y)
    (hx : AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h) :
    ∃ (A : AEIdent (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) 8)
      (hspan : pSpan (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) = ae6I Ω[R] W (u₁ * u₂))
      (hker : A.φ.ker = ⊥) (hcore : pCoreOf 2 (ae6I Ω[R] W (u₁ * u₂)) = ae6D Ω[R] W (u₁ * u₂)),
      h * (y * t * y⁻¹) * h⁻¹ ∈ ae6I Ω[R] W (u₁ * u₂) ∧
      (pkgOf A hspan hker hcore).ph t = vq α₀ ∧
      (pkgOf A hspan hker hcore).ph (y * t * y⁻¹) = vq β₀ ∧
      permQ 8 ((pkgOf A hspan hker hcore).ph (h * (y * t * y⁻¹) * h⁻¹)) = σ₀ := by
  obtain ⟨hE1, hE2, hE3, hE4, -⟩ := hD Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨hDsq, -⟩ := hDN Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨-, A₀, hspan, hker₀, hcore⟩ := hI Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  set P₀ := pkgOf A₀ hspan hker₀ hcore with hP₀
  let C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y :=
    ⟨H, fr, P₀, e8Lab_pkgOf A₀ hspan hker₀ hcore, hDsq, hE1, hE2, hE3, hE4⟩
  set τ := y * t * y⁻¹ with hτ
  set x := h * τ * h⁻¹ with hxdef
  have hc : h * t * h⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    calc h * t * h⁻¹ = (t * h) * h⁻¹ := by rw [this]
      _ = t := by group
  obtain ⟨a, ha, hta, hxI, hfix, hpres⟩ := C.step4 hc hx.2.1
  obtain ⟨β, hτβ, hβ, hab⟩ := C.tau_cross ha hta
  have hta' : P₀.ph t = vq a := hta
  have hτβ' : P₀.ph τ = vq β := hτβ
  have hxx : x * x = 1 := by
    have h1 : t * t = 1 := H.ex.1.datum.hz.sq
    calc x * x = h * y * (t * t) * y⁻¹ * h⁻¹ := by rw [hxdef, hτ]; group
      _ = 1 := by rw [h1]; group
  set σ := P₀.rho x with hσ
  have hσσ : ∀ z, σ (σ z) = z := by
    intro z
    have h1 : σ * σ = 1 := by
      rw [hσ, ← P₀.rho_mul hxI hxI, hxx, P₀.rho_one]
    have := congrArg (fun σ : Equiv.Perm (Fin 8) => σ z) h1
    simpa [Equiv.Perm.mul_apply] using this
  have hτmem : τ ∈ ⁅ae6D Ω[R] W (u₁ * u₂), Subgroup.zpowers x⁆ := by
    rw [hx.2.2]
    exact Subgroup.subset_closure (by simp)
  have hmapβ : β.map σ.toEmbedding = β :=
    map_rho_eq_of_mem_comm P₀ hxI hxx hτmem hτβ'
  have hpb : ∀ z, σ z ∈ β ↔ z ∈ β := by
    intro z
    have h1 := Finset.ext_iff.mp hmapβ (σ z)
    simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply] at h1
    exact h1.symm
  obtain ⟨ψ, hψa, hψβ, hψσ⟩ := exists_perm_std ha hβ hab hσσ hfix hpres hpb
  have hker : (A₀.twist ψ⁻¹).φ.ker = ⊥ := by rw [twist_ker]; exact hker₀
  refine ⟨A₀.twist ψ⁻¹, hspan, hker, hcore, hxI, ?_, ?_, ?_⟩
  · rw [ph_twist A₀ hspan hker₀ hcore ψ⁻¹ t, ← hP₀, hta', twistHom_vq, ← hψa, map_perm_map_inv]
  · rw [ph_twist A₀ hspan hker₀ hcore ψ⁻¹ τ, ← hP₀, hτβ', twistHom_vq, ← hψβ, map_perm_map_inv]
  · rw [ph_twist A₀ hspan hker₀ hcore ψ⁻¹ x, ← hP₀, permQ_twistHom]
    have hρ : permQ 8 (P₀.ph x) = σ := rfl
    rw [hρ, inv_inv]
    calc ψ⁻¹ * σ * ψ = ψ⁻¹ * (σ * ψ) := by group
      _ = ψ⁻¹ * (ψ * σ₀) := by rw [hψσ]
      _ = σ₀ := by group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
