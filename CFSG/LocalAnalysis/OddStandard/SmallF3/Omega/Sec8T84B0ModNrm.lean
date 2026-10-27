module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModSchur
public import Certificates.Certificate442267

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4)

variable {G : Type} [Group G] {E B : Subgroup G} {hBE : B ≤ E} {u : MulAut ↥E}
  {hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B} {A : Subgroup (MulAut ↥E)}
  {hAu : ∀ a ∈ A, a * u = u * a}

theorem schur_normalizer {X X' W' S' T' : Mat4} (hXX' : X * X' = 1) (hX'X : X' * X = 1)
    (hS : X * rho sigma = S' * X) (hT : X * rho tau = T' * X)
    (hWS : W' * rho sigma = S' * W') (hWT : W' * rho tau = T' * W') : W' = 0 ∨ W' = X := by
  have hS' : rho sigma * X' = X' * S' := by
    calc rho sigma * X'
        = (X' * X) * rho sigma * X' := by rw [hX'X, one_mul]
      _ = X' * (X * rho sigma) * X' := by noncomm_ring
      _ = X' * (S' * X) * X' := by rw [hS]
      _ = (X' * S') * (X * X') := by noncomm_ring
      _ = X' * S' := by rw [hXX', mul_one]
  have hT' : rho tau * X' = X' * T' := by
    calc rho tau * X'
        = (X' * X) * rho tau * X' := by rw [hX'X, one_mul]
      _ = X' * (X * rho tau) * X' := by noncomm_ring
      _ = X' * (T' * X) * X' := by rw [hT]
      _ = (X' * T') * (X * X') := by noncomm_ring
      _ = X' * T' := by rw [hXX', mul_one]
  have hMs : (X' * W') * rho sigma = rho sigma * (X' * W') := by
    calc (X' * W') * rho sigma = X' * (W' * rho sigma) := by noncomm_ring
      _ = X' * (S' * W') := by rw [hWS]
      _ = (X' * S') * W' := by noncomm_ring
      _ = (rho sigma * X') * W' := by rw [hS']
      _ = rho sigma * (X' * W') := by noncomm_ring
  have hMt : (X' * W') * rho tau = rho tau * (X' * W') := by
    calc (X' * W') * rho tau = X' * (W' * rho tau) := by noncomm_ring
      _ = X' * (T' * W') := by rw [hWT]
      _ = (X' * T') * W' := by noncomm_ring
      _ = (rho tau * X') * W' := by rw [hT']
      _ = rho tau * (X' * W') := by noncomm_ring
  have hXW : X * (X' * W') = W' := by rw [← mul_assoc, hXX', one_mul]
  rcases schur_rho hMs hMt with hM | hM
  · left
    rw [← hXW, hM, mul_zero]
  · right
    rw [← hXW, hM, mul_one]

theorem Frame.normalizer (F : Frame E B hBE u hfix A hAu)
    {m : Mat4}
    (hm : ∀ a : ↥A, Acts F.θ (a : MulAut ↥E)
      (Dm m (rho ((F.ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)))))
    (g : MulAut ↥E) (hg : g * u = u * g) (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    ∃ X : Mat4, (Acts F.θ g (Dm m X) ∨ Acts F.θ g (Dm m X * blk 1 1)) ∧
      ∀ b : ↥B, Multiplicative.toAdd (F.eB (resB hBE u hfix g hg b)) =
        X *ᵥ Multiplicative.toAdd (F.eB b) := by
  let hF := Certificates.certificate442267
  obtain ⟨α, U, hActs, hres⟩ := F.exists_blk g hg
  have hg' : g⁻¹ * u = u * g⁻¹ := by
    have h := congrArg (fun f : MulAut ↥E => g⁻¹ * f * g⁻¹) hg
    simpa [mul_assoc] using h.symm
  obtain ⟨α', U', hActs', _⟩ := F.exists_blk g⁻¹ hg'
  have hαα' : α * α' = 1 := by
    have h1 : Acts F.θ (g * g⁻¹) (blk α U * blk α' U') := hActs.mul hActs'
    rw [mul_inv_cancel] at h1
    have h2 : blk α U * blk α' U' = 1 := h1.matrix_eq (acts_one F.θ)
    rw [blk_mul, ← blk_one] at h2
    exact (blk_inj h2).1
  have hα'α : α' * α = 1 := by
    have h1 : Acts F.θ (g⁻¹ * g) (blk α' U' * blk α U) := hActs'.mul hActs
    rw [inv_mul_cancel] at h1
    have h2 : blk α' U' * blk α U = 1 := h1.matrix_eq (acts_one F.θ)
    rw [blk_mul, ← blk_one] at h2
    exact (blk_inj h2).1
  let aσ : ↥A := F.ψ.symm ⟨sigma, Equiv.Perm.mem_alternatingGroup.mpr hF.sigma_even⟩
  let aτ : ↥A := F.ψ.symm ⟨tau, Equiv.Perm.mem_alternatingGroup.mpr hF.tau_even⟩
  let aσ' : ↥A := ⟨g * (aσ : MulAut ↥E) * g⁻¹, hgA _ aσ.2⟩
  let aτ' : ↥A := ⟨g * (aτ : MulAut ↥E) * g⁻¹, hgA _ aτ.2⟩
  let S' : Mat4 := rho ((F.ψ aσ' : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
  let T' : Mat4 := rho ((F.ψ aτ' : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
  have hψσ : ((F.ψ aσ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = sigma := by
    simp [aσ]
  have hψτ : ((F.ψ aτ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = tau := by
    simp [aτ]
  have hconjσ : g * (aσ : MulAut ↥E) = (aσ' : MulAut ↥E) * g := by
    show g * (aσ : MulAut ↥E) = (g * (aσ : MulAut ↥E) * g⁻¹) * g
    group
  have hconjτ : g * (aτ : MulAut ↥E) = (aτ' : MulAut ↥E) * g := by
    show g * (aτ : MulAut ↥E) = (g * (aτ : MulAut ↥E) * g⁻¹) * g
    group
  have hmulσ : blk α U * Dm m (rho sigma) = Dm m S' * blk α U := by
    have h1 : Acts F.θ (g * (aσ : MulAut ↥E)) (blk α U * Dm m (rho sigma)) := by
      have h := hActs.mul (hm aσ)
      simpa [hψσ] using h
    have h2 : Acts F.θ (g * (aσ : MulAut ↥E)) (Dm m S' * blk α U) := by
      rw [hconjσ]
      have h := (hm aσ').mul hActs
      simpa [S'] using h
    exact Acts.matrix_eq h1 h2
  have hmulτ : blk α U * Dm m (rho tau) = Dm m T' * blk α U := by
    have h1 : Acts F.θ (g * (aτ : MulAut ↥E)) (blk α U * Dm m (rho tau)) := by
      have h := hActs.mul (hm aτ)
      simpa [hψτ] using h
    have h2 : Acts F.θ (g * (aτ : MulAut ↥E)) (Dm m T' * blk α U) := by
      rw [hconjτ]
      have h := (hm aτ').mul hActs
      simpa [T'] using h
    exact Acts.matrix_eq h1 h2
  have hcoreσ := normalizer_core hmulσ
  have hcoreτ := normalizer_core hmulτ
  have hW : U + α * m + m * α = 0 ∨ U + α * m + m * α = α :=
    schur_normalizer hαα' hα'α hcoreσ.1 hcoreτ.1 hcoreσ.2 hcoreτ.2
  refine ⟨α, ?_, hres⟩
  rcases Dm_form hW with hD | hD
  · left
    rwa [← hD]
  · right
    rwa [← hD]

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
