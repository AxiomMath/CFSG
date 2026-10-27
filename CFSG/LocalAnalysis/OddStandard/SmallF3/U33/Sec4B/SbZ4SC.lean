module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4B1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

@[expose] def z4Comm (g a : G) : G := g * a * g⁻¹ * a⁻¹

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem t_mem_X : t ∈ ctxX t tau x₁ x₂ := subset_closure (by simp)

theorem tau_mem_X : tau ∈ ctxX t tau x₁ x₂ := subset_closure (by simp)

theorem ttau_mem_X : t * tau ∈ ctxX t tau x₁ x₂ := mul_mem hp.t_mem_X hp.tau_mem_X

theorem comm_mem {g a : G} (hg : g ∈ ctxX t tau x₁ x₂) (ha : a ∈ ctxO t tau x₁ x₂) :
    z4Comm g a ∈ fourGrp x₁ x₂ := by
  have ha' : a ∈ ctxR t tau x₁ x₂ := hp.O_eq_R ▸ ha
  have h := ha'.2.1 g hg
  have h2 : z4Comm g a = (a * g * a⁻¹ * g⁻¹)⁻¹ := by unfold z4Comm; group
  rw [h2]; exact inv_mem h

theorem comm_V {g a : G} (hg : g ∈ ctxO t tau x₁ x₂) (ha : a ∈ fourGrp x₁ x₂) :
    z4Comm g a = 1 := by
  have h : g ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [← hp.O_eq_CV]; exact hg
  have h2 := mem_centralizer_iff.mp h.2 a ha
  unfold z4Comm
  rw [← h2]; group

theorem comm_mul {g a b : G} (hg : g ∈ ctxX t tau x₁ x₂) (ha : a ∈ ctxQ t tau x₁ x₂ rho)
    (hb : b ∈ ctxQ t tau x₁ x₂ rho) : z4Comm g (a * b) = z4Comm g a * z4Comm g b := by
  have hv := hp.comm_mem hg (hp.Q_le_O hb)
  have h1 : a * z4Comm g b = z4Comm g b * a := hp.Q_comm _ ha _ (hp.V_le_Q hv)
  have h2 : a * z4Comm g b * a⁻¹ = z4Comm g b := by rw [h1]; group
  calc z4Comm g (a * b) = z4Comm g a * (a * z4Comm g b * a⁻¹) := by unfold z4Comm; group
    _ = z4Comm g a * z4Comm g b := by rw [h2]

theorem comm_inv {g a : G} (hg : g ∈ ctxX t tau x₁ x₂) (ha : a ∈ ctxQ t tau x₁ x₂ rho) :
    z4Comm g a⁻¹ = (z4Comm g a)⁻¹ := by
  have h := hp.comm_mul hg ha (inv_mem ha)
  have h1 : z4Comm g (a * a⁻¹) = 1 := by unfold z4Comm; group
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem comm_conj {g c : G} (hgc : g * c = c * g) (a : G) :
    z4Comm g (c * a * c⁻¹) = c * z4Comm g a * c⁻¹ := by
  have h : g = c * g * c⁻¹ := by rw [← hgc]; group
  unfold z4Comm
  calc g * (c * a * c⁻¹) * g⁻¹ * (c * a * c⁻¹)⁻¹
      = (c * g * c⁻¹) * (c * a * c⁻¹) * (c * g * c⁻¹)⁻¹ * (c * a * c⁻¹)⁻¹ := by rw [← h]
    _ = c * (g * a * g⁻¹ * a⁻¹) * c⁻¹ := by group

theorem comm_ttau {a : G} (ha : a ∈ ctxQ t tau x₁ x₂ rho) :
    z4Comm (t * tau) a = z4Comm tau a * z4Comm t a := by
  have hv := hp.comm_mem hp.tau_mem_X (hp.Q_le_O ha)
  have h1 : t * z4Comm tau a * t⁻¹ = z4Comm tau a := by rw [hp.t_comm_V _ hv]; group
  calc z4Comm (t * tau) a = t * (z4Comm tau a * a) * t⁻¹ * a⁻¹ := by unfold z4Comm; group
    _ = (t * z4Comm tau a * t⁻¹) * (t * a * t⁻¹ * a⁻¹) := by group
    _ = z4Comm tau a * z4Comm t a := by rw [h1]; rfl

theorem comm_eq_one_iff {g a : G} : z4Comm g a = 1 ↔ g * a = a * g := by
  unfold z4Comm
  constructor
  · intro h
    calc g * a = (g * a * g⁻¹ * a⁻¹) * (a * g) := by group
      _ = a * g := by rw [h, one_mul]
  · intro h
    rw [h]; group

end Z4Pre

end CFSG.OddStandard.SmallF3.HarrisU33
