module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem conj_eq_mul_comm_inv {g k : G} (hg : g ∈ ctxX t tau x₁ x₂)
    (hgV : ∀ v ∈ fourGrp x₁ x₂, g * v = v * g) (hk : k ∈ ctxO t tau x₁ x₂) :
    k * g * k⁻¹ = g * (z4Comm g k)⁻¹ := by
  have hv : z4Comm g k ∈ fourGrp x₁ x₂ := hp.comm_mem hg hk
  have hc : g * (z4Comm g k)⁻¹ = (z4Comm g k)⁻¹ * g := hgV _ (inv_mem hv)
  rw [hc]
  unfold z4Comm
  group

theorem conjIn_Q_eq {g : G} (hg : g ∈ ctxX t tau x₁ x₂)
    (hgV : ∀ v ∈ fourGrp x₁ x₂, g * v = v * g)
    (hsurj : ∀ v ∈ fourGrp x₁ x₂, ∃ a ∈ ctxQ t tau x₁ x₂ rho, z4Comm g a = v) :
    conjIn (ctxQ t tau x₁ x₂ rho) g = g • (fourGrp x₁ x₂ : Set G) := by
  ext u
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine Set.mem_smul_set.mpr ⟨(z4Comm g k)⁻¹, inv_mem (hp.comm_mem hg (hp.Q_le_O hk)), ?_⟩
    rw [smul_eq_mul]
    exact (hp.conj_eq_mul_comm_inv hg hgV (hp.Q_le_O hk)).symm
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hu
    obtain ⟨a, ha, hav⟩ := hsurj v⁻¹ (inv_mem hv)
    refine ⟨a, ha, ?_⟩
    rw [hp.conj_eq_mul_comm_inv hg hgV (hp.Q_le_O ha), hav, inv_inv, smul_eq_mul]

theorem tQ_eq : conjIn (ctxQ t tau x₁ x₂ rho) t = t • (fourGrp x₁ x₂ : Set G) :=
  hp.conjIn_Q_eq hp.t_mem_X hp.t_comm_V fun v hv => by
    obtain ⟨a, ha, hav⟩ := hp.exists_comm_eq v hv
    exact ⟨a, hp.Y_le_Q ha, hav⟩

theorem tauQ_eq (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹) :
    conjIn (ctxQ t tau x₁ x₂ rho) tau = tau • (fourGrp x₁ x₂ : Set G) :=
  hp.conjIn_Q_eq hp.tau_mem_X hp.tau_comm_V fun v hv => by
    obtain ⟨q, hq, rfl⟩ := (hp.V_eq_sq v).mp hv
    refine ⟨q⁻¹, inv_mem hq, ?_⟩
    have h := htau q⁻¹ (inv_mem hq)
    unfold z4Comm
    rw [h, inv_inv, pow_two]

end Z4Pre

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem ttauQ_eq :
    conjIn (ctxQ t tau x₁ x₂ rho) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G) := by
  refine hg.toZ4Pre.conjIn_Q_eq hg.ttau_mem_X (fun v hv => ?_) fun v hv => ?_
  · rw [mul_assoc, hg.tau_comm_V v hv, ← mul_assoc, hg.t_comm_V v hv, mul_assoc]
  · obtain ⟨a, ha, hav⟩ := hg.exists_comm_eq v hv
    refine ⟨a, hg.Y_le_Q ha, ?_⟩
    have h1 : z4Comm tau a = 1 := hg.comm_eq_one_iff.mpr (hg.tau_cent a ha)
    rw [hg.comm_ttau (hg.Y_le_Q ha), h1, hav, one_mul]

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
