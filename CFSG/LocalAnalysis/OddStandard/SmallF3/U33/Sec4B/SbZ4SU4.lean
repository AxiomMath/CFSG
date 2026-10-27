module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SU2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SU3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem mem_Q_of_comm_comm (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹)
    {V' : Subgroup G} {v₁ v₂ : G} (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂) {s : G}
    (hs : s ∈ ctxU t tau x₁ x₂ lam)
    (h : ∀ a ∈ ctxU t tau x₁ x₂ lam, ∀ b ∈ ctxU t tau x₁ x₂ lam,
      s * z4Comm a b = z4Comm a b * s) : s ∈ ctxQ t tau x₁ x₂ rho := by
  have hv₁U : v₁ ∈ ctxU t tau x₁ x₂ lam :=
    hg.toZ4Pre.Q_le_U (hV.V'_le_Q hg.toZ4Pre hV.v₁_mem)
  have hx₁U : x₁ ∈ ctxU t tau x₁ x₂ lam := hg.toZ4Pre.Q_le_U hg.x₁_mem_Q
  have hy : s * x₁ ^ 2 = x₁ ^ 2 * s := by
    have hc := h t hg.toZ4Pre.t_mem_U v₁ hv₁U
    rwa [hV.comm_v₁ hg.toZ4Pre] at hc
  have hsO : s ∈ ctxO t tau x₁ x₂ := hg.mem_O_of_comm_y hs hy
  have h₁ : s * (x₂ * x₁⁻¹) = (x₂ * x₁⁻¹) * s := by
    have hc := h lam hg.toZ4Pre.lam_mem_U x₁ hx₁U
    have hcomm : z4Comm lam x₁ = x₂ * x₁⁻¹ := by
      unfold z4Comm
      rw [hg.lam_conj_x₁]
    rwa [hcomm] at hc
  have h₃ : s * (v₂ * v₁) = (v₂ * v₁) * s := by
    have hc := h (lam * t) hg.toZ4Pre.sigma_mem_U v₁ hv₁U
    have hv₁inv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right (hV.sq_eq_one hV.v₁_mem)
    have hcomm : z4Comm (lam * t) v₁ = v₂ * v₁ := by
      unfold z4Comm
      rw [hV.sigma_v₁, hv₁inv]
    rwa [hcomm] at hc
  exact hg.mem_Q_of_comm_p htau hV hsO h₁ h₃

theorem mem_ctxNQ_of_normalizes_U (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹)
    {V' : Subgroup G} {v₁ v₂ : G} (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂) {n : G}
    (hn : ∀ x ∈ ctxU t tau x₁ x₂ lam, n * x * n⁻¹ ∈ ctxU t tau x₁ x₂ lam) :
    n ∈ ctxNQ t tau x₁ x₂ rho := by
  have hnU : n ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) :=
    S4A.mem_normalizer_of_conj_mem hn
  have hn' : ∀ x ∈ ctxU t tau x₁ x₂ lam, n⁻¹ * x * n ∈ ctxU t tau x₁ x₂ lam := by
    intro x hx
    have hiff := (Subgroup.mem_normalizer_iff.mp (inv_mem hnU)) x
    simpa using hiff.mp hx
  have hQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, n * q * n⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro q hq
    have hqU : q ∈ ctxU t tau x₁ x₂ lam := hg.toZ4Pre.Q_le_U hq
    have hnqU : n * q * n⁻¹ ∈ ctxU t tau x₁ x₂ lam := hn q hqU
    refine hg.mem_Q_of_comm_comm htau hV hnqU ?_
    intro a ha b hb
    have ha' : n⁻¹ * a * n ∈ ctxU t tau x₁ x₂ lam := hn' a ha
    have hb' : n⁻¹ * b * n ∈ ctxU t tau x₁ x₂ lam := hn' b hb
    set c : G := z4Comm (n⁻¹ * a * n) (n⁻¹ * b * n) with hcdef
    have hc : c ∈ ctxQ t tau x₁ x₂ rho := hg.comm_mem_Q ha' hb'
    have hz : z4Comm a b = n * c * n⁻¹ := by
      rw [hcdef]
      unfold z4Comm
      group
    rw [hz]
    have hqc : q * c = c * q := hg.Q_comm q hq c hc
    calc (n * q * n⁻¹) * (n * c * n⁻¹) = n * (q * c) * n⁻¹ := by group
      _ = n * (c * q) * n⁻¹ := by rw [hqc]
      _ = (n * c * n⁻¹) * (n * q * n⁻¹) := by group
  unfold ctxNQ
  exact S4A.mem_normalizer_of_conj_mem hQ

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
