module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbCtx11
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

structure Z4Good (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Z4Pre t L S x₁ x₂ lam rho tau where
  tau_cent : ∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau

theorem ctxO_swap (ht2 : t * t = 1) : ctxO t (t * tau) x₁ x₂ = ctxO t tau x₁ x₂ := by
  rw [ctxO, ctxO, S4B.ctxM_swap ht2]

theorem ctxQ_swap (ht2 : t * t = 1) :
    ctxQ t (t * tau) x₁ x₂ rho = ctxQ t tau x₁ x₂ rho := by
  rw [ctxQ, ctxQ, ctxO_swap ht2]

theorem ctxYq_swap (ht2 : t * t = 1) :
    ctxYq t (t * tau) x₁ x₂ rho = ctxYq t tau x₁ x₂ rho := by
  rw [ctxYq, ctxYq, ctxQ_swap ht2]

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem swap (hc : Ctx4Q t L S x₁ x₂ lam rho (t * tau)) :
    Z4Pre t L S x₁ x₂ lam rho (t * tau) :=
  ⟨hc, by rw [ctxQ_swap hp.t_mul_self]; exact hp.q_iso⟩

theorem good_of_cent_ttau (hc : Ctx4Q t L S x₁ x₂ lam rho (t * tau))
    (h : ∀ a ∈ ctxYq t tau x₁ x₂ rho, (t * tau) * a = a * (t * tau)) :
    Z4Good t L S x₁ x₂ lam rho (t * tau) :=
  ⟨hp.swap hc, by rw [ctxYq_swap hp.t_mul_self]; exact h⟩

theorem conj_Q_mem {n q : G} (hn : n ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G))
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : n * q * n⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
  (mem_normalizer_iff.mp hn q).mp hq

theorem conj_V {n v : G} (hn : n ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G))
    (hv : v ∈ fourGrp x₁ x₂) : n * v * n⁻¹ ∈ fourGrp x₁ x₂ := by
  obtain ⟨q, hq, rfl⟩ := (hp.V_eq_sq v).mp hv
  rw [← conj_pow]
  exact hp.sq_mem_V (hp.conj_Q_mem hn hq)

theorem conj_Y {n a : G} (hn : n ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G))
    (ha : a ∈ ctxYq t tau x₁ x₂ rho) : n * a * n⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  rw [hp.mem_Y_iff] at ha ⊢
  refine ⟨hp.conj_Q_mem hn ha.1, ?_⟩
  rw [conj_pow, ha.2]
  group

end Z4Pre

end CFSG.OddStandard.SmallF3.HarrisU33
