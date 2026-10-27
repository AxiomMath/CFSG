module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ST1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ST2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem P0_le : closure ({t, tau} : Set G) ≤
    ctxNQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := by
  rw [Subgroup.closure_le]
  rintro g (hg1 | hg1)
  · rw [hg1]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact S4A.mem_normalizer_of_conj_mem (fun q hq => hg.normal_Q.2 t hg.t_mem_M q hq)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hg.rho_comm_t.symm
  · rw [hg1]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact S4A.mem_normalizer_of_conj_mem (fun q hq => hg.normal_Q.2 tau hg.tau_mem_M q hq)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hg.rho_comm_tau.symm

theorem isPGroup_P0 : IsPGroup 2 (closure ({t, tau} : Set G)) := by
  intro g
  refine ⟨1, ?_⟩
  have hmem : (g : G) ∈ closure ({t, tau} : Set G) := g.2
  have hsq : (g : G) * (g : G) = 1 := by
    rcases (S4B.mem_closure_pair_of_invol hg.t_mul_self hg.tau_mul_self hg.t_comm_tau).mp hmem with
      h | h | h | h
    · rw [h]; group
    · rw [h]; exact hg.t_mul_self
    · rw [h]; exact hg.tau_mul_self
    · rw [h]
      calc t * tau * (t * tau) = t * (tau * t) * tau := by group
        _ = t * (t * tau) * tau := by rw [hg.t_comm_tau]
        _ = (t * t) * (tau * tau) := by group
        _ = 1 := by rw [hg.t_mul_self, hg.tau_mul_self, one_mul]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]
  exact hsq

theorem mem_M_of_conj_fix {n : G}
    (hn : n ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G))
    (ht : n * t * n⁻¹ = t) (htau : n * tau * n⁻¹ = tau) : n ∈ ctxM t tau x₁ x₂ := by
  unfold ctxM
  apply S4A.mem_normalizer_of_conj_mem
  intro x hx
  have hfour : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
    rw [fourGrp, Subgroup.closure_le]
    rintro g (hg1 | hg1)
    · rw [hg1]; exact Subgroup.subset_closure (by simp)
    · rw [hg1]; exact Subgroup.subset_closure (by simp)
  have hK : ctxX t tau x₁ x₂ ≤
      (ctxX t tau x₁ x₂).comap (MulAut.conj n).toMonoidHom := by
    rw [ctxX, Subgroup.closure_le]
    rintro g (hg1 | hg1 | hg1 | hg1)
    · rw [hg1]
      change (MulAut.conj n) t ∈ ctxX t tau x₁ x₂
      rw [MulAut.conj_apply, ht]
      exact hg.t_mem_X
    · rw [hg1]
      change (MulAut.conj n) tau ∈ ctxX t tau x₁ x₂
      rw [MulAut.conj_apply, htau]
      exact hg.tau_mem_X
    · rw [hg1]
      change (MulAut.conj n) (x₁ ^ 2) ∈ ctxX t tau x₁ x₂
      rw [MulAut.conj_apply]
      exact hfour (hg.toZ4Pre.conj_V hn hg.y_mem_V)
    · rw [hg1]
      change (MulAut.conj n) ((x₁ * x₂) ^ 2) ∈ ctxX t tau x₁ x₂
      rw [MulAut.conj_apply]
      exact hfour (hg.toZ4Pre.conj_V hn hg.z_mem_V)
  exact hK hx

theorem tt_sylow : IsSylowIn 2 (closure {t, tau})
    (ctxNQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G)) := by
  obtain ⟨𝒮, h𝒮, hP𝒮⟩ := S4B.exists_isSylowIn_of_le hg.P0_le hg.isPGroup_P0
  have heq : closure ({t, tau} : Set G) = 𝒮 :=
    S4B.eq_of_forall_normalizes h𝒮.2.1 hP𝒮 ?_
  · rw [heq]; exact h𝒮
  · intro n hn hnorm
    have hnR := h𝒮.1 hn
    have hnQ : n ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      simpa [ctxNQ] using hnR.1
    have hnρ : n * rho = rho * n := Subgroup.mem_centralizer_singleton_iff.mp hnR.2
    have ht : n * t * n⁻¹ = t :=
      hg.toZ4Pre.conj_t_eq (hnorm t (Subgroup.subset_closure (by simp)))
    have htau : n * tau * n⁻¹ = tau :=
      hg.conj_tau_eq hnQ (hnorm tau (Subgroup.subset_closure (by simp)))
    have hnM : n ∈ ctxM t tau x₁ x₂ := hg.mem_M_of_conj_fix hnQ ht htau
    obtain ⟨k, hk⟩ := h𝒮.2.1 ⟨n, hn⟩
    have hnk : n ^ 2 ^ k = 1 := by
      have hval := congrArg Subtype.val hk
      simpa [Subgroup.coe_pow] using hval
    exact hg.toZ4Pre.two_elt_cent_rho hnM hnρ hnk

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
