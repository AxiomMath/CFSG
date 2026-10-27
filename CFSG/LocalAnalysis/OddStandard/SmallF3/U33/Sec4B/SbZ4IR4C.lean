module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4FC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4P

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

theorem z4iPartC (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng V' : Subgroup G} {v₁ v₂ : G}
    (hN : Z4IOdd t tau x₁ x₂ rho Ng) (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂) :
    S4B.Z4IPartC (hz.z4iSub Ng) (hz.z4iSub (ctxQ t tau x₁ x₂ rho))
      (hz.z4iSub (ctxYq t tau x₁ x₂ rho)) (hz.z4iSub (fourGrp x₁ x₂)) (hz.z4iSub V')
      (hz.z4iSub (baseGrp x₁ x₂)) (hz.z4iSub (ctxKI t tau x₁ x₂ rho))
      hz.z4iRho hz.z4iT hz.z4iTau hz.z4iLam := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show rho ^ 3 = 1
    simpa [hz.ord_rho] using pow_orderOf_eq_one rho
  · intro x hx
    change rho * (x : G) * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho
    exact (mem_set_normalizer_iff.mp hz.z4i_rho_mem_NQ (x : G)).mp hx
  · intro x hx
    change rho * (x : G) * rho⁻¹ ∈ ctxYq t tau x₁ x₂ rho
    exact hz.z4i_NQ_Y hz.z4i_rho_mem_NQ hx
  · intro x hx
    change rho * (x : G) * rho⁻¹ ∈ fourGrp x₁ x₂
    exact hz.z4i_NQ_V hz.z4i_rho_mem_NQ hx
  · intro x hx
    change rho * (x : G) * rho⁻¹ ∈ V'
    exact (mem_set_normalizer_iff.mp hV.2.2.2.2.2.1 (x : G)).mp hx
  · intro x hx
    have hxmem : (x : G) ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
      rw [hz.CQ_t]; exact hx
    have hxt : Commute t (x : G) := mem_centralizer_iff.mp hxmem.2 t rfl
    have hrt : Commute t rho := hz.rho_comm_t.symm
    have hyQ : rho * (x : G) * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      (mem_set_normalizer_iff.mp hz.z4i_rho_mem_NQ (x : G)).mp hxmem.1
    have hycent : rho * (x : G) * rho⁻¹ ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.mpr (((hrt.mul_right hxt).mul_right hrt.inv_right).eq).symm
    change rho * (x : G) * rho⁻¹ ∈ baseGrp x₁ x₂
    rw [← hz.CQ_t]
    exact ⟨hyQ, hycent⟩
  · intro x hx
    change rho * (x : G) * rho⁻¹ ∈ ctxKI t tau x₁ x₂ rho
    exact hz.z4i_rho_norm_KI (k := (x : G)) hx
  · intro q hq h
    have h' : rho * (q : G) * rho⁻¹ = (q : G) := congrArg Subtype.val h
    exact Subtype.ext (hz.rho_fpf (q : G) hq h')
  · intro k hk h
    rw [hz.z4i_sup_sub hN] at h ⊢
    exact hz.z4i_rho_fpf_KC (k := (k : G)) hk h
  · intro x hx
    change t * (x : G) * t⁻¹ ∈ ctxKI t tau x₁ x₂ rho
    exact hz.z4i_t_norm_KI (k := (x : G)) hx
  · intro x hx
    change tau * (x : G) * tau⁻¹ ∈ ctxKI t tau x₁ x₂ rho
    exact hz.z4i_tau_norm_KI (k := (x : G)) hx
  · intro x hx
    change lam * (x : G) * lam⁻¹ ∈ ctxKI t tau x₁ x₂ rho
    exact hz.z4i_lam_norm_KI (k := (x : G)) hx
  · intro k hk
    rw [hz.z4i_sup_sub hN]
    change t * (k : G) * t⁻¹ * (k : G)⁻¹ ∈ ctxCQ t tau x₁ x₂ rho
    exact hz.z4i_comm_t_KI (k := (k : G)) hk
  · intro q hq
    exact Subtype.ext (hz.tau_inv_Q (q : G) hq)
  · intro h
    rw [hz.z4i_sup_sub hN] at h
    exact hz.z4i_tau_not_mem_C h

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
