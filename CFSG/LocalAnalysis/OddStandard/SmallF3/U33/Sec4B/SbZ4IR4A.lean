module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

structure Z4IOdd (t tau x₁ x₂ rho : G) (Ng : Subgroup G) : Prop where
  le_C : Ng ≤ ctxCQ t tau x₁ x₂ rho
  odd : Odd (Nat.card Ng)
  inf_Q : Ng ⊓ ctxQ t tau x₁ x₂ rho = ⊥
  sup_Q : Ng ⊔ ctxQ t tau x₁ x₂ rho = ctxCQ t tau x₁ x₂ rho
  iff_odd : ∀ c ∈ ctxCQ t tau x₁ x₂ rho, c ∈ Ng ↔ Odd (orderOf c)

namespace Ctx4Z

abbrev z4iSub (_hz : Ctx4Z t L S x₁ x₂ lam rho tau) (A : Subgroup G) :
    Subgroup ↥(ctxNQ t tau x₁ x₂ rho) := A.subgroupOf (ctxNQ t tau x₁ x₂ rho)

@[expose] def z4iT (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : ↥(ctxNQ t tau x₁ x₂ rho) :=
  ⟨t, hz.z4i_t_mem_NQ⟩

@[expose] def z4iTau (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : ↥(ctxNQ t tau x₁ x₂ rho) :=
  ⟨tau, hz.z4i_tau_mem_NQ⟩

@[expose] def z4iRho (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : ↥(ctxNQ t tau x₁ x₂ rho) :=
  ⟨rho, hz.z4i_rho_mem_NQ⟩

@[expose] def z4iLam (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : ↥(ctxNQ t tau x₁ x₂ rho) :=
  ⟨lam, hz.z4i_lam_mem_NQ⟩

theorem z4i_mem_sub (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (A : Subgroup G)
    (x : ↥(ctxNQ t tau x₁ x₂ rho)) : x ∈ hz.z4iSub A ↔ (x : G) ∈ A :=
  Iff.rfl

theorem z4i_card_sub (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {A : Subgroup G}
    (hA : A ≤ ctxNQ t tau x₁ x₂ rho) : Nat.card (hz.z4iSub A) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem z4i_Q_le_NQ (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ≤ ctxNQ t tau x₁ x₂ rho :=
  Subgroup.le_normalizer

theorem z4i_exists_odd (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
    (hsyl : IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho)) :
    ∃ Ng : Subgroup G, Z4IOdd t tau x₁ x₂ rho Ng := by
  have hcent : ∀ c ∈ ctxCQ t tau x₁ x₂ rho, ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      c * q = q * c := fun c hc q hq => (Subgroup.mem_centralizer_iff.mp hc q hq).symm
  obtain ⟨N, hNC, hodd, hinf, hsup, hiff, _⟩ :=
    S4B.z4i_odd_core hsyl.1 hsyl.2.1 hsyl.2.2 hcent
  exact ⟨N, hNC, hodd, hinf, hsup, hiff⟩

end Ctx4Z

namespace Z4IOdd

variable {Ng : Subgroup G}

theorem le_NQ (hN : Z4IOdd t tau x₁ x₂ rho Ng) : Ng ≤ ctxNQ t tau x₁ x₂ rho :=
  hN.le_C.trans (ctxCQ_le_ctxNQ t tau x₁ x₂ rho)

theorem conj_mem (hN : Z4IOdd t tau x₁ x₂ rho Ng) {g n : G}
    (hg : g ∈ ctxNQ t tau x₁ x₂ rho) (hn : n ∈ Ng) : g * n * g⁻¹ ∈ Ng :=
  S4B.z4i_odd_core_normal hN.iff_odd hN.le_C (fun c hc => conj_mem_ctxCQ hg hc) n hn

end Z4IOdd

namespace Ctx4Z

theorem z4i_normal_N (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng : Subgroup G}
    (hN : Z4IOdd t tau x₁ x₂ rho Ng) : (hz.z4iSub Ng).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using Z4IOdd.conj_mem hN g.2 hn

theorem z4i_sup_sub (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng : Subgroup G}
    (hN : Z4IOdd t tau x₁ x₂ rho Ng) :
    hz.z4iSub (ctxQ t tau x₁ x₂ rho) ⊔ hz.z4iSub Ng = hz.z4iSub (ctxCQ t tau x₁ x₂ rho) := by
  rw [← Subgroup.subgroupOf_sup hz.z4i_Q_le_NQ (Z4IOdd.le_NQ hN), sup_comm, hN.sup_Q]

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
