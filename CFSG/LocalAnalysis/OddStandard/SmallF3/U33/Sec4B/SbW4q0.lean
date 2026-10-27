module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4d4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_toW4Ctxc (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    W4Ctxc t L S x₁ x₂ lam rho tau := by
  have c0 : W4Ctx0 t L S x₁ x₂ lam rho tau := { toCtx10 := hc.toCtx10, tM := hc.tM }
  have ca : W4Ctxa t L S x₁ x₂ lam rho tau :=
    { toW4Ctx0 := c0, card_M := hc.card_M, normal_V := hc.normal_V, normal_E := hc.normal_E }
  have cb : W4Ctxb t L S x₁ x₂ lam rho tau :=
    { toW4Ctxa := ca, O_eq_C := hc.O_eq_CV, card_O := hc.card_O,
      lam_not_mem_O := w4_lam_not_mem_O ca }
  exact { toW4Ctxb := cb, M_eq := hc.M_eq, S_le_U := hc.S_le_U, U_sylow := hc.U_sylow }

theorem w4q_X_facts
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    CFSG.Open.IsElemAbelian 2 (ctxX t tau x₁ x₂) ∧ Nat.card (ctxX t tau x₁ x₂) = 16 :=
  S4A.ctxX_elemAbelian_of hc.toCtx10.toCtx4.toCtx hc.toCtx10.toCtx4.l44.1

theorem w4q_V_central (hc : Ctx4C t L S x₁ x₂ lam rho tau) {g v : G}
    (hg : g ∈ ctxO t tau x₁ x₂) (hv : v ∈ fourGrp x₁ x₂) : g * v * g⁻¹ = v :=
  w4_O_cent_V (w4q_toW4Ctxc hc).toW4Ctxb hg hv

theorem w4q_X_le_O
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    ctxX t tau x₁ x₂ ≤ ctxO t tau x₁ x₂ := by
  intro g hg
  rw [hc.O_eq_CV]
  refine ⟨Subgroup.le_normalizer hg, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact (w4_X_comm hc.toCtx10.toCtx4 hg (w4_V_le_X t tau x₁ x₂ hv)).symm

theorem w4q_V_le_O
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ ctxO t tau x₁ x₂ :=
  (w4_V_le_X t tau x₁ x₂).trans (w4q_X_le_O hc)

theorem w4q_A_le_O (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ≤ ctxO t tau x₁ x₂ := by
  obtain ⟨-, -, h₁, h₂⟩ := w4_gens_mem_O (w4q_toW4Ctxc hc).toW4Ctxb
  rw [baseGrp, Subgroup.closure_le]
  intro x hx
  rcases (by simpa using hx) with h | h
  · rw [h]; exact h₁
  · rw [h]; exact h₂

theorem w4q_O_comm_X
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {g x : G}
    (hg : g ∈ ctxO t tau x₁ x₂) (hx : x ∈ ctxX t tau x₁ x₂) :
    g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂ :=
  (w4_O_le_R (w4q_toW4Ctxc hc).toW4Ctxb hg).2.1 x hx

theorem w4q_M_comm_X
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {g x : G}
    (hg : g ∈ ctxM t tau x₁ x₂) (hx : x ∈ ctxX t tau x₁ x₂) :
    g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂ := by
  have hw := w4q_toW4Ctxc hc
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hVc : ∀ v ∈ fourGrp x₁ x₂, g * v * g⁻¹ * v⁻¹ ∈ fourGrp x₁ x₂ := fun v hv =>
    mul_mem (hc.normal_V.2 g hg v hv) (inv_mem hv)
  refine w4_commutator_mem_V_of_gens hc4 ?_ ?_ (hVc _ hyV) (hVc _ hzV) x hx
  · obtain ⟨a, ha, hae⟩ := Set.mem_smul_set.mp (w4_conj_t_mem hw.toW4Ctx0 hg)
    simp only [smul_eq_mul] at hae
    rw [← hae, w4_t_comm_V hc4 ha, mul_inv_cancel_right]
    exact ha
  · obtain ⟨b, hb, hbe⟩ := Set.mem_smul_set.mp (w4_conj_tau_mem hw hg)
    simp only [smul_eq_mul] at hbe
    rw [← hbe, w4_tau_comm_V hc4 hb, mul_inv_cancel_right]
    exact hb

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
