module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0f1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0f1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section StepA

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem lam_mem_U : lam ∈ ctxU t tau x₁ x₂ lam :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)

theorem lam_conj_O {a : G} (ha : a ∈ ctxO t tau x₁ x₂) : lam * a * lam⁻¹ ∈ ctxO t tau x₁ x₂ :=
  (O_normal_M t tau x₁ x₂).2 lam hc.lam_mem_M a ha

theorem normal_V_U : NormalIn (fourGrp x₁ x₂) (ctxU t tau x₁ x₂ lam) :=
  ⟨(V_le_O hc).trans (O_le_U hc), fun g hg k hk => hc.normal_V.2 g (U_le_M hc hg) k hk⟩

theorem U_decomp {u : G} (hu : u ∈ ctxU t tau x₁ x₂ lam) :
    u ∈ ctxO t tau x₁ x₂ ∨ ∃ a ∈ ctxO t tau x₁ x₂, u = a * lam := by
  let H : Subgroup G :=
    { carrier := {u : G | u ∈ ctxO t tau x₁ x₂ ∨ ∃ a ∈ ctxO t tau x₁ x₂, u = a * lam}
      one_mem' := Or.inl (one_mem (ctxO t tau x₁ x₂))
      mul_mem' := by
        rintro u v (hu | ⟨a, ha, rfl⟩) (hv | ⟨b, hb, rfl⟩)
        · exact Or.inl (mul_mem hu hv)
        · exact Or.inr ⟨u * b, mul_mem hu hb, by group⟩
        · refine Or.inr ⟨a * (lam * v * lam⁻¹), mul_mem ha (lam_conj_O hc hv), by group⟩
        · refine Or.inl ?_
          have heq : (a * lam) * (b * lam) = a * (lam * b * lam⁻¹) := by
            rw [show (a * lam) * (b * lam) = a * (lam * b * lam⁻¹) * (lam * lam) by group,
              lam_mul_self hc, mul_one]
          rw [heq]
          exact mul_mem ha (lam_conj_O hc hb)
      inv_mem' := by
        rintro u (hu | ⟨a, ha, rfl⟩)
        · exact Or.inl (inv_mem hu)
        · have hlam : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (lam_mul_self hc)
          have h2 : lam * a⁻¹ * lam⁻¹ * lam = lam * a⁻¹ := by
            rw [show lam * a⁻¹ * lam⁻¹ * lam = lam * a⁻¹ * (lam⁻¹ * lam) by group,
              inv_mul_cancel, mul_one]
          refine Or.inr ⟨lam * a⁻¹ * lam⁻¹, lam_conj_O hc (inv_mem ha), ?_⟩
          rw [mul_inv_rev, h2, hlam] }
  have hle : ctxU t tau x₁ x₂ lam ≤ H := by
    rw [ctxU]
    exact sup_le (fun a ha => Or.inl ha)
      (Subgroup.zpowers_le.mpr (Or.inr ⟨1, one_mem _, (one_mul lam).symm⟩))
  exact hle hu

theorem gamma3_le_V :
    ⁅⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆, ctxU t tau x₁ x₂ lam⁆ ≤ fourGrp x₁ x₂ :=
  gamma3_le_of_index_two (normal_V_U hc) (O_le_U hc) (lam_mem_U hc)
    (by rw [lam_mul_self hc]; exact one_mem _) (fun a ha b hb => O_comm_le hc ha hb)
    (fun a ha => O_sq_mem_V hc ha) (fun a ha => lam_conj_O hc ha) (fun h hh => U_decomp hc hh)

end StepA

section StepB

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem x₁_mem_Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q (subset_closure (by simp))

theorem x₂_mem_Q : x₂ ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q (subset_closure (by simp))

theorem a_mem_comm_U : x₂ * x₁⁻¹ ∈ ⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆ := by
  have hx₁ : x₁ ∈ ctxU t tau x₁ x₂ lam := O_le_U hc (hc.Q_le_O (x₁_mem_Q hc))
  have h := Subgroup.commutator_mem_commutator (lam_mem_U hc) hx₁
  rwa [commutatorElement_def, hc.wreath.conj_x₁] at h

theorem a_mem_Q : x₂ * x₁⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
  mul_mem (x₂_mem_Q hc) (inv_mem (x₁_mem_Q hc))

theorem a_not_mem_V : x₂ * x₁⁻¹ ∉ fourGrp x₁ x₂ := by
  intro ha
  have hsqa : (x₂ * x₁⁻¹) ^ 2 = 1 := (fourGrp_elemAbelian hc).2 (x₂ * x₁⁻¹) ha
  have hcomm : Commute x₂ x₁⁻¹ := (show Commute x₂ x₁ from hc.x₁_comm_x₂.symm).inv_right
  have h2 : x₂ ^ 2 * (x₁ ^ 2)⁻¹ = 1 := by
    rw [Commute.mul_pow hcomm, inv_pow] at hsqa
    exact hsqa
  exact hc.y_ne_x₂_sq (mul_inv_eq_one.mp h2).symm

theorem V_le_gamma3 (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) :
    fourGrp x₁ x₂ ≤ ⁅⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆, ctxU t tau x₁ x₂ lam⁆ := by
  intro c hcV
  obtain ⟨w, hwQ, hw⟩ := pairing_Q hc hs (a_mem_Q hc) (a_not_mem_V hc) hcV
  have hwU : w ∈ ctxU t tau x₁ x₂ lam := O_le_U hc (hc.Q_le_O hwQ)
  have h := Subgroup.commutator_mem_commutator (a_mem_comm_U hc) hwU
  rwa [commutatorElement_def, hw] at h

theorem gamma3_eq_V (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) :
    ⁅⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆, ctxU t tau x₁ x₂ lam⁆ = fourGrp x₁ x₂ :=
  le_antisymm (gamma3_le_V hc) (V_le_gamma3 hc hs)

theorem char_V (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) :
    CharIn (fourGrp x₁ x₂) (ctxU t tau x₁ x₂ lam) := by
  have h := charIn_commutator3 (ctxU t tau x₁ x₂ lam)
  rwa [gamma3_eq_V hc hs] at h

end StepB

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
