module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3c1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section Basic

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem rho_cubed : rho * rho * rho = 1 := by
  have h := pow_orderOf_eq_one rho
  rw [hc.ord_rho] at h
  rw [← pow_two, ← pow_succ]
  exact h

theorem rho_conj_Q : ∀ q ∈ ctxQ t tau x₁ x₂ rho, rho * q * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
  fun q hq => hc.normal_Q.2 rho hc.rho_mem_M q hq

theorem rho_conj_V : ∀ v ∈ fourGrp x₁ x₂, rho * v * rho⁻¹ ∈ fourGrp x₁ x₂ :=
  fun v hv => hc.normal_V.2 rho hc.rho_mem_M v hv

theorem rho_conj_O : ∀ o ∈ ctxO t tau x₁ x₂, rho * o * rho⁻¹ ∈ ctxO t tau x₁ x₂ :=
  fun o ho => (O_normal_M t tau x₁ x₂).2 rho hc.rho_mem_M o ho

theorem rho_fix_Q : ∀ q ∈ ctxQ t tau x₁ x₂ rho, rho * q = q * rho → q = 1 := by
  intro q hq hqr
  have hmem : q ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
    ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hqr.symm⟩
  rw [hc.CQ_rho] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem V_sq : ∀ v ∈ fourGrp x₁ x₂, v * v = 1 := fun v hv => by
  rw [← pow_two]
  exact (fourGrp_elemAbelian hc).2 v hv

theorem V_comm_Q : ∀ v ∈ fourGrp x₁ x₂, ∀ q ∈ ctxQ t tau x₁ x₂ rho, v * q = q * v :=
  fun v hv q hq => (V_comm_O hc (hc.Q_le_O hq) hv).symm

theorem Q_comm_V : ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho,
    a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := hc.Q_quot.2

theorem Q_sq_V : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a * a ∈ fourGrp x₁ x₂ := fun a ha => by
  rw [← pow_two]
  exact hc.Q_quot.1 a ha

theorem rho_comm_T : ∀ d ∈ closure ({t, tau} : Set G), rho * d = d * rho := by
  intro d hd
  rcases (mem_T_iff hc).mp hd with rfl | h | h | h
  · simp
  · exact (s_facts hc (Or.inl h)).2.2.2.1
  · exact (s_facts hc (Or.inr (Or.inl h))).2.2.2.1
  · exact (s_facts hc (Or.inr (Or.inr h))).2.2.2.1

theorem T_sq : ∀ d ∈ closure ({t, tau} : Set G), d * d = 1 := by
  intro d hd
  rcases (mem_T_iff hc).mp hd with rfl | h | h | h
  · simp
  · exact (s_facts hc (Or.inl h)).1
  · exact (s_facts hc (Or.inr (Or.inl h))).1
  · exact (s_facts hc (Or.inr (Or.inr h))).1

theorem T_comm : ∀ d ∈ closure ({t, tau} : Set G), ∀ e ∈ closure ({t, tau} : Set G),
    d * e = e * d := by
  intro d hd e he
  rcases (mem_T_iff hc).mp hd with rfl | h | h | h
  · simp
  · exact (s_facts hc (Or.inl h)).2.2.1 e he
  · exact (s_facts hc (Or.inr (Or.inl h))).2.2.1 e he
  · exact (s_facts hc (Or.inr (Or.inr h))).2.2.1 e he

theorem fix_mod_V : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
    rho * q * rho⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂ → q ∈ fourGrp x₁ x₂ := by
  intro q hq hmem
  by_contra hqV
  exact rho_conj_mul_inv_not_mem (ctxQ t tau x₁ x₂ rho) (fourGrp x₁ x₂) rho hc.V_le_Q
    (V_sq hc) (rho_conj_V hc) (rho_fix_Q hc) hq hqV hmem

end Basic

section PBasic

variable (ha : Ctx4P t L S x₁ x₂ lam rho tau)
include ha

theorem P_le_LO : ctxPL t tau x₁ x₂ ≤ ctxLO t tau x₁ x₂ := (normal_ctxPL ha.toCtx4A).1

theorem V_le_P : fourGrp x₁ x₂ ≤ ctxPL t tau x₁ x₂ :=
  (V_le_O ha.toCtx4L.toCtx4Q).trans (O_le_ctxPL ha.toCtx4A)

theorem P_comm_V : ∀ p ∈ ctxPL t tau x₁ x₂, ∀ v ∈ fourGrp x₁ x₂, p * v = v * p := by
  intro p hp v hv
  have hC : p ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hp).2
  exact (Subgroup.mem_centralizer_iff.mp hC v hv).symm

theorem LO_conj_P : ∀ g ∈ ctxLO t tau x₁ x₂, ∀ p ∈ ctxPL t tau x₁ x₂,
    g * p * g⁻¹ ∈ ctxPL t tau x₁ x₂ := (normal_ctxPL ha.toCtx4A).2

theorem LO_conj_V : ∀ g ∈ ctxLO t tau x₁ x₂, ∀ v ∈ fourGrp x₁ x₂,
    g * v * g⁻¹ ∈ fourGrp x₁ x₂ := fun g hg v hv =>
  conj_V_of_mem_LO ha.toCtx4L.toCtx4Q (isSylSL34_of_Ctx4L ha.toCtx4L) hg hv

theorem sig_conj_Q : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
    (lam * t) * q * (lam * t)⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  intro q hq
  have h := q_conj_Q ha.toCtx4L hq
  rwa [t_comm_lam ha.toCtx4L.toCtx4Q] at h

end PBasic

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
