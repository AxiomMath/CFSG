module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2c1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem exists_BData (ha : Ctx4P t L S x₁ x₂ lam rho tau)
    (hQn : ¬ NormalIn (ctxQ t tau x₁ x₂ rho) (ctxLO t tau x₁ x₂)) :
    ∃ (B : Subgroup G) (ω : G), BData t x₁ x₂ lam rho tau B ω := by
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  obtain ⟨B, hVB, hBQ, hB16, hBP, hρB, hσB⟩ := exists_B ha hQn
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a :=
    abelian_of_rho_inv (ctxQ t tau x₁ x₂ rho) (fourGrp x₁ x₂) B rho hVB hBQ
      (card_fourGrp hc) (V_sq hc) (V_comm_Q hc) (Q_comm_V hc) (Q_sq_V hc)
      (rho_cubed hc) (rho_conj_Q hc) (rho_conj_V hc) (rho_fix_Q hc) hρB hB16
  have hρnt : ∃ v ∈ fourGrp x₁ x₂, rho * v ≠ v * rho := by
    by_contra h
    apply rho_not_mem_ctxPL ha.toCtx4A
    show rho ∈ ctxLO t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
    refine Subgroup.mem_inf.mpr ⟨rho_mem_LO ha.toCtx4A, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    by_contra hne
    exact h ⟨v, hv, fun h' => hne h'.symm⟩
  obtain ⟨d, hdD, hd1, hdc⟩ :=
    exists_cent_elem B (fourGrp x₁ x₂) (closure ({t, tau} : Set G)) rho (lam * t)
      (card_fourGrp hc) (V_sq hc) hVB hB16 hBab
      (fun b hb => Q_sq_V hc b (hBQ hb))
      (fun v hv b hb => V_comm_Q hc v hv b (hBQ hb))
      (card_T hc)
      (fun d hd v hv => V_comm_O hc (T_le_O hc hd) hv)
      (fun d hd b hb => by
        have h1 : b * d * b⁻¹ * d⁻¹ ∈ fourGrp x₁ x₂ :=
          comm_Q_O_mem_V hc (hBQ hb) (T_le_O hc hd)
        have h2 : (b * d * b⁻¹ * d⁻¹)⁻¹ ∈ fourGrp x₁ x₂ := Subgroup.inv_mem _ h1
        rwa [show (b * d * b⁻¹ * d⁻¹)⁻¹ = d * b * d⁻¹ * b⁻¹ by group] at h2)
      (rho_cubed hc) hρB (rho_conj_V hc)
      (fun d hd => rho_comm_T hc d hd)
      (fun b hb => rho_fix_Q hc b (hBQ hb))
      hρnt hσB
      (by rw [← t_comm_lam hc]; exact tlam_conj_rho hc)
      (fun b hb => by
        have hq2 : (lam * t) * (lam * t) = 1 := by
          rw [← t_comm_lam hc]; exact q_mul_self hc
        rw [hq2]
        rw [show (1 : G) * b * 1⁻¹ * b⁻¹ = 1 by group]
        exact Subgroup.one_mem _)
      (fun d hd => by
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        have hcomm : (lam * t) * d = d * (lam * t) := by
          rw [← t_comm_lam hc]
          exact T_comm_q ha.toCtx4L hd
        rw [hcomm]; group)
  refine ⟨B, d, ?_⟩
  exact { V_le := hVB, le_Q := hBQ, card := hB16, comm := hBab, P_comm := hBP,
          rho_mem := hρB, sig_mem := hσB, ω_mem := hdD, ω_ne := hd1, ω_comm := hdc }

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
