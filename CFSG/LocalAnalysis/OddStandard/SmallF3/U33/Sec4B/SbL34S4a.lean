module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped commutatorElement
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


private theorem commutator_zpowers_eq_bot_of_comm {Q : Subgroup G} {s : G}
    (hs : ∀ q ∈ Q, s * q = q * s) : ⁅Q, zpowers s⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun q hq => (hs q hq).symm))

theorem CO_Q_le_V (hl : Ctx4L t L S x₁ x₂ lam rho tau) {o : G}
    (ho : o ∈ ctxO t tau x₁ x₂) (hcent : ∀ q ∈ ctxQ t tau x₁ x₂ rho, o * q = q * o) :
    o ∈ fourGrp x₁ x₂ := by
  classical
  obtain ⟨q, hq, s, hsT, hqs⟩ := O_decomp hl.toCtx4Q ho
  have hsCO : s ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hl.CO_rho]; exact hsT
  have hρs : rho * s = s * rho :=
    (Subgroup.mem_centralizer_singleton_iff.mp hsCO.2).symm
  have hVsq : ∀ v ∈ fourGrp x₁ x₂, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact (fourGrp_elemAbelian hl.toCtx4Q).2 v hv
  have hρV : ∀ v ∈ fourGrp x₁ x₂, rho * v * rho⁻¹ ∈ fourGrp x₁ x₂ :=
    fun v hv => hl.normal_V.2 rho hl.rho_mem_M v hv
  have hfix : ∀ q' ∈ ctxQ t tau x₁ x₂ rho, rho * q' = q' * rho → q' = 1 := by
    intro q' hq' hq'r
    have hmem : q' ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
      ⟨hq', Subgroup.mem_centralizer_singleton_iff.mpr hq'r.symm⟩
    rw [hl.CQ_rho] at hmem
    exact Subgroup.mem_bot.mp hmem
  set w : G := rho * q * rho⁻¹ * q⁻¹ with hwdef
  have hwQ : w ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hwdef]
    exact mul_mem (hl.normal_Q.2 rho hl.rho_mem_M q hq) (inv_mem hq)
  have hconj_s : rho * s * rho⁻¹ = s := by rw [hρs]; group
  have hconj_qs : rho * (q * s) * rho⁻¹ = (rho * q * rho⁻¹) * s := by
    calc rho * (q * s) * rho⁻¹
        = (rho * q * rho⁻¹) * (rho * s * rho⁻¹) := by group
      _ = (rho * q * rho⁻¹) * s := by rw [hconj_s]
  have hw_eq : w = (rho * o * rho⁻¹) * o⁻¹ := by
    rw [hwdef, hqs, hconj_qs]
    group
  have hcent_conj : ∀ q' ∈ ctxQ t tau x₁ x₂ rho,
      (rho * o * rho⁻¹) * q' = q' * (rho * o * rho⁻¹) := by
    intro q' hq'
    have hq'' : rho⁻¹ * q' * rho ∈ ctxQ t tau x₁ x₂ rho := by
      have h := hl.normal_Q.2 rho⁻¹ (inv_mem hl.rho_mem_M) q' hq'
      simpa using h
    have hcomm := hcent (rho⁻¹ * q' * rho) hq''
    calc (rho * o * rho⁻¹) * q'
        = rho * (o * (rho⁻¹ * q' * rho)) * rho⁻¹ := by group
      _ = rho * ((rho⁻¹ * q' * rho) * o) * rho⁻¹ := by rw [hcomm]
      _ = q' * (rho * o * rho⁻¹) := by group
  have hcent_inv : ∀ q' ∈ ctxQ t tau x₁ x₂ rho, o⁻¹ * q' = q' * o⁻¹ := by
    intro q' hq'
    calc o⁻¹ * q' = o⁻¹ * (q' * o) * o⁻¹ := by group
      _ = o⁻¹ * (o * q') * o⁻¹ := by rw [← hcent q' hq']
      _ = q' * o⁻¹ := by group
  have hw_cent : ∀ q' ∈ ctxQ t tau x₁ x₂ rho, q' * w = w * q' := by
    intro q' hq'
    rw [hw_eq]
    calc q' * ((rho * o * rho⁻¹) * o⁻¹)
        = (q' * (rho * o * rho⁻¹)) * o⁻¹ := by group
      _ = ((rho * o * rho⁻¹) * q') * o⁻¹ := by rw [← hcent_conj q' hq']
      _ = (rho * o * rho⁻¹) * (q' * o⁻¹) := by group
      _ = (rho * o * rho⁻¹) * (o⁻¹ * q') := by rw [← hcent_inv q' hq']
      _ = ((rho * o * rho⁻¹) * o⁻¹) * q' := by group
  have hwV : w ∈ fourGrp x₁ x₂ := by
    have hmem : w ∈ ctxQ t tau x₁ x₂ rho ⊓
        centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      ⟨hwQ, Subgroup.mem_centralizer_iff.mpr fun q' hq' => hw_cent q' hq'⟩
    rw [hl.Z_Q] at hmem
    exact hmem
  have hqV : q ∈ fourGrp x₁ x₂ := by
    by_contra hqV
    exact rho_conj_mul_inv_not_mem (ctxQ t tau x₁ x₂ rho) (fourGrp x₁ x₂) rho
      hl.V_le_Q hVsq hρV hfix hq hqV (hwdef ▸ hwV)
  have hs_eq : s = q⁻¹ * o := by rw [hqs]; group
  have hscent : ∀ q' ∈ ctxQ t tau x₁ x₂ rho, s * q' = q' * s := by
    intro q' hq'
    have hqinv_comm : q⁻¹ * q' = q' * q⁻¹ :=
      (V_comm_O hl.toCtx4Q (hl.Q_le_O hq') (inv_mem hqV)).symm
    calc s * q' = (q⁻¹ * o) * q' := by rw [hs_eq]
      _ = q⁻¹ * (o * q') := by group
      _ = q⁻¹ * (q' * o) := by rw [hcent q' hq']
      _ = (q⁻¹ * q') * o := by group
      _ = (q' * q⁻¹) * o := by rw [hqinv_comm]
      _ = q' * (q⁻¹ * o) := by group
      _ = q' * s := by rw [hs_eq]
  rcases (mem_T_iff hl.toCtx4Q).mp hsT with hs1 | hs1 | hs1 | hs1
  · rw [hqs, hs1, mul_one]
    exact hqV
  · exfalso
    have hcomm_bot : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = ⊥ :=
      commutator_zpowers_eq_bot_of_comm hscent
    have hcomm_V : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = fourGrp x₁ x₂ := by
      rw [hs1]; exact hl.comm_t
    have hcard : Nat.card (fourGrp x₁ x₂) = 1 := by
      rw [← hcomm_V, hcomm_bot, Subgroup.card_bot]
    rw [card_fourGrp hl.toCtx4Q] at hcard
    norm_num at hcard
  · exfalso
    have hcomm_bot : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = ⊥ :=
      commutator_zpowers_eq_bot_of_comm hscent
    have hcomm_V : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = fourGrp x₁ x₂ := by
      rw [hs1]; exact hl.comm_tau
    have hcard : Nat.card (fourGrp x₁ x₂) = 1 := by
      rw [← hcomm_V, hcomm_bot, Subgroup.card_bot]
    rw [card_fourGrp hl.toCtx4Q] at hcard
    norm_num at hcard
  · exfalso
    have hcomm_bot : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = ⊥ :=
      commutator_zpowers_eq_bot_of_comm hscent
    have hcomm_V : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = fourGrp x₁ x₂ := by
      rw [hs1]; exact hl.comm_ttau
    have hcard : Nat.card (fourGrp x₁ x₂) = 1 := by
      rw [← hcomm_V, hcomm_bot, Subgroup.card_bot]
    rw [card_fourGrp hl.toCtx4Q] at hcard
    norm_num at hcard

theorem CLO_Q_le_V (ha : Ctx4A t L S x₁ x₂ lam rho tau)
    (hQn : NormalIn (ctxQ t tau x₁ x₂ rho) (ctxLO t tau x₁ x₂)) {d : G}
    (hd : d ∈ ctxLO t tau x₁ x₂) (hcent : ∀ q ∈ ctxQ t tau x₁ x₂ rho, d * q = q * d) :
    d ∈ fourGrp x₁ x₂ := by
  clear hQn
  have hdO : d ∈ ctxO t tau x₁ x₂ := by
    apply ha.CL_Obar d hd
    intro o ho
    have hdoO : d * o * d⁻¹ ∈ ctxO t tau x₁ x₂ :=
      (Subgroup.mem_normalizer_iff.mp hd o).mp ho
    have hcO : d * o * d⁻¹ * o⁻¹ ∈ ctxO t tau x₁ x₂ :=
      mul_mem hdoO (inv_mem ho)
    refine CO_Q_le_V ha.toCtx4L hcO ?_
    intro q hq
    have hq₁Q : o⁻¹ * q * o ∈ ctxQ t tau x₁ x₂ rho := by
      have h := ha.normal_Q.2 o⁻¹ (inv_mem (ha.O_le_M ho)) q hq
      simpa using h
    have hdq₁ : d * (o⁻¹ * q * o) = (o⁻¹ * q * o) * d := hcent (o⁻¹ * q * o) hq₁Q
    have hdq₁' : d⁻¹ * (o⁻¹ * q * o) * d = o⁻¹ * q * o := by
      calc d⁻¹ * (o⁻¹ * q * o) * d
          = d⁻¹ * ((o⁻¹ * q * o) * d) := by group
        _ = d⁻¹ * (d * (o⁻¹ * q * o)) := by rw [← hdq₁]
        _ = o⁻¹ * q * o := by group
    have hcq_conj : (d * o * d⁻¹ * o⁻¹) * q * (d * o * d⁻¹ * o⁻¹)⁻¹ = q := by
      have hqeq : q = o * (o⁻¹ * q * o) * o⁻¹ := by group
      calc (d * o * d⁻¹ * o⁻¹) * q * (d * o * d⁻¹ * o⁻¹)⁻¹
          = (d * o * d⁻¹ * o⁻¹) * (o * (o⁻¹ * q * o) * o⁻¹) *
              (d * o * d⁻¹ * o⁻¹)⁻¹ := by
            conv_lhs => rw [hqeq]
        _ = d * o * (d⁻¹ * (o⁻¹ * q * o) * d) * o⁻¹ * d⁻¹ := by group
        _ = d * o * (o⁻¹ * q * o) * o⁻¹ * d⁻¹ := by rw [hdq₁']
        _ = d * q * d⁻¹ := by group
        _ = q := by rw [hcent q hq]; group
    have hcq : (d * o * d⁻¹ * o⁻¹) * q = q * (d * o * d⁻¹ * o⁻¹) := by
      have h := congrArg (fun x => x * (d * o * d⁻¹ * o⁻¹)) hcq_conj
      simpa [mul_assoc] using h
    exact hcq
  exact CO_Q_le_V ha.toCtx4L hdO hcent

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
