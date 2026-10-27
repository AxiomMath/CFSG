module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l18_C_normal (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    NormalIn (ctxCY t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho) := by
  refine ⟨inf_le_left, ?_⟩
  intro g hg k hk
  have hkK : k ∈ ctxK t tau x₁ x₂ rho := hk.1
  have hkC : k ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := hk.2
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (ctxK t tau x₁ x₂ rho).mul_mem
      ((ctxK t tau x₁ x₂ rho).mul_mem hg hkK) ((ctxK t tau x₁ x₂ rho).inv_mem hg)
  · refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    have hy' : g⁻¹ * y * g ∈ ctxYq t tau x₁ x₂ rho := by
      simpa using l17_K_normalizes_Y hc g⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem hg) y hy
    have hcomm : (g⁻¹ * y * g) * k = k * (g⁻¹ * y * g) :=
      Subgroup.mem_centralizer_iff.mp hkC _ hy'
    have hconj := congrArg (fun z => g * z * g⁻¹) hcomm
    have h1 : g * ((g⁻¹ * y * g) * k) * g⁻¹ = y * (g * k * g⁻¹) := by group
    have h2 : g * (k * (g⁻¹ * y * g)) * g⁻¹ = (g * k * g⁻¹) * y := by group
    rw [h1, h2] at hconj
    exact hconj

theorem l18_comm_mem_Y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {c q : G}
    (hcC : c ∈ ctxCY t tau x₁ x₂ rho) (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    c * q * c⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  have hcK : c ∈ ctxK t tau x₁ x₂ rho := hcC.1
  have hcCent : c ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := hcC.2
  have huQ : c * q * c⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hc.normal_Q_K.2 c hcK q hq
  have hdQ : c * q * c⁻¹ * q⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    (ctxQ t tau x₁ x₂ rho).mul_mem huQ ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
  rw [mem_ctxYq_iff hc.q_iso]
  refine ⟨hdQ, ?_⟩
  have hq2V : q ^ 2 ∈ fourGrp x₁ x₂ := l17_Q_sq_mem hc q hq
  have hq2Y : q ^ 2 ∈ ctxYq t tau x₁ x₂ rho := l17_V_le_Y hc hq2V
  have hc_q2 : c * q ^ 2 * c⁻¹ = q ^ 2 := by
    have hcomm := Subgroup.mem_centralizer_iff.mp hcCent (q ^ 2) hq2Y
    rw [← hcomm]; group
  have hu2 : (c * q * c⁻¹) * (c * q * c⁻¹) = q ^ 2 := by
    calc (c * q * c⁻¹) * (c * q * c⁻¹) = c * (q * q) * c⁻¹ := by group
      _ = c * q ^ 2 * c⁻¹ := by rw [pow_two]
      _ = q ^ 2 := hc_q2
  have hcommQ : q⁻¹ * (c * q * c⁻¹) = (c * q * c⁻¹) * q⁻¹ :=
    IsZ4Z4E4.comm hc.q_iso ((ctxQ t tau x₁ x₂ rho).inv_mem hq) huQ
  have hsq : (c * q * c⁻¹ * q⁻¹) * (c * q * c⁻¹ * q⁻¹) = 1 := by
    calc (c * q * c⁻¹ * q⁻¹) * (c * q * c⁻¹ * q⁻¹)
        = (c * q * c⁻¹) * (q⁻¹ * (c * q * c⁻¹)) * q⁻¹ := by group
      _ = (c * q * c⁻¹) * ((c * q * c⁻¹) * q⁻¹) * q⁻¹ := by rw [hcommQ]
      _ = (c * q * c⁻¹) * (c * q * c⁻¹) * q⁻¹ * q⁻¹ := by group
      _ = q ^ 2 * q⁻¹ * q⁻¹ := by rw [hu2]
      _ = 1 := by group
  simpa [pow_two] using hsq

theorem l18_rho_not_mem_C (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    rho ∉ ctxCY t tau x₁ x₂ rho := by
  intro hrho
  have hx1sqV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx1sqY : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := l17_V_le_Y hc hx1sqV
  have hx1sqQ : x₁ ^ 2 ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hx1sqY
  have hx1sqP : x₁ ^ 2 ∈ ctxP t tau x₁ x₂ rho := by
    refine ⟨hc.normal_Q_K.1 hx1sqQ, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun a ha => IsZ4Z4E4.comm hc.q_iso ha hx1sqQ)
  have hcomm : x₁ ^ 2 * rho = rho * x₁ ^ 2 :=
    Subgroup.mem_centralizer_iff.mp hrho.2 (x₁ ^ 2) hx1sqY
  exact (l17_yz_ne hc).1 (l17_CP_rho hc (x₁ ^ 2) hx1sqP hcomm)

theorem l18_C_pgroup (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    IsPGroup 2 (ctxCY t tau x₁ x₂ rho) := by
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  have hρ1 : rho ≠ 1 := by
    intro h
    have hord : orderOf rho = 3 := hc.ord_rho
    rw [h, orderOf_one] at hord
    norm_num at hord
  exact isPGroup_two_of_normal (n := 12) hc.card_K inf_le_left (l18_C_normal hc).2 hρK hρ3
    hρ1 (l18_rho_not_mem_C hc)

theorem l18_C_le_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxCY t tau x₁ x₂ rho ≤ ctxOK t tau x₁ x₂ rho :=
  l18_le_OK (l18_C_normal hc) (l18_C_pgroup hc)

theorem l18_QA_le_C (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om} ≤ ctxCY t tau x₁ x₂ rho := by
  refine sup_le (fun q hq => ⟨hc.normal_Q_K.1 hq, ?_⟩) ?_
  · exact Subgroup.mem_centralizer_iff.mpr
      (fun y hy => IsZ4Z4E4.comm hc.q_iso (ctxYq_le_ctxQ hy) hq)
  · rw [Subgroup.closure_le]
    rintro x (hx : x ∈ ({tau, om} : Set G))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨(l17_mem_K hc).2.1,
        Subgroup.mem_centralizer_iff.mpr (fun a ha => (hc.tau_cent_Y a ha).symm)⟩
    · exact ⟨(l17_mem_K hc).2.2.1,
        Subgroup.mem_centralizer_iff.mpr (fun a ha => (hc.om_cent_Y a ha).symm)⟩

private lemma l18_conj_eq_conj (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {c c' q : G}
    (h1 : c ∈ ctxCY t tau x₁ x₂ rho) (h2 : c' ∈ ctxCY t tau x₁ x₂ rho)
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    c * c' * q * (c * c')⁻¹ = c' * c * q * (c' * c)⁻¹ := by
  have hδ : c * q * c⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho := l18_comm_mem_Y hc h1 hq
  have hδ' : c' * q * c'⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho := l18_comm_mem_Y hc h2 hq
  have hcq : c * q * c⁻¹ = (c * q * c⁻¹ * q⁻¹) * q := by group
  have hc'q : c' * q * c'⁻¹ = (c' * q * c'⁻¹ * q⁻¹) * q := by group
  have hcδ : c * (c * q * c⁻¹ * q⁻¹) * c⁻¹ = c * q * c⁻¹ * q⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.mp h1.2 (c * q * c⁻¹ * q⁻¹) hδ
    rw [← h]; group
  have hc'δ' : c' * (c' * q * c'⁻¹ * q⁻¹) * c'⁻¹ = c' * q * c'⁻¹ * q⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.mp h2.2 (c' * q * c'⁻¹ * q⁻¹) hδ'
    rw [← h]; group
  have hcδ' : c * (c' * q * c'⁻¹ * q⁻¹) * c⁻¹ = c' * q * c'⁻¹ * q⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.mp h1.2 (c' * q * c'⁻¹ * q⁻¹) hδ'
    rw [← h]; group
  have hc'δ : c' * (c * q * c⁻¹ * q⁻¹) * c'⁻¹ = c * q * c⁻¹ * q⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.mp h2.2 (c * q * c⁻¹ * q⁻¹) hδ
    rw [← h]; group
  have hcomm : (c' * q * c'⁻¹ * q⁻¹) * (c * q * c⁻¹ * q⁻¹) =
      (c * q * c⁻¹ * q⁻¹) * (c' * q * c'⁻¹ * q⁻¹) :=
    IsZ4Z4E4.comm hc.q_iso (ctxYq_le_ctxQ hδ') (ctxYq_le_ctxQ hδ)
  have ha : c * c' * q * (c * c')⁻¹ =
      (c' * q * c'⁻¹ * q⁻¹) * (c * q * c⁻¹ * q⁻¹) * q := by
    calc c * c' * q * (c * c')⁻¹
        = c * (c' * q * c'⁻¹) * c⁻¹ := by group
      _ = c * ((c' * q * c'⁻¹ * q⁻¹) * q) * c⁻¹ := by conv_lhs => rw [hc'q]
      _ = (c * (c' * q * c'⁻¹ * q⁻¹) * c⁻¹) * (c * q * c⁻¹) := by group
      _ = (c' * q * c'⁻¹ * q⁻¹) * ((c * q * c⁻¹ * q⁻¹) * q) := by
            conv_lhs => rw [hcδ', hcq]
      _ = (c' * q * c'⁻¹ * q⁻¹) * (c * q * c⁻¹ * q⁻¹) * q := by group
  have hb : c' * c * q * (c' * c)⁻¹ =
      (c * q * c⁻¹ * q⁻¹) * (c' * q * c'⁻¹ * q⁻¹) * q := by
    calc c' * c * q * (c' * c)⁻¹
        = c' * (c * q * c⁻¹) * c'⁻¹ := by group
      _ = c' * ((c * q * c⁻¹ * q⁻¹) * q) * c'⁻¹ := by conv_lhs => rw [hcq]
      _ = (c' * (c * q * c⁻¹ * q⁻¹) * c'⁻¹) * (c' * q * c'⁻¹) := by group
      _ = (c * q * c⁻¹ * q⁻¹) * ((c' * q * c'⁻¹ * q⁻¹) * q) := by
            conv_lhs => rw [hc'δ, hc'q]
      _ = (c * q * c⁻¹ * q⁻¹) * (c' * q * c'⁻¹ * q⁻¹) * q := by group
  rw [ha, hb, hcomm]

theorem l18_comm_mem_Q (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) {c c' : G}
    (h1 : c ∈ ctxCY t tau x₁ x₂ rho) (h2 : c' ∈ ctxCY t tau x₁ x₂ rho) :
    c * c' * c⁻¹ * c'⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  have hcK : c ∈ ctxK t tau x₁ x₂ rho := h1.1
  have hc'K : c' ∈ ctxK t tau x₁ x₂ rho := h2.1
  have haq : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      (c * c') * q * (c * c')⁻¹ = (c' * c) * q * (c' * c)⁻¹ :=
    fun q hq => l18_conj_eq_conj hc13 h1 h2 hq
  have hwK : c * c' * c⁻¹ * c'⁻¹ ∈ ctxK t tau x₁ x₂ rho := by
    have h1' : c * c' * c⁻¹ * c'⁻¹ = (c * c') * (c' * c)⁻¹ := by group
    rw [h1']
    exact (ctxK t tau x₁ x₂ rho).mul_mem ((ctxK t tau x₁ x₂ rho).mul_mem hcK hc'K)
      ((ctxK t tau x₁ x₂ rho).inv_mem ((ctxK t tau x₁ x₂ rho).mul_mem hc'K hcK))
  have hwCent : c * c' * c⁻¹ * c'⁻¹ ∈
      centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr (fun q hq => ?_)
    have hbq : c' * c ∈ ctxK t tau x₁ x₂ rho :=
      (ctxK t tau x₁ x₂ rho).mul_mem hc'K hcK
    have hq1 : (c' * c)⁻¹ * q * (c' * c) ∈ ctxQ t tau x₁ x₂ rho := by
      simpa using hc13.normal_Q_K.2 (c' * c)⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem hbq) q hq
    have hconj : (c * c' * c⁻¹ * c'⁻¹) * q * (c * c' * c⁻¹ * c'⁻¹)⁻¹ = q := by
      have e1 : (c * c' * c⁻¹ * c'⁻¹) * q * (c * c' * c⁻¹ * c'⁻¹)⁻¹ =
          (c * c') * ((c' * c)⁻¹ * q * (c' * c)) * (c * c')⁻¹ := by group
      rw [e1, haq ((c' * c)⁻¹ * q * (c' * c)) hq1]
      group
    have hwq : (c * c' * c⁻¹ * c'⁻¹) * q = q * (c * c' * c⁻¹ * c'⁻¹) := by
      have := congrArg (fun x => x * (c * c' * c⁻¹ * c'⁻¹)) hconj
      simpa [mul_assoc] using this
    exact hwq.symm
  have hwP : c * c' * c⁻¹ * c'⁻¹ ∈ ctxP t tau x₁ x₂ rho := ⟨hwK, hwCent⟩
  rw [hc.P_eq] at hwP
  exact hwP

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
