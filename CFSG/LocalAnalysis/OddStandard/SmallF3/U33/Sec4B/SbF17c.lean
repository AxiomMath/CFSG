module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Grp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l17_P_normal (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    NormalIn (ctxP t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho) := by
  refine ⟨inf_le_left, ?_⟩
  intro g hg k hk
  have hkK : k ∈ ctxK t tau x₁ x₂ rho := hk.1
  have hkC : k ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := hk.2
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (ctxK t tau x₁ x₂ rho).mul_mem
      ((ctxK t tau x₁ x₂ rho).mul_mem hg hkK) ((ctxK t tau x₁ x₂ rho).inv_mem hg)
  · refine Subgroup.mem_centralizer_iff.mpr (fun q hq => ?_)
    have hq' : g⁻¹ * q * g ∈ ctxQ t tau x₁ x₂ rho := by
      simpa using hc.normal_Q_K.2 g⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem hg) q hq
    have hcomm : (g⁻¹ * q * g) * k = k * (g⁻¹ * q * g) :=
      Subgroup.mem_centralizer_iff.mp hkC _ hq'
    have hconj := congrArg (fun y => g * y * g⁻¹) hcomm
    have h1 : g * ((g⁻¹ * q * g) * k) * g⁻¹ = q * (g * k * g⁻¹) := by group
    have h2 : g * (k * (g⁻¹ * q * g)) * g⁻¹ = (g * k * g⁻¹) * q := by group
    rw [h1, h2] at hconj
    exact hconj

theorem l17_Q_le_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ≤ ctxP t tau x₁ x₂ rho := by
  intro q hq
  refine ⟨hc.normal_Q_K.1 hq, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr (fun a ha => IsZ4Z4E4.comm hc.q_iso ha hq)

theorem l17_P_cent_Y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ p ∈ ctxP t tau x₁ x₂ rho, ∀ a ∈ ctxYq t tau x₁ x₂ rho, p * a = a * p := by
  intro p hp a ha
  have hpC : p ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := hp.2
  have hcomm : a * p = p * a :=
    Subgroup.mem_centralizer_iff.mp hpC a (ctxYq_le_ctxQ ha)
  exact hcomm.symm

theorem l17_rho_not_mem_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    rho ∉ ctxP t tau x₁ x₂ rho := by
  intro hρ
  have hρC : rho ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := hρ.2
  have hQle : ctxQ t tau x₁ x₂ rho ≤ ctxCO t tau x₁ x₂ rho := by
    intro q hq
    refine ⟨l17_Q_le_O hc hq, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr (fun a ha => ?_)
    have hcomm : q * rho = rho * q :=
      Subgroup.mem_centralizer_iff.mp hρC q hq
    simpa [Set.mem_singleton_iff.mp ha] using hcomm.symm
  have hcard : Nat.card (ctxQ t tau x₁ x₂ rho) ≤ 8 := by
    calc Nat.card (ctxQ t tau x₁ x₂ rho) ≤ Nat.card (ctxCO t tau x₁ x₂ rho) :=
          Subgroup.card_le_of_le hQle
      _ = Nat.card ↥(closure ({t, om} : Set G)) := by rw [hc.CO_eq]
      _ = 8 := (ctx13_T_facts hc).2.2
  rw [IsZ4Z4E4.card hc.q_iso] at hcard
  omega

theorem l17_P_pgroup (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    IsPGroup 2 (ctxP t tau x₁ x₂ rho) := by
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  have hρ1 : rho ≠ 1 := by
    intro h
    have hord : orderOf rho = 3 := hc.ord_rho
    rw [h, orderOf_one] at hord
    norm_num at hord
  exact isPGroup_two_of_normal (n := 12) hc.card_K inf_le_left (l17_P_normal hc).2 hρK hρ3 hρ1
    (l17_rho_not_mem_P hc)

theorem l17_P_le_sylow (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxP t tau x₁ x₂ rho ≤ 𝒮 := by
  exact le_of_normal_isPGroup inf_le_left (l17_P_normal hc.toCtx13).2 (l17_P_pgroup hc.toCtx13)
    hc.sylow.1 hc.sylow.2.1 hc.sylow.2.2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
