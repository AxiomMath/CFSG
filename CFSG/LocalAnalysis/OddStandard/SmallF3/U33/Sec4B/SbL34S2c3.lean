module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2c1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2c2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem CQ_type_of {s : G} (hsO : s ∈ ctxO t tau x₁ x₂) (hρs : rho * s = s * rho)
    (hcard : Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G) : Subgroup G) = 2 ^ 4) :
    IsZ4Z4Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G)) ∨
      IsE16Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G)) := by
  have hB : Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G) : Subgroup G) = 16 :=
    hcard.trans (by norm_num)
  have hVB : fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G) := by
    intro v hv
    exact ⟨hc.V_le_Q hv, Subgroup.mem_centralizer_singleton_iff.mpr (V_comm_O hc hsO hv).symm⟩
  have hBQ : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G) ≤ ctxQ t tau x₁ x₂ rho :=
    inf_le_left
  have hVcard : Nat.card (fourGrp x₁ x₂) = 4 := card_fourGrp hc
  have hVsq : ∀ v ∈ fourGrp x₁ x₂, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact (fourGrp_elemAbelian hc).2 v hv
  have hVc : ∀ v ∈ fourGrp x₁ x₂, ∀ q ∈ ctxQ t tau x₁ x₂ rho, v * q = q * v :=
    fun v hv q hq => (V_comm_O hc (hc.Q_le_O hq) hv).symm
  have hQc : ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho,
      a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := hc.Q_quot.2
  have hQs : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a * a ∈ fourGrp x₁ x₂ := fun a ha => by
    rw [← pow_two]
    exact hc.Q_quot.1 a ha
  have hρ3 : rho * rho * rho = 1 := by
    have h := pow_orderOf_eq_one rho
    rw [hc.ord_rho] at h
    rw [← pow_two, ← pow_succ]
    exact h
  have hρQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, rho * q * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun q hq => hc.normal_Q.2 rho hc.rho_mem_M q hq
  have hρV : ∀ v ∈ fourGrp x₁ x₂, rho * v * rho⁻¹ ∈ fourGrp x₁ x₂ :=
    fun v hv => hc.normal_V.2 rho hc.rho_mem_M v hv
  have hfix : ∀ q ∈ ctxQ t tau x₁ x₂ rho, rho * q = q * rho → q = 1 := by
    intro q hq hqr
    have hmem : q ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
      ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hqr.symm⟩
    rw [hc.CQ_rho] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hρs' : rho⁻¹ * s = s * rho⁻¹ := by
    calc rho⁻¹ * s = rho⁻¹ * (s * rho) * rho⁻¹ := by group
      _ = rho⁻¹ * (rho * s) * rho⁻¹ := by rw [hρs]
      _ = s * rho⁻¹ := by group
  have hρB : ∀ b ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G),
      rho * b * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G) := by
    intro b hb
    refine ⟨hρQ b hb.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hbs : b * s = s * b := Subgroup.mem_centralizer_singleton_iff.mp hb.2
    calc rho * b * rho⁻¹ * s = rho * (b * (rho⁻¹ * s)) := by group
      _ = rho * (b * (s * rho⁻¹)) := by rw [hρs']
      _ = rho * ((b * s) * rho⁻¹) := by group
      _ = rho * ((s * b) * rho⁻¹) := by rw [hbs]
      _ = (rho * s) * (b * rho⁻¹) := by group
      _ = (s * rho) * (b * rho⁻¹) := by rw [hρs]
      _ = s * (rho * b * rho⁻¹) := by group
  have hab := abelian_of_rho_inv (ctxQ t tau x₁ x₂ rho) (fourGrp x₁ x₂)
    (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G)) rho hVB hBQ hVcard hVsq hVc hQc hQs hρ3
    hρQ hρV hfix hρB hB
  exact isE16_or_isZ4Z4_of_abelian (ctxQ t tau x₁ x₂ rho) (fourGrp x₁ x₂)
    (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({s} : Set G)) rho hVB hBQ hVcard hVsq hQs hρ3 hfix
    hρB hB hab

theorem CQ_tau_type_holds :
    IsZ4Z4Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G)) ∨
      IsE16Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G)) :=
  CQ_type_of hc hc.tau_mem_O hc.rho_comm_tau (card_CQ_tau hc)

theorem CQ_ttau_type_holds :
    IsZ4Z4Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) ∨
      IsE16Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) :=
  CQ_type_of hc (mul_mem hc.t_mem_O hc.tau_mem_O)
    (s_facts hc (Or.inr (Or.inr rfl))).2.2.2.1 (card_CQ_ttau hc)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
