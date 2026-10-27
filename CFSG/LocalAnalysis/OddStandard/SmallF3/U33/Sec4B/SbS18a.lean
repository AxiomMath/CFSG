module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC18
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Grp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l18_OK_normal :
    NormalIn (ctxOK t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho) := by
  unfold ctxOK
  constructor
  · exact CFSG.LieType.BorelTits.pCoreOf_le 2 (ctxK t tau x₁ x₂ rho)
  · intro g hg k hk
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (ctxK t tau x₁ x₂ rho) hg) k).mp hk

theorem l18_OK_pgroup : IsPGroup 2 (ctxOK t tau x₁ x₂ rho) := by
  unfold ctxOK
  exact isPGroup_pCoreOf (ctxK t tau x₁ x₂ rho)

theorem l18_le_OK {N : Subgroup G} (hN : NormalIn N (ctxK t tau x₁ x₂ rho))
    (h2 : IsPGroup 2 N) : N ≤ ctxOK t tau x₁ x₂ rho := by
  have hnorm : ctxK t tau x₁ x₂ rho ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hN.2 g hg n hn
    · intro hn
      have h := hN.2 g⁻¹ (inv_mem hg) (g * n * g⁻¹) hn
      have heq : g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n := by group
      rwa [heq] at h
  unfold ctxOK
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN.1 hnorm h2

theorem l18_OK_le_sylow (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxOK t tau x₁ x₂ rho ≤ 𝒮 := by
  exact le_of_normal_isPGroup (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂)
      (rho := rho)).1
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).2
    (l18_OK_pgroup (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho))
    hc.sylow.1 hc.sylow.2.1 hc.sylow.2.2

theorem l18_R_le_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau} ≤ ctxOK t tau x₁ x₂ rho := by
  set R : Subgroup G := ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) with hR
  have hcardR : Nat.card R = 2 ^ 8 := by
    rw [hR, ← l17_R_eq hc]
    exact hc.card_R
  have hpR : IsPGroup 2 R := IsPGroup.of_card (n := 8) hcardR
  change R ≤ CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ hpR
  · rw [hR]
    exact Subgroup.le_normalizer
  · unfold ctxK
    rw [hR]

theorem l18_rho_not_mem_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    rho ∉ ctxOK t tau x₁ x₂ rho := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hrho
  have hne : (⟨rho, hrho⟩ : ↥(ctxOK t tau x₁ x₂ rho)) ≠ 1 := by
    intro h
    have h1 : orderOf (⟨rho, hrho⟩ : ↥(ctxOK t tau x₁ x₂ rho)) = 1 := by
      rw [h, orderOf_one]
    rw [Subgroup.orderOf_mk, hc.ord_rho] at h1
    norm_num at h1
  have hdvd : 2 ∣ orderOf (⟨rho, hrho⟩ : ↥(ctxOK t tau x₁ x₂ rho)) :=
    (l18_OK_pgroup (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).dvd_orderOf hne
  rw [Subgroup.orderOf_mk, hc.ord_rho] at hdvd
  norm_num at hdvd

theorem l18_lam_not_mem_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    lam ∉ ctxOK t tau x₁ x₂ rho := by
  intro hlam
  have hrhoK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
  have hconj : rho * lam * rho⁻¹ ∈ ctxOK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).2
      rho hrhoK lam hlam
  have hcomm : rho * lam * rho⁻¹ * lam⁻¹ ∈ ctxOK t tau x₁ x₂ rho :=
    mul_mem hconj (inv_mem hlam)
  have heq : rho * lam * rho⁻¹ * lam⁻¹ = rho ^ 2 := by
    have h1 : lam * rho⁻¹ * lam⁻¹ = rho := by
      calc lam * rho⁻¹ * lam⁻¹ = (lam * rho * lam⁻¹)⁻¹ := by group
        _ = (rho⁻¹)⁻¹ := by rw [hc.lam_rho]
        _ = rho := by rw [inv_inv]
    calc rho * lam * rho⁻¹ * lam⁻¹ = rho * (lam * rho⁻¹ * lam⁻¹) := by group
      _ = rho * rho := by rw [h1]
      _ = rho ^ 2 := by rw [pow_two]
  rw [heq] at hcomm
  have hrho2 : rho ∈ ctxOK t tau x₁ x₂ rho := by
    have h3 : rho ^ 3 = 1 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
    have hrho4 : (rho ^ 2) ^ 2 = rho := by
      calc (rho ^ 2) ^ 2 = rho ^ (2 * 2) := (pow_mul rho 2 2).symm
        _ = rho ^ 4 := by norm_num
        _ = rho ^ 3 * rho := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
        _ = 1 * rho := by rw [h3]
        _ = rho := one_mul rho
    have h4 : (rho ^ 2) ^ 2 ∈ ctxOK t tau x₁ x₂ rho := pow_mem hcomm 2
    rwa [hrho4] at h4
  exact l18_rho_not_mem_OK hc hrho2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
