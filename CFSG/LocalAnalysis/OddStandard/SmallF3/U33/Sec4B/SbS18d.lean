module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC18
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17Y

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l18_T_le_sylow (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    t ∈ 𝒮 ∧ tau ∈ 𝒮 ∧ om ∈ 𝒮 ∧ lam ∈ 𝒮 := by
  obtain ⟨htO, htauO, homO⟩ := l17_mem_O hc.toCtx13
  have hO : ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam := le_sup_left
  have hlamU : lam ∈ ctxU t tau x₁ x₂ lam :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  exact ⟨hc.U_le (hO htO), hc.U_le (hO htauO), hc.U_le (hO homO), hc.U_le hlamU⟩

theorem l18_le_sylow (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxQ t tau x₁ x₂ rho ≤ 𝒮 ∧ ctxYq t tau x₁ x₂ rho ≤ 𝒮 ∧ S ≤ 𝒮 ∧ ctxR t tau x₁ x₂ ≤ 𝒮 := by
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := l17_Q_le_O hc.toCtx13
  have hOU : ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam := le_sup_left
  have hQS : ctxQ t tau x₁ x₂ rho ≤ 𝒮 := hQO.trans (hOU.trans hc.U_le)
  exact ⟨hQS, ctxYq_le_ctxQ.trans hQS, hc.S_le_U.trans hc.U_le,
    hc.R_le_O.trans (hOU.trans hc.U_le)⟩

theorem l18_card_sylow (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) : Nat.card 𝒮 = 2 ^ 12 := by
  have hfac : (3 * 2 ^ 12).factorization 2 = 12 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
      Nat.factorization_pow_self Nat.prime_two]
  rw [card_eq_of_isSylowIn hc.sylow, hc.card_K, hfac]

theorem l18_Y_E16 (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    IsE16In 𝒮 (ctxYq t tau x₁ x₂ rho) := by
  exact ⟨(l18_le_sylow hc).2.1, l17_Y_elem hc.toCtx13, l17_card_Y hc.toCtx13⟩

theorem l18_Y_normal_sylow (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    NormalIn (ctxYq t tau x₁ x₂ rho) 𝒮 := by
  refine ⟨(l18_le_sylow hc).2.1, ?_⟩
  intro g hg k hk
  exact l17_K_normalizes_Y hc.toCtx13 g (hc.sylow.1 hg) k hk

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
