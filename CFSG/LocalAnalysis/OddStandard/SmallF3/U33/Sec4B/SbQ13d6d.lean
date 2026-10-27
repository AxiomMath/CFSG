module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d3a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_two_pow_dvd_card_L (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) :
    2 ^ 11 ∣ Nat.card ↥(q13L t tau x₁ x₂ rho om) := by
  obtain ⟨𝒮, _hS2, _hUS, hNUS, hcardS⟩ := q13d_exists_cover h
  have hS_le_normU : 𝒮 ≤ Subgroup.normalizer (ctxU t tau x₁ x₂ lam : Set G) :=
    Subgroup.le_normalizer_iff.mpr hNUS.2
  have hnorm_le : Subgroup.normalizer (ctxU t tau x₁ x₂ lam : Set G) ≤
      q13L t tau x₁ x₂ rho om := by
    rw [q13L]
    exact q13d_normalizer_le_of_charIn (q13d_E0_char_U h hB)
  have hS_le_L : 𝒮 ≤ q13L t tau x₁ x₂ rho om := hS_le_normU.trans hnorm_le
  have hdvd : Nat.card ↥𝒮 ∣ Nat.card ↥(q13L t tau x₁ x₂ rho om) :=
    Subgroup.card_dvd_of_le hS_le_L
  rwa [hcardS] at hdvd

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
