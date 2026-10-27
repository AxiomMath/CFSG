module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59EChar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Stmt
import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59R6

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G]

theorem fz59e_of_R6 [Finite G] {t x₁ x₂ lam a₁₂ a₂₂ a₃₂ : G} {S T₂ : Subgroup G}
    (hT : IsFzT2 t x₁ x₂ S T₂) (hns : ¬ FzSylow T₂)
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂)
    (hR : fzR t x₁ x₂ = fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂) :
    2 ^ 10 ∣ Nat.card (fz59N3 t x₁ x₂) := by
  have hc : FzCanon T₂ (fzR t x₁ x₂) := by
    rw [hR]
    exact fz59e_canon hsh
  have hTN : T₂ ≤ fz59N3 t x₁ x₂ := fz59e_le_normalizer_of_canon hc
  have hcard := relIndex_mul_card T₂ (fz59N3 t x₁ x₂)
  rw [inf_of_le_left hTN, hsh.card] at hcard
  by_contra h10
  apply hns
  refine fzl_sylow_of_canon (W := fzR t x₁ x₂) hTN hT.isPGroup ?_ hc
  rintro ⟨k, hk⟩
  have hk' : T₂.relIndex (fz59N3 t x₁ x₂) = 2 * k := hk
  apply h10
  rw [← hcard, hk']
  exact ⟨k, by ring⟩

theorem fz59Even_holds :
    Fz59Even := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hr4 hctx hK hT hns hsh
  exact fz59e_of_R6 hT hns hsh (fzl59f_R_eq_R6 hr4 hctx hK hT hsh).1

end CFSG.OddStandard.SmallF3.FritzII
