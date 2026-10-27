module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutX

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Fi23

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem Cd_rank_proved :
    ∀ σ : MulAut ↥Cd, σ * σ = 1 → (∀ l : ↥Cd, σ ≠ MulAut.conj l) →
      ∀ B : Subgroup ↥Cd, (∀ b ∈ B, b ^ 2 = 1) → (∀ b ∈ B, σ b = b) → Nat.card B ≤ 2 ^ 8 :=
  Cd_rank_of_extS extSRank_proved

end CFSG.EvenSporadicStandard.TwoFi22.DS81
