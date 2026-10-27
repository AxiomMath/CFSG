module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutSylow
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Fi23

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ExtSRank : Prop :=
  ∀ A : Subgroup (Equiv.Perm (Fin 3510)), A ≤ fi22ExtS → (∀ a ∈ A, a ^ 2 = 1) → ¬ A ≤ fi22P →
    Nat.card A ≤ 2 ^ 8

theorem outerRankCore_of_ext
    (h : ExtSRank) :
    OuterRankCore := by
  obtain ⟨Q, hQ⟩ := fi22ExtS_sylow
  exact AutSylow.rank_of_sylow fi22R_le_normalizer Q hQ h

theorem Cd_rank_of_extS
    (h : ExtSRank) :
    ∀ σ : MulAut ↥Cd, σ * σ = 1 → (∀ l : ↥Cd, σ ≠ MulAut.conj l) →
      ∀ B : Subgroup ↥Cd, (∀ b ∈ B, b ^ 2 = 1) → (∀ b ∈ B, σ b = b) → Nat.card B ≤ 2 ^ 8 :=
  Cd_rank_of_core (outerRankCore_of_ext h)

end CFSG.EvenSporadicStandard.TwoFi22.DS81
