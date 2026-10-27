module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAssembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutH
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXRank

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Sporadic.Fi23

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem Cd_aut_cent :
    ∀ σ : MulAut ↥Cd, (∀ e ∈ E0, σ e = e) → ∃ x ∈ E0, σ = MulAut.conj x :=
  Cd_aut_cent_of_exists exists_centralizerCore_elementary_abelian

theorem Cd_rank :
    ∀ σ : MulAut ↥Cd, σ * σ = 1 → (∀ l : ↥Cd, σ ≠ MulAut.conj l) →
      ∀ B : Subgroup ↥Cd, (∀ b ∈ B, b ^ 2 = 1) → (∀ b ∈ B, σ b = b) → Nat.card B ≤ 2 ^ 8 :=
  Cd_rank_proved

theorem fi22CoverAut :
    Fi22CoverAut :=
  ⟨Cd_rank, Cd_aut_cent⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81
