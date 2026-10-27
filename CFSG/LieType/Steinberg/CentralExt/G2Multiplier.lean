module

public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.RankTwo.G2Extras
public import CFSG.LieType.Steinberg.RankTwo.G2Comm
public import CFSG.LieType.Steinberg.G2.Perfect

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

namespace CFSG.LieType.Steinberg.CentralExt.AdjointClosed

variable {K : Type} [Field K] [Finite K]

theorem g2_exists_section_of_central (hK : 5 ≤ Nat.card K) {E : Type*} [Group E]
    {π : E →* adjointGroup .G2 K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : adjointGroup .G2 K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, hP, -⟩ :=
    RankTwo.g2_conclusionB_of_comm fun O => RankTwo.g2_exists_commutatorFormula K O
  obtain ⟨C, -, hC⟩ := RankTwo.g2_exists_commutatorFormula K O
  exact exists_section_of_central (rootOperatorFamily .G2) hK cartan_mul_cartanInvG2
    (RankTwo.g2_chevalleyExtras K O C hC) hP hπ hcen

theorem g2_hopfMultiplier (hK : 5 ≤ Nat.card K) :
    commutator (AdjointQuotient .G2 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) := by
  have : Group.IsPerfect ↥(adjointGroup .G2 K) := isPerfect_g2_of_three_le_card K (by omega)
  exact hopfMultiplier_subsingleton center_adjointGroup_eq_bot
    fun π hπ hcen => g2_exists_section_of_central hK hπ hcen

end CFSG.LieType.Steinberg.CentralExt.AdjointClosed
