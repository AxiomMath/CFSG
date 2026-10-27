module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeSpec

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open scoped commutatorElement

theorem exists_perfect_Cbar :
    ∃ Y : Subgroup (Equiv.Perm (Fin 3510)), Y ≤ Cbar ∧ ⁅Y, Y⁆ = Y ∧
      (Y ⊔ Qbar).relIndex Cbar = 2 ∧
      ∀ U : Subgroup (Equiv.Perm (Fin 3510)), Subgroup.zpowers t1 ≤ U → U ≤ Qbar →
        InvUnder Y U →
          Nat.card U = 2 ∨ Nat.card U = 2 ^ 2 ∨ Nat.card U = 2 ^ 10 ∨ Nat.card U = 2 ^ 11 :=
  ⟨Ybar, Ybar_le_Cbar, commutator_Ybar, relIndex_Ybar_sup_Qbar,
    fun _ ht hUQ hinv => lattice_Ybar ht hUQ hinv⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
