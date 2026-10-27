module

public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.ClassicalInvolution.QuaternionStructure.Lifting
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs

public section

namespace CFSG.ClassicalInvolution.A7M

open Equiv Equiv.Perm CFSG.ClassicalInvolution.Hat2A7
open scoped MatrixGroups

theorem nonempty_mulEquiv_alternatingGroup_five_psl :
    Nonempty (alternatingGroup (Fin 5) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  have hSL : Nat.card SL(2, ZMod 5) = 120 := by
    rw [Matrix.card_SL_field (𝔽 := ZMod 5) 2, ZMod.card, Fin.prod_univ_two]
    norm_num
  have h60 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = 60 := by
    have := QuaternionStructure.natCard_specialLinearGroup_two (K := ZMod 5)
      (Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; norm_num))
    rw [hSL] at this
    change 120 = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) * 2 at this
    omega
  obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
  exact ⟨e.symm⟩

end CFSG.ClassicalInvolution.A7M
