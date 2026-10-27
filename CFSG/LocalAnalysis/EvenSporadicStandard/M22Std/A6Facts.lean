module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.SolomonA7Input
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open
open CFSG.EvenSporadicStandard.M23Std

instance isSimpleGroup_alternatingGroup_six : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem even_natCard_alternatingGroup_six : Even (Nat.card (alternatingGroup (Fin 6))) := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp only [Fintype.card_fin]
  exact ⟨180, by decide⟩

theorem center_alternatingGroup_six : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
  alternatingGroup.center_eq_bot (by simp)

open Equiv Equiv.Perm in
@[expose] def sigma6 : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

open Equiv Equiv.Perm in
theorem sigma6_mem : sigma6 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.2 (by simp [sigma6, Equiv.Perm.sign_mul])

open Equiv Equiv.Perm in
theorem orderOf_sigma6 : orderOf (⟨sigma6, sigma6_mem⟩ : alternatingGroup (Fin 6)) = 4 := by
  rw [Subgroup.orderOf_mk, show (4 : ℕ) = 2 ^ (1 + 1) by norm_num]
  exact orderOf_eq_prime_pow (by decide : ¬ sigma6 ^ 2 ^ 1 = 1) (by decide)

theorem solomonGen_six (h : CFSG.EvenSporadicStandard.Fin76b.SolomonZ2A6) :
    SolomonGen (alternatingGroup (Fin 6)) := h

end CFSG.EvenSporadicStandard.M22Std
