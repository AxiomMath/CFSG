module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporM12J2
public import CFSG.GH74.Generic.S45.LSporRu
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporBasic

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG.ComponentClassification.SolMax
open CFSG Subgroup CFSG.Blueprint

theorem evenPumpSpor_M11 :
    EvenPumpSporClauseFor .M11 :=
  evenPumpSporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .M11) = Nat.card NativeSporadic.M11 from rfl,
      Sporadic.Mathieu.card_M11]
    decide)

theorem evenPumpSpor_M12 :
    EvenPumpSporClauseFor .M12 :=
  evenPumpSporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .M12) = Nat.card NativeSporadic.M12 from rfl,
      Sporadic.Mathieu.card_M12]
    decide)

theorem evenPumpSpor_J1 :
    EvenPumpSporClauseFor .J1 :=
  evenPumpSporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .J1) = Nat.card NativeSporadic.J1 from rfl,
      Sporadic.J1.card_J1]
    decide)

theorem evenPumpSpor_J3 :
    EvenPumpSporClauseFor .J3 :=
  evenPumpSporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .J3) = Nat.card NativeSporadic.J3 from rfl,
      Sporadic.J3.card_J3]
    decide)

theorem evenPumpSpor_J2 :
    EvenPumpSporClauseFor .J2 :=
  evenPumpSporClauseFor_of_fixed_card
    (ComponentClassification.J2Cover.nativeEquivP : NativeSporadic.Carrier .J2 ≃* _)
    fun α hα hα1 => by
      have hord : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα) hα1
      rcases GH74.GLS.IVK.Proofs2.j2_fixed_card_aut α hord with h | h | h <;> rw [h] <;> decide

theorem evenPumpSpor_M22 :
    EvenPumpSporClauseFor .M22 :=
  evenPumpSporClauseFor_of_fixed_card (K := NativeSporadic.M22) (MulEquiv.refl _)
    fun α hα hα1 => by
    rcases GH74.Generic.S45.m22_fixed_card α hα hα1 with h | h | h <;> rw [h] <;> decide

theorem evenPumpSpor_M23 :
    EvenPumpSporClauseFor .M23 :=
  evenPumpSporClauseFor_of_fixed_card (K := NativeSporadic.M23) (MulEquiv.refl _)
    fun α hα hα1 => by
    rw [GH74.Generic.S45.LAlt.m23_fixed_card α hα hα1]
    decide

theorem evenPumpSpor_M24 :
    EvenPumpSporClauseFor .M24 :=
  evenPumpSporClauseFor_of_fixed_card (K := NativeSporadic.M24) (MulEquiv.refl _)
    fun α hα hα1 => by
    rcases GH74.Generic.S45.LAlt.m24_fixed_card α hα hα1 with h | h <;> rw [h] <;> decide

theorem evenPumpSpor_Ru :
    EvenPumpSporClauseFor .Ru :=
  evenPumpSporClauseFor_of_fixedSubgroup_card fun S _ _ e α hα hα1 => by
    have h1 : Nat.card (ComponentClassification.FixedCommutingProduct.fixedSubgroup α) =
        Nat.card ↥(GH74.Uniqueness.Bender.autFixed α) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    rw [h1]
    rcases GH74.Generic.S45.ru_fixed_card e α hα hα1 with h | h <;> rw [h] <;> decide

end CFSG.ComponentClassification.EvenPump
