module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.U33
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.U33
public import CFSG.GH74.KGroups.U33TablesInputs
public meta import CFSG.GH74.KGroups.U33TablesInputs
public import Certificates.Certificate5133
public import Certificates.Certificate5134

public section

namespace CFSG.GH74.KGroups.U33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem QS_valid :
    QS.check = true ∧ QS.orderCertificate = 32 :=
  Certificates.certificate5134.1

theorem QS_ok : ValidSchreier QS := QS_valid.1

theorem QS_closure : QS.originalSubgroup = Subgroup.closure {sy0, sy1, sy2, sy3, sy4} := by
  rw [QS, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem QS_le_check : leCheck QS QP = true :=
  Certificates.certificate5134.2.2.2

theorem QS_le :
    QS.originalSubgroup ≤ QP.originalSubgroup :=
  leCheck_sound QS QP QP_ok QS_le_check

theorem inv_ok :
    invConjCheck (elemsT QP) t0 = true :=
  Certificates.certificate5134.2.1

theorem small_ok :
    smallCheck (elemsT QS) s0 = true :=
  Certificates.certificate5134.2.2.1

theorem card_S : Nat.card QS.originalSubgroup = 2 ^ 5 := by
  rw [card_group QS QS_ok, QS_valid.2]
  norm_num

section Tables

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem card_K : Nat.card K = 2 ^ 5 * 189 := by
  rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  norm_num

theorem finite_K' : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv

theorem one_class :
    ∀ u v : K, orderOf u = 2 → orderOf v = 2 → ∃ g : K, g * u * g⁻¹ = v :=
  one_class_of_model QP.originalSubgroup e t0 (invConjCheck_sound QP QP_ok inv_ok)

theorem smallTable
    (T : Subgroup K) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    (∀ x ∈ T, x ^ 2 = 1 → ∃ k : K, k⁻¹ * x * k ∈ T ∧
      ∀ y ∈ T, y * (k⁻¹ * x * k) = (k⁻¹ * x * k) * y) ∧
    (∀ a ∈ T, (∀ y ∈ T, y * a = a * y) → a ^ 2 = 1 → a ∈ ⁅T, T⁆) ∧
    (∃ s : K, ∀ a ∈ T, (∀ y ∈ T, y * a = a * y) → a ^ 2 = 1 → a = 1 ∨ a = s) := by
  have : Finite K := finite_K' e
  have hs := smallCheck_sound QS QS_ok small_ok
  exact smallTable_of_model QP.originalSubgroup e QS.originalSubgroup QS_le card_S (card_K e)
    (by decide) (one_class e) s0 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 T hT hTi

end Tables

end CFSG.GH74.KGroups.U33
