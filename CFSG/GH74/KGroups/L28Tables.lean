module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.L28
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.L28
public import CFSG.GH74.KGroups.L28TablesInputs
public meta import CFSG.GH74.KGroups.L28TablesInputs
public import Certificates.Certificate5118
public import Certificates.Certificate5119

public section

namespace CFSG.GH74.KGroups.L28

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem QS_valid :
    QS.check = true ∧ QS.orderCertificate = 8 :=
  Certificates.certificate5119.1

theorem QS_ok : ValidSchreier QS := QS_valid.1

theorem QS_le_check : leCheck QS QP = true :=
  Certificates.certificate5119.2.2.2

theorem QS_le :
    QS.originalSubgroup ≤ QP.originalSubgroup :=
  leCheck_sound QS QP QP_ok QS_le_check

theorem QS_comm : commCheck (elemsT QS) = true :=
  Certificates.certificate5119.2.1

theorem out_ok :
    powInPCheck (elemsT QA) QP 8 = true :=
  Certificates.certificate5119.2.2.1

theorem card_S : Nat.card QS.originalSubgroup = 2 ^ 3 := by
  rw [card_group QS QS_ok, QS_valid.2]
  norm_num

section Tables

variable {K : Type} [Group K]

theorem out_inner
    (h : LieModel K .PSL 2 2 3) (φ : MulAut K) (n : ℕ) (hφ : φ ^ 2 ^ n = 1) :
    ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  obtain ⟨M, hP, hA⟩ := autModel h
  have hs := powInPCheck_sound QA QP QA_ok QP_ok out_ok
  have hN : Nat.card (MulAut K) = 2 ^ 3 * 189 := by rw [card_mulAut h]; norm_num
  exact M.out_inner_two hN (by decide) (fun τ hτ h2 => by
    rw [hP]; rw [hA] at hτ; exact hs τ hτ h2) φ n hφ

theorem sylow_comm
    (h : LieModel K .PSL 2 2 3) (Q : Subgroup K) (hQ : IsPGroup 2 Q)
    (hQi : ¬ 2 ∣ Q.index) : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  obtain ⟨e⟩ := equiv_of_lieModel h
  have : Finite K := finite_K h
  have hK : Nat.card K = 2 ^ 3 * 63 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]; norm_num
  exact sylow_comm_of_model QP.originalSubgroup e QS.originalSubgroup QS_le card_S hK (by decide)
    (commCheck_sound QS QS_ok QS_comm) Q hQ hQi

end Tables

end CFSG.GH74.KGroups.L28
