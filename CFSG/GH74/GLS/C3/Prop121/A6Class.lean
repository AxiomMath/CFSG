module

public import CFSG.GH74.GLS.C3.Prop121.CentKFin
public meta import CFSG.GH74.GLS.C3.Prop121.CentKFin
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Prop121.A6ClassInputs
public meta import CFSG.GH74.GLS.C3.Prop121.A6ClassInputs
public import Certificates.Certificate5075

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm

theorem okInvConj_true : okInvConj = true :=
  Certificates.certificate5075

theorem isConj_of_involutions_alt_six
    (a b : alternatingGroup (Fin 6)) (ha : orderOf a = 2)
    (hb : orderOf b = 2) : IsConj a b := by
  have hsq : ∀ c : alternatingGroup (Fin 6), orderOf c = 2 →
      (c : Perm (Fin 6)) * c = 1 ∧ (c : Perm (Fin 6)) ≠ 1 ∧ sign (c : Perm (Fin 6)) = 1 := by
    intro c hc
    refine ⟨?_, ?_, mem_alternatingGroup.1 c.2⟩
    · have : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
      have h2 := congrArg Subtype.val this
      simpa [sq] using h2
    · intro h1
      have : c = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hc
      omega
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 okInvConj_true (a : Perm (Fin 6))
    (mem_inv6.2 (hsq a ha))) (b : Perm (Fin 6)) (mem_inv6.2 (hsq b hb))
  obtain ⟨π, hπ, hπab⟩ := List.any_eq_true.1 h1
  have hπs : sign π = 1 := mem_even6.1 hπ
  refine isConj_iff.2 ⟨⟨π, mem_alternatingGroup.2 hπs⟩, ?_⟩
  apply Subtype.ext
  simpa using of_decide_eq_true hπab

end CFSG.GH74.GLS.C3.Prop121
