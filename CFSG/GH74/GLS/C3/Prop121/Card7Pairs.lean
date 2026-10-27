module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup

theorem pair_count_transport {Γ M : Type*} [Group Γ] [Group M] (D : Subgroup Γ) (e : ↥D ≃* M)
    (PX PY : Γ → Prop) (PX' PY' : M → Prop)
    (hX : ∀ d : ↥D, PX (d : Γ) ↔ PX' (e d)) (hY : ∀ d : ↥D, PY (d : Γ) ↔ PY' (e d)) (v : ↥D) :
    Nat.card {p : Γ × Γ // p.1 ∈ D ∧ p.2 ∈ D ∧ PX p.1 ∧ PY p.2 ∧ (v : Γ) ∈ zpowers (p.1 * p.2)} =
      Nat.card {q : M × M // PX' q.1 ∧ PY' q.2 ∧ e v ∈ zpowers (q.1 * q.2)} := by
  have hz : ∀ a b : ↥D, ((v : Γ) ∈ zpowers ((a : Γ) * (b : Γ))) ↔ (e v ∈ zpowers (e a * e b)) := by
    intro a b
    constructor
    · rintro hv
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hv
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      have : (a * b) ^ k = v := Subtype.ext (by simpa using hk)
      rw [← map_mul, ← map_zpow, this]
    · rintro hv
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hv
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      have : (a * b) ^ k = v := by
        apply e.injective
        rw [map_zpow, map_mul, hk]
      simpa using congrArg Subtype.val this
  refine Nat.card_congr
    { toFun := fun p => ⟨(e ⟨p.1.1, p.2.1⟩, e ⟨p.1.2, p.2.2.1⟩), ?_, ?_, ?_⟩
      invFun := fun q => ⟨((e.symm q.1.1 : ↥D), (e.symm q.1.2 : ↥D)), (e.symm q.1.1).2,
        (e.symm q.1.2).2, ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (hX ⟨p.1.1, p.2.1⟩).1 p.2.2.2.1
  · exact (hY ⟨p.1.2, p.2.2.1⟩).1 p.2.2.2.2.1
  · exact (hz ⟨p.1.1, p.2.1⟩ ⟨p.1.2, p.2.2.1⟩).1 p.2.2.2.2.2
  · exact (hX (e.symm q.1.1)).2 (by simpa using q.2.1)
  · exact (hY (e.symm q.1.2)).2 (by simpa using q.2.2.1)
  · have := (hz (e.symm q.1.1) (e.symm q.1.2)).2 (by simpa using q.2.2.2)
    exact this
  · intro p
    ext <;> simp
  · intro q
    ext <;> simp

end CFSG.GH74.GLS.C3.Prop121.Card7
