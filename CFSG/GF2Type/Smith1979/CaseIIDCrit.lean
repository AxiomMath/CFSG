module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.GF2Type.Smith1979.Case2

@[expose] def CritII (X : Type*) [Group X] : Prop :=
  ∃ σ : MulAut X, σ * σ = 1 ∧ (∀ x : X, σ ≠ MulAut.conj x) ∧ Nat.card {x : X // σ x = x} = 1344

theorem CritII.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : CritII X) :
    CritII Y := by
  obtain ⟨σ, hσ2, hσi, hσc⟩ := h
  refine ⟨MulAut.congr e σ, ?_, fun y hy => hσi (e.symm y) ?_, ?_⟩
  · rw [← map_mul, hσ2, map_one]
  · ext x
    have h := congrArg (fun φ : MulAut Y => e.symm (φ (e x))) hy
    simpa [MulAut.congr_apply, MulAut.conj_apply] using h
  · rw [← hσc]
    exact Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun y => by
      rw [MulAut.congr_apply]
      exact (Equiv.eq_symm_apply e.toEquiv).symm)

@[expose] def fixSubgroup {X : Type*} [Group X] (σ : MulAut X) : Subgroup X :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id X)

theorem mem_fixSubgroup {X : Type*} [Group X] {σ : MulAut X} {x : X} :
    x ∈ fixSubgroup σ ↔ σ x = x :=
  Iff.rfl

theorem card_fixSubgroup {X : Type*} [Group X] (σ : MulAut X) :
    Nat.card (fixSubgroup σ) = Nat.card {x : X // σ x = x} :=
  rfl

end CFSG.GF2Type.Smith1979.Case2
