module

public import CFSG.Open.LocalVocabulary

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

@[expose] def i28_14_symConstrAct (p N : ℕ) :
    Multiplicative (Fin N → ZMod p) →* Equiv.Perm (Fin N × ZMod p) where
  toFun f := Equiv.prodShear (Equiv.refl _) fun k => Equiv.addRight (Multiplicative.toAdd f k)
  map_one' := Equiv.ext fun y => by simp
  map_mul' f g := Equiv.ext fun y => by
    simp [add_assoc, add_comm (Multiplicative.toAdd g y.1)]

theorem i28_14_symConstrAct_apply (p N : ℕ) (f : Multiplicative (Fin N → ZMod p))
    (y : Fin N × ZMod p) :
    i28_14_symConstrAct p N f y = (y.1, y.2 + Multiplicative.toAdd f y.1) := rfl

theorem i28_14_symConstrAct_injective (p N : ℕ) : Function.Injective (i28_14_symConstrAct p N) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  apply Multiplicative.toAdd.injective
  funext k
  have := congrArg (fun σ : Equiv.Perm (Fin N × ZMod p) => (σ (k, 0)).2) hf
  simpa [i28_14_symConstrAct_apply] using this

theorem i28_14_symConstr_exists {p : ℕ} (hp : p.Prime) (X : Type) [Fintype X] :
    ∃ A : Subgroup (Equiv.Perm X), IsElemAbelian p A ∧ Nat.card A = p ^ (Fintype.card X / p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set N := Fintype.card X / p with hN
  have hle : Fintype.card (Fin N × ZMod p) ≤ Fintype.card X := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]
    exact Nat.div_mul_le_self _ _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  let ι : Fin N × ZMod p ≃ Set.range e := Equiv.ofInjective e e.injective
  let Ψ : Multiplicative (Fin N → ZMod p) →* Equiv.Perm X :=
    (Equiv.Perm.extendDomainHom ι).comp (i28_14_symConstrAct p N)
  have hinj : Function.Injective Ψ :=
    (Equiv.Perm.extendDomainHom_injective ι).comp (i28_14_symConstrAct_injective p N)
  have hcomm : ∀ f g : Multiplicative (Fin N → ZMod p), Ψ f * Ψ g = Ψ g * Ψ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  refine ⟨Ψ.range, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, f, rfl⟩ ⟨_, g, rfl⟩
    exact Subtype.ext (hcomm f g)
  · rintro _ ⟨f, rfl⟩
    rw [← map_pow]
    have : f ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      funext k
      simp
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin N → ZMod p) ≃ _), Nat.card_pi]
    simp

end CFSG.HardMathSupport.Solomon.Coordinator
