module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UTableSpec

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

@[expose] def mulE0 (a b : Nat) : Nat := (eTab[a]!)[b]!

@[expose] def mulEJ3 (a b : Nat) : Nat := (eTabJ3[a]!)[b]!

@[expose] def eT : Nat := 21

@[expose] def posD (i : Nat) : Nat := if i = 0 then 0 else if i = 1 then 1 else if i = 4 then 2 else 3

@[expose] def redP (i k : Nat) : Nat × Nat :=
  if i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 then (i, k) else (dMul i 2, mulE0 k eT)

@[expose] def ixP (i k : Nat) : Nat := 32 * posD (redP i k).1 + (redP i k).2

@[expose] def decD (a : Nat) : Nat :=
  if a / 32 = 0 then 0 else if a / 32 = 1 then 1 else if a / 32 = 2 then 4 else 5

@[expose] def mulC (a b : Nat) : Nat := ixP (dMul (decD a) (decD b)) (mulE0 (a % 32) (b % 32))

@[expose] def tC : Nat := 21

@[expose] def invC (a : Nat) : Nat := ((List.range 128).find? fun b => mulC a b == 0).getD 0

@[expose] def commC (a b : Nat) : Nat := mulC (mulC a b) (mulC (invC a) (invC b))

@[expose] def mulF (a b : Fin 128) : Fin 128 := ⟨mulC a b % 128, Nat.mod_lt _ (by norm_num)⟩

@[expose] def tF : Fin 128 := ⟨21, by norm_num⟩

@[expose] def AutC : Subgroup (Equiv.Perm (Fin 128)) where
  carrier := {π | ∀ a b : Fin 128, π (mulF a b) = mulF (π a) (π b)}
  mul_mem' := by
    intro π σ hπ hσ a b
    show π (σ (mulF a b)) = mulF (π (σ a)) (π (σ b))
    rw [hσ a b, hπ (σ a) (σ b)]
  one_mem' := fun a b => rfl
  inv_mem' := by
    intro π hπ a b
    apply π.injective
    have h1 : π (π⁻¹ (mulF a b)) = mulF a b := Equiv.apply_symm_apply π _
    have h2 : π (π⁻¹ a) = a := Equiv.apply_symm_apply π _
    have h3 : π (π⁻¹ b) = b := Equiv.apply_symm_apply π _
    rw [h1, hπ (π⁻¹ a) (π⁻¹ b), h2, h3]

structure TabLab {M : Type*} [Group M] (W : Subgroup M) (lab : Nat → M) : Prop where
  mem : ∀ c < 128, lab c ∈ W
  surj : ∀ w ∈ W, ∃ c < 128, lab c = w
  inj : ∀ a < 128, ∀ b < 128, lab a = lab b → a = b
  mul : ∀ a < 128, ∀ b < 128, lab (mulC a b) = lab a * lab b
  one : lab 0 = 1

end CFSG.EvenSporadicStandard.Fin76b.W16
