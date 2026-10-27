module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

abbrev C16K0 : Type := ZMod 2 × ZMod 2

abbrev C16H0 : Type := C16K0 × C16K0

@[expose] def c16Rho0 (p : C16K0) : C16K0 := (p.2, p.1 + p.2)

@[expose] def c16Theta (σ : C16H0) : C16H0 := (c16Rho0 (σ.1 + σ.2), c16Rho0 σ.1)

@[expose] def c16Nu (σ : C16H0) : C16H0 := σ + c16Theta σ + c16Theta (c16Theta σ)

@[expose] def c16T0 : C16H0 := ((1, 0), (0, 1))

@[expose] def c16Qm (σ : C16H0) : Prop := c16Nu σ = 0 ∨ c16Nu σ = c16T0

instance : DecidablePred c16Qm := fun σ => by unfold c16Qm; infer_instance

@[expose] def c16Pplus (σ : C16H0) : Prop := σ.1 = 0 ∨ σ.2 = 0 ∨ σ.1 + σ.2 = 0

instance : DecidablePred c16Pplus := fun σ => by unfold c16Pplus; infer_instance

@[expose] def c16Good (σ : C16H0) : Prop := σ ≠ 0 ∧ ¬ c16Pplus σ

instance : DecidablePred c16Good := fun σ => by unfold c16Good; infer_instance

theorem c16_card_Qm : (Finset.univ.filter c16Qm).card = 8 := by decide

theorem c16_F4 : ∀ w : C16H0, c16Qm w → w ≠ 0 → c16Pplus w → c16Good (c16T0 + w) := by decide

@[expose] def c16Sep (σ : C16H0) : Prop :=
  ∀ w : C16H0, c16Qm w → w ≠ 0 → c16Pplus w → c16Good (σ + w)

instance : DecidablePred c16Sep := fun σ => by unfold c16Sep; infer_instance

theorem c16_F5 : ∀ σ : C16H0, c16Qm σ → c16Sep σ → σ = c16T0 := by decide

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
