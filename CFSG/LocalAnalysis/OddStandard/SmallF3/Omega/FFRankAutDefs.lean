module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

@[expose] def ffRADPlus : Fin 6 → ZMod 3 := ![-1, 1, 1, 1, 1, 1]

@[expose] def ffRADMinus : Fin 6 → ZMod 3 := fun _ => 1

@[expose] def FFRASide (n : ℕ) (d : Fin 6 → ZMod 3) (flag : Bool) (bound : ℕ) : Prop :=
  ∃ (T : Fin n → Matrix (Fin 6) (Fin 6) (ZMod 3)) (mul : Fin n → Fin n → Fin n) (one : Fin n)
      (𝓛 : Set (Finset (Fin n))),
    T one = 1 ∧
    (∀ i, ∃ c : ZMod 3, (c = 1 ∨ c = -1) ∧
      (T i)ᵀ * Matrix.diagonal d * T i = c • Matrix.diagonal d) ∧
    (∀ i j, T (mul i j) = T i * T j ∨ T (mul i j) = -(T i * T j)) ∧
    (∀ i j, T i = T j ∨ T i = -T j → i = j) ∧
    {one} ∈ 𝓛 ∧ (∀ H ∈ 𝓛, H.card ≤ bound) ∧
    ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → (if flag then mul x x = one else mul x x ∈ H) →
      (∀ h ∈ H, mul x h = mul h x) → H ∪ H.image (mul x) ∈ 𝓛

end CFSG.OddStandard.SmallF3.Omega
