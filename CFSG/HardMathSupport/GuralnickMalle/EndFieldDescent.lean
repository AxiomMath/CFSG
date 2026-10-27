module

public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Curtis
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.HardMathSupport.GuralnickMalle

theorem nonempty_ringHom_algebraicClosure
    {K F₀ : Type*} [Field K] [Finite K] [Field F₀] [Finite F₀] {p : ℕ}
    [CharP K p] [CharP F₀ p] : Nonempty (F₀ →+* AlgebraicClosure K) := by
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have : Algebra (ZMod p) F₀ := ZMod.algebra F₀ p
  have : Algebra (ZMod p) (AlgebraicClosure K) := ZMod.algebra (AlgebraicClosure K) p
  have : Module.Finite (ZMod p) F₀ := Module.finite_iff_finite.mpr ‹Finite F₀›
  have : Algebra.IsAlgebraic (ZMod p) F₀ := Algebra.IsAlgebraic.of_finite (ZMod p) F₀
  exact ⟨(IsAlgClosed.lift (R := ZMod p) (S := F₀) (M := AlgebraicClosure K)).toRingHom⟩

end CFSG.HardMathSupport.GuralnickMalle
