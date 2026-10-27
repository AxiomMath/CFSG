module


public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence

theorem abelian_equiv {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : E, x ^ p = 1) (hab : ∀ x y : E, x * y = y * x) :
    ∃ n : ℕ, Nonempty (E ≃* Multiplicative (Fin n → ZMod p)) := by
  have add_equiv_aux {p : ℕ} [Fact p.Prime] (A : Type) [AddCommGroup A] [Finite A]
      [Module (ZMod p) A] : ∃ n : ℕ, Nonempty (A ≃+ (Fin n → ZMod p)) := by
    haveI : Module.Finite (ZMod p) A := Module.Finite.of_finite
    exact ⟨_, ⟨(Module.finBasis (ZMod p) A).equivFun.toAddEquiv⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup E := { ‹Group E› with mul_comm := hab }
  letI : Module (ZMod p) (Additive E) :=
    AddCommGroup.zmodModule (n := p) fun x => by
      have := hexp x.toMul
      simpa using congrArg Additive.ofMul this
  haveI : Finite (Additive E) := ‹Finite E›
  obtain ⟨n, ⟨e⟩⟩ := add_equiv_aux (p := p) (Additive E)
  exact ⟨n, ⟨AddEquiv.toMultiplicative e⟩⟩

end CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
