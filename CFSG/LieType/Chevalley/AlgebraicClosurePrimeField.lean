module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public section

namespace CFSG.LieType.Chevalley

theorem algebraicClosure_isAlgebraic_zmod (r : ℕ) [Fact r.Prime] (k : Type) [Field k] [Finite k]
    [CharP (AlgebraicClosure k) r] :
    letI := ZMod.algebra (AlgebraicClosure k) r
    Algebra.IsAlgebraic (ZMod r) (AlgebraicClosure k) := by
  let _ : Algebra (ZMod r) (AlgebraicClosure k) := ZMod.algebra (AlgebraicClosure k) r
  refine ⟨fun y => ?_⟩
  obtain ⟨E, hEf, hyE, -⟩ :=
    exists_finite_subfield_of_finset (K := k) ({y} : Finset (AlgebraicClosure k))
  have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
  have : Fintype E := Fintype.ofFinite E
  have hpow : y ^ Fintype.card E = y :=
    congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
  refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod r) Fintype.one_lt_card, ?_⟩
  rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]

end CFSG.LieType.Chevalley
