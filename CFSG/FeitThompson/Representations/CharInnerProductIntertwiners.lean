module
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module
open scoped ComplexConjugate

variable {G : Type*} [Group G] [Fintype G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem cfInner_character_eq_finrank_intertwiningMap (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) :
    cfInner σ.character ρ.character = (finrank ℂ (ρ.IntertwiningMap σ) : ℂ) := by
  rw [cfInner_def, ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ]
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  rw [Representation.character_inv ρ (isOfFinOrder_of_finite g)]

theorem cfInner_character_eq_finrank_hom (X Y : FDRep ℂ G) :
    cfInner Y.character X.character = (finrank ℂ (X ⟶ Y) : ℂ) := by
  rw [cfInner_def, ← FDRep.scalar_product_char_eq_finrank_equivariant X Y]
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  rw [show X.character g⁻¹ = Representation.character X.ρ g⁻¹ from rfl,
    Representation.character_inv X.ρ (isOfFinOrder_of_finite g)]
  rfl

end CFSG.FeitThompson
