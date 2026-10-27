module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.AGLEmbedding

open CFSG.PreuniquenessRankFour.Helpers

variable {A V : Type*} [CommGroup A] [Finite A] [Group V] [Finite V] [MulDistribMulAction A V]

@[expose] def fixedBy (F : Subgroup A) : Subgroup V where
  carrier := {v | ∀ a ∈ F, a • v = v}
  one_mem' := fun a _ => smul_one a
  mul_mem' := fun hv hw a ha => by rw [smul_mul', hv a ha, hw a ha]
  inv_mem' := fun hv a ha => by rw [smul_inv', hv a ha]

omit [Finite A] [Finite V] in
theorem fixedBy_top_le (F : Subgroup A) : fixedBy (⊤ : Subgroup A) ≤ (fixedBy F : Subgroup V) :=
  fun _ hv a _ => hv a trivial

end CFSG.AGLEmbedding
