module

public import CFSG.HardMathSupport.RichardWeiss.Proving.CarmichaelLift

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.LocalAnalysis.ComponentInitial

theorem injective_of_surjective_alt {α : Type} [Fintype α] [DecidableEq α] (hα : 5 ≤ Nat.card α)
    {K : Type} [Group K] [Nontrivial K] (f : alternatingGroup α →* K)
    (hf : Function.Surjective f) : Function.Injective f := by
  have : IsSimpleGroup (alternatingGroup α) := alternatingGroup.isSimpleGroup hα
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker f) with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := exists_ne (1 : K)
    obtain ⟨x, rfl⟩ := hf k
    have hx : x ∈ MonoidHom.ker f := by
      rw [h]
      exact Subgroup.mem_top x
    exact hk (MonoidHom.mem_ker.mp hx)

end CFSG.HardMathSupport.RichardWeiss.Proving
