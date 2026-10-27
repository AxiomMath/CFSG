module


public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.LinearAlgebra.CoprimeActions.IrreducibleNormalFixedSpace

theorem fixedSpace_eq_bot {F E V : Type*} [Field F] [Group E] [AddCommGroup V] [Module F V]
    (ρ : Representation F E V) (hfaith : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (N : Subgroup E) [N.Normal] (hN : N ≠ ⊥) :
    Representation.invariants (ρ.comp N.subtype) = ⊥ := by
  let S : Subrepresentation ρ :=
    ⟨Representation.invariants (ρ.comp N.subtype), by
      intro g v hv
      rw [Representation.mem_invariants] at hv ⊢
      intro n
      have hn : g⁻¹ * (n : E) * g ∈ N := by
        simpa using (Subgroup.Normal.conj_mem ‹N.Normal› (n : E) n.2 g⁻¹)
      have h1 := hv ⟨g⁻¹ * (n : E) * g, hn⟩
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at h1 ⊢
      have h2 := congrArg (ρ g) h1
      rw [← Module.End.mul_apply, ← map_mul] at h2
      rw [← Module.End.mul_apply, ← map_mul]
      simpa [mul_assoc] using h2⟩
  rcases hirr.eq_bot_or_eq_top S with h | h
  · have := congrArg Subrepresentation.toSubmodule h
    exact this
  · exfalso
    apply hN
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    apply hfaith
    ext v
    have hv : v ∈ S := by rw [h]; trivial
    have := (Representation.mem_invariants _ _).1 hv ⟨n, hn⟩
    simpa using this

end CFSG.LinearAlgebra.CoprimeActions.IrreducibleNormalFixedSpace

end
