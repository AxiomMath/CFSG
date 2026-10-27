module

public import CFSG.GH74.Filter.Monster.Elementary

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem t_sporadic_M : S_sporadic .M := by
  intro G _ _ hnonab ⟨e⟩
  have hG : commutator Y443 ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hnonab
    have hsub : Subsingleton M := ⟨fun x y => by
      have hx : (x : Y443) ∈ (⊥ : Subgroup Y443) := by rw [← h]; exact x.2
      have hy : (y : Y443) ∈ (⊥ : Subgroup Y443) := by rw [← h]; exact y.2
      rw [Subgroup.mem_bot] at hx hy
      exact Subtype.ext (hx.trans hy.symm)⟩
    have : Subsingleton (Carrier .M) := hsub
    have : Subsingleton G := e.injective.subsingleton
    exact hab (Subsingleton.elim _ _)
  exact not_gen4_of_mulEquiv e.symm (Monster.not_gen4_M hG)

end CFSG.GH74.Filter
