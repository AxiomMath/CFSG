module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitBase

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem fixFlag_inv (ρ : H →* Module.End F V) (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V)
    (Q : Subgroup H) (h1 : NormQ ρ r Q) (h2 : NormQ ρ r⁻¹ Q) :
    ∀ k, ∀ v ∈ fixFlag ρ Q k, r v ∈ fixFlag ρ Q k := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [fixFlag_zero, Submodule.mem_bot] at hv
    subst hv
    rw [fixFlag_zero, semilin_map_zero hr]
    exact Submodule.zero_mem _
  | succ k ih =>
    intro v hv
    rw [mem_fixFlag_succ] at hv ⊢
    intro g hg
    obtain ⟨x', hx', hx'eq⟩ := h2 g hg
    have h := hx'eq (r v)
    rw [perm_inv_apply r v] at h
    have key : ρ g (r v) = r (ρ x' v) := by
      have h' : r (r⁻¹ (ρ g (r v))) = r (ρ x' v) := congrArg r h
      rwa [perm_apply_inv r] at h'
    have hsub : ρ g (r v) - r v = r (ρ x' v - v) := by
      rw [semilin_map_sub hr, key]
    rw [hsub]
    exact ih _ (hv x' hx')

end CFSG.LieType.ChevTwo.OppCl.TK
