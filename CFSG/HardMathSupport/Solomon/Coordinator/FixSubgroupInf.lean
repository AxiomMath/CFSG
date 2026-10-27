module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

variable {K : Type*} [Group K]

theorem iInf_fixSubgroup_closure (s : Set (MulAut K)) :
    ⨅ f ∈ Subgroup.closure s, fixSubgroup f = ⨅ f ∈ s, fixSubgroup f := by
  refine le_antisymm (le_iInf fun f => le_iInf fun hf => ?_)
    (le_iInf fun f => le_iInf fun hf => ?_)
  · exact iInf₂_le_of_le (f := fun f _ => fixSubgroup f) f (Subgroup.subset_closure hf) le_rfl
  · intro x hx
    have hstab : Subgroup.closure s ≤ MulAction.stabilizer (MulAut K) x := by
      refine (Subgroup.closure_le (MulAction.stabilizer (MulAut K) x)).mpr fun g hg => ?_
      change g ∈ MulAction.stabilizer (MulAut K) x
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact mem_fixSubgroup.mp (iInf₂_le_of_le (f := fun f _ => fixSubgroup f) g hg le_rfl hx)
    exact mem_fixSubgroup.mpr (by simpa [MulAut.smul_def] using hstab hf)

theorem iInf_fixSubgroup_zpowers (α : MulAut K) :
    ⨅ f ∈ Subgroup.zpowers α, fixSubgroup f = fixSubgroup α := by
  rw [Subgroup.zpowers_eq_closure, iInf_fixSubgroup_closure]
  refine le_antisymm (iInf₂_le_of_le (f := fun f _ => fixSubgroup f) α (Set.mem_singleton α) le_rfl) ?_
  refine le_iInf fun f => le_iInf fun hf => ?_
  rw [Set.mem_singleton_iff] at hf
  subst hf
  exact le_rfl

theorem iInf_fixSubgroup_zpowers_sup (α β : MulAut K) :
    ⨅ f ∈ Subgroup.zpowers α ⊔ Subgroup.zpowers β, fixSubgroup f =
      fixSubgroup α ⊓ fixSubgroup β := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    ← Subgroup.closure_union, iInf_fixSubgroup_closure]
  refine le_antisymm (le_inf (iInf₂_le_of_le (f := fun f _ => fixSubgroup f) α (Or.inl rfl) le_rfl)
    (iInf₂_le_of_le (f := fun f _ => fixSubgroup f) β (Or.inr rfl) le_rfl)) ?_
  refine le_iInf fun f => le_iInf fun hf => ?_
  rcases hf with hf | hf
  · rw [hf]; exact inf_le_left
  · rw [hf]; exact inf_le_right

end CFSG.HardMathSupport.Solomon.Coordinator

end
