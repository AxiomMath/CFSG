module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.OuterAutomorphisms

variable {Y Z : Type*} [Group Y] [Group Z]

@[expose] noncomputable def innAutDerived (Y : Type*) [Group Y] : Subgroup (MulAut Y) :=
  inner Y ⊔ commutator (MulAut Y)

instance innAutDerived_normal (Y : Type*) [Group Y] : (innAutDerived Y).Normal :=
  Subgroup.sup_normal _ _

theorem inner_le_innAutDerived (Y : Type*) [Group Y] : inner Y ≤ innAutDerived Y :=
  le_sup_left

theorem commutator_le_innAutDerived (Y : Type*) [Group Y] :
    commutator (MulAut Y) ≤ innAutDerived Y :=
  le_sup_right

theorem map_mem_commutator_mulAut (f : MulAut Y →* MulAut Z) {x : MulAut Y}
    (hx : x ∈ commutator (MulAut Y)) : f x ∈ commutator (MulAut Z) := by
  have : f x ∈ (commutator (MulAut Y)).map f := ⟨x, hx, rfl⟩
  rw [commutator_def, Subgroup.map_commutator] at this
  rw [commutator_def]
  exact Subgroup.commutator_mono le_top le_top this

theorem innerAut_le_commutator_of_perfect (hY : commutator Y = ⊤) :
    inner Y ≤ commutator (MulAut Y) := by
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ commutator Y := hY ▸ Subgroup.mem_top y
  have h1 : (commutator Y).map (MulAut.conj : Y →* MulAut Y) ≤ commutator (MulAut Y) := by
    rw [commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h1 ⟨y, hy, rfl⟩

theorem innAutDerived_eq_commutator_of_perfect (hY : commutator Y = ⊤) :
    innAutDerived Y = commutator (MulAut Y) :=
  le_antisymm (sup_le (innerAut_le_commutator_of_perfect hY) le_rfl) le_sup_right

theorem map_commutator_mulAut_congr (e : Y ≃* Z) :
    (commutator (MulAut Y)).map (MulAut.congr e).toMonoidHom = commutator (MulAut Z) := by
  rw [commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (MulAut.congr e).surjective, ← commutator_def]

theorem map_innAutDerived_congr (e : Y ≃* Z) :
    (innAutDerived Y).map (MulAut.congr e).toMonoidHom = innAutDerived Z := by
  rw [innAutDerived, innAutDerived, Subgroup.map_sup, inner_map_congr, map_commutator_mulAut_congr]

theorem mem_innAutDerived_congr (e : Y ≃* Z) {α : MulAut Y} :
    MulAut.congr e α ∈ innAutDerived Z ↔ α ∈ innAutDerived Y := by
  rw [← map_innAutDerived_congr e]
  exact Subgroup.mem_map_iff_mem (MulAut.congr e).injective

end CFSG.ComponentClassification.OuterAutomorphisms
