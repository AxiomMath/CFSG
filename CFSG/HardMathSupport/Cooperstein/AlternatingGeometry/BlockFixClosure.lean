module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ModelTwoAF

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem blockFix_eq_closure : blockFix ι = Subgroup.closure (Set.range (blockTransp (ι := ι))) := by
  classical
  apply le_antisymm
  · intro z hz
    rw [← range_blockPermHom] at hz
    obtain ⟨g, rfl⟩ := hz
    set E : Subgroup (Perm (ι × Bool)) := Subgroup.closure (Set.range (blockTransp (ι := ι))) with hE
    have hmem : ∀ i, tI i ∈ E.comap (blockPermHom ι) := fun i => by
      show blockPermHom ι (tI i) ∈ E
      rw [blockPermHom_tI]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hEq := eq_ker_fsign (E.comap (blockPermHom ι)) (∅ : Finset ι)
      (fun i => by simp [hmem i]) (fun i hi => by simp at hi)
    have hg : g ∈ E.comap (blockPermHom ι) := by
      rw [hEq, MonoidHom.mem_ker, fsign_apply]; simp
    exact hg
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact swap_mem_blockFix rfl

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
