module

public import CFSG.Blueprint.SourceExceptionalModels
public import CFSG.LieType.Chevalley.SimpleRootSubgroups
public import CFSG.LieType.Ree.Duality

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank Module CFSG.LieType.Chevalley
open CFSG.LieType.Ree

theorem map_autFixedSubgroup_of_conj {A C : Type} [Group A] [Group C] (Φ : A ≃* C)
    (η : A ≃* A) (F : C ≃* C) (hconj : ∀ g, Φ (η g) = F (Φ g)) :
    (autFixedSubgroup η).map (Φ : A →* C) = autFixedSubgroup F := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_autFixedSubgroup]
    change F (Φ g) = Φ g
    rw [← hconj, (mem_autFixedSubgroup η g).1 hg]
  · intro hx
    refine ⟨Φ.symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_autFixedSubgroup]
    apply Φ.injective
    rw [hconj, MulEquiv.apply_symm_apply]
    exact (mem_autFixedSubgroup F x).1 hx

variable {E : Type} [AddCommGroup E] [Module ℝ E]

end CFSG.Blueprint.EvenSource
