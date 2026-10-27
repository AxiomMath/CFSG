module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalReal
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
import CFSG.GroupTheory.SignedPermFixedSpace

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsSignedCoords)

variable {K : Type} [Field K]

theorem c₀_normalizer [Finite K] (F : Frame K) :
    ∀ m ∈ Subgroup.normalizer ((c₀ F).range : Set ↥(Omega7 K)),
      ∃ (τ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ v,
        m * c₀ F v * m⁻¹ =
          c₀ F (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (τ i)) := by
  intro m hm
  refine exists_signedPerm_of_conj_mem_range (Omega7 K).subtype (c₀ F)
    (c₀_injective F) ?_ m ?_
  · intro v
    have hset : (⋂ v' : F3Cube, fixedVectors ((Omega7 K).subtype (c₀ F v'))) =
        {w : Idx → K | ∀ v' : F3Cube,
          (((c₀ F v' : ↥(Omega7 K)) : GL Idx K) : Matrix Idx Idx K) *ᵥ w = w} := by
      ext w
      simp [fixedVectors]
    have hsingle : fixedVectors ((Omega7 K).subtype (c₀ F v)) =
        {w : Idx → K | (((c₀ F v : ↥(Omega7 K)) : GL Idx K) : Matrix Idx Idx K) *ᵥ w = w} :=
      rfl
    rw [commonFixedVectors, hset, hsingle]
    exact fix_iff F v
  · intro v
    have h : m * c₀ F v * m⁻¹ ∈ (c₀ F).range :=
      (Subgroup.mem_set_normalizer_iff.mp hm (c₀ F v)).mp ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp h
    exact ⟨w, hw.symm⟩

theorem c₀_signedCoords [Finite K] (F : Frame K) :
    IsSignedCoords (c₀ F).range (c₀ F) :=
  ⟨c₀_injective F, rfl, c₀_normalizer F, exists_realizer F⟩

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
