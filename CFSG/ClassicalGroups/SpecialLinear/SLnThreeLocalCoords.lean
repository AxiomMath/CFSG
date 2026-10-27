module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalReal
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
import CFSG.GroupTheory.SignedPermFixedSpace

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsSignedCoords)
open CFSG.Open (StatedSL)

variable {K : Type} [Field K] {n : ℕ}

theorem c₀_normalizer (hn : n = 6 ∨ n = 7) :
    ∀ m ∈ Subgroup.normalizer ((c₀ K hn).range : Set ↥(StatedSL n K)),
      ∃ (τ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ v,
        m * c₀ K hn v * m⁻¹ =
          c₀ K hn (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (τ i)) := by
  intro m hm
  refine CFSG.GroupTheory.exists_signedPerm_of_conj_mem_range (StatedSL n K).subtype
    (c₀ K hn) (c₀_injective hn) ?_ m ?_
  · intro v
    rw [CFSG.GroupTheory.commonFixedVectors]
    rw [show (⋂ v, CFSG.GroupTheory.fixedVectors
          ((StatedSL n K).subtype (c₀ K hn v))) =
        {w : Fin n → K |
          ∀ v', ((c₀ K hn v' : StatedSL n K) : GL (Fin n) K).val.mulVec w = w}
        from Set.ext fun w => by
          simp [Set.mem_iInter, CFSG.GroupTheory.fixedVectors]]
    exact fix_iff hn v
  · intro v
    have h : m * c₀ K hn v * m⁻¹ ∈ (c₀ K hn).range :=
      (Subgroup.mem_set_normalizer_iff.mp hm (c₀ K hn v)).mp ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp h
    exact ⟨w, hw.symm⟩

theorem c₀_signedCoords [Finite K] (h3 : (3 : K) ≠ 0) (hn : n = 6 ∨ n = 7) :
    IsSignedCoords (c₀ K hn).range (c₀ K hn) :=
  ⟨c₀_injective hn, rfl, c₀_normalizer hn, exists_conj_c₀ h3 hn⟩

end CFSG.ClassicalGroups.SLnThreeLocal
