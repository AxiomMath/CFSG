module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRealizers
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
import CFSG.GroupTheory.SignedPermFixedSpace

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsSignedCoords)
open CFSG.GroupTheory
open Matrix

variable {K : Type} [Field K] {b c : K}

theorem c₀_normalizer [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ m ∈ Subgroup.normalizer ((c₀ h3 hbc).range : Set ↥(omegaMinus8 K b c)),
      ∃ (τ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ v,
        m * c₀ h3 hbc v * m⁻¹ =
          c₀ h3 hbc (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (τ i)) := by
  have hfix : ∀ v : Multiplicative (Fin 3 → ZMod 3),
      fixedVectors ((omegaMinus8 K b c).subtype (c₀ h3 hbc v)) =
        commonFixedVectors (omegaMinus8 K b c).subtype (c₀ h3 hbc) ↔
        ∀ i, Multiplicative.toAdd v i ≠ 0 := by
    intro v
    have hcommon : commonFixedVectors (omegaMinus8 K b c).subtype (c₀ h3 hbc) =
        {w : OmegaIdx → K | ∀ v' : Multiplicative (Fin 3 → ZMod 3),
          (((c₀ h3 hbc v' : omegaMinus8 K b c) : GL OmegaIdx K) :
            Matrix OmegaIdx OmegaIdx K) *ᵥ w = w} := by
      ext w
      simp only [commonFixedVectors, Set.mem_iInter, Set.mem_setOf_eq, fixedVectors,
        Subgroup.coe_subtype]
    rw [hcommon]
    exact fix_iff h3 hbc v
  intro m hm
  exact exists_signedPerm_of_conj_mem_range (omegaMinus8 K b c).subtype (c₀ h3 hbc)
    (c₀_injective h3 hbc) hfix m fun v => by
      have h : m * c₀ h3 hbc v * m⁻¹ ∈ (c₀ h3 hbc).range :=
        (Subgroup.mem_set_normalizer_iff.mp hm (c₀ h3 hbc v)).mp ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp h
      exact ⟨w, hw.symm⟩

theorem c₀_signedCoords [Finite K] (h3 : (3 : K) ≠ 0) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSignedCoords (c₀ h3 hbc).range (c₀ h3 hbc) :=
  ⟨c₀_injective h3 hbc, rfl, c₀_normalizer h3 hbc, exists_conj_c₀_signedPerm h3 hbc⟩

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
