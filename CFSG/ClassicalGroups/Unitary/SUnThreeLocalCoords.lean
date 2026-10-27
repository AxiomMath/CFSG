module

public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalReal
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
import CFSG.GroupTheory.SignedPermFixedSpace

public section

namespace CFSG.ClassicalGroups.SUnThreeLocal

open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsSignedCoords)
open CFSG.LieType.Universal.Unitary (SU)

variable {L : Type} [Field L] {n : ℕ} {σ : L ≃+* L} (ζ : FixedCubeRoot σ)

private theorem c₀_normalizer_fixedVectors (hn : n = 6 ∨ n = 7)
    (v : Multiplicative (Fin 3 → ZMod 3)) :
    CFSG.GroupTheory.fixedVectors ((SU σ n).subtype (c₀ ζ hn v)) =
        CFSG.GroupTheory.commonFixedVectors (SU σ n).subtype (c₀ ζ hn) ↔
      ∀ i, Multiplicative.toAdd v i ≠ 0 := by
  have h₁ : CFSG.GroupTheory.fixedVectors ((SU σ n).subtype (c₀ ζ hn v)) =
      {w : Fin n → L | ((c₀ ζ hn v : SU σ n) : GL (Fin n) L).val *ᵥ w = w} := by
    ext w
    simp [CFSG.GroupTheory.fixedVectors, Subgroup.subtype_apply]
  have h₂ : CFSG.GroupTheory.commonFixedVectors (SU σ n).subtype (c₀ ζ hn) =
      {w : Fin n → L | ∀ v' : Multiplicative (Fin 3 → ZMod 3),
        ((c₀ ζ hn v' : SU σ n) : GL (Fin n) L).val *ᵥ w = w} := by
    ext w
    simp [CFSG.GroupTheory.commonFixedVectors, CFSG.GroupTheory.fixedVectors,
      Subgroup.subtype_apply]
  rw [h₁, h₂]
  exact fix_iff ζ hn v

theorem c₀_normalizer (hn : n = 6 ∨ n = 7) :
    ∀ m ∈ Subgroup.normalizer ((c₀ ζ hn).range : Set ↥(SU σ n)),
      ∃ (τ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ v,
        m * c₀ ζ hn v * m⁻¹ =
          c₀ ζ hn (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (τ i)) := by
  intro m hm
  exact CFSG.GroupTheory.exists_signedPerm_of_conj_mem_range (SU σ n).subtype (c₀ ζ hn)
    (c₀_injective ζ hn) (c₀_normalizer_fixedVectors ζ hn) m fun v => by
      have h : m * c₀ ζ hn v * m⁻¹ ∈ (c₀ ζ hn).range :=
        (Subgroup.mem_set_normalizer_iff.mp hm (c₀ ζ hn v)).mp ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp h
      exact ⟨w, hw.symm⟩

theorem c₀_signedCoords (htr : ∃ c : L, c ≠ 0 ∧ σ c = -c) (hn : n = 6 ∨ n = 7) :
    IsSignedCoords (c₀ ζ hn).range (c₀ ζ hn) :=
  ⟨c₀_injective ζ hn, rfl, c₀_normalizer ζ hn, exists_conj_c₀ ζ htr hn⟩

end CFSG.ClassicalGroups.SUnThreeLocal
