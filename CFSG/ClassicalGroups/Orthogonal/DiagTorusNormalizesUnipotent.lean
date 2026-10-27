module

public import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open Matrix

variable {m : ℕ} {F : Type} [Field F]

theorem toLinEquiv_diagGLPlusHom (d : Fin m → Fˣ) :
    toLinEquiv (Fin m ⊕ Fin m) F (diagGLPlusHom m F d) = torusElt m F d := by
  ext v c
  rw [toLinEquiv_apply, coe_diagGLPlusHom, Matrix.mulVec_diagonal, torusElt_apply]
  rcases c with i | i <;> rfl

theorem diagTorusOrth_le_normalizer_plusDerivedUnipotent {m : ℕ} (hm : 4 ≤ m) {F : Type}
    [Field F] [Finite F] [CharP F 2] :
    diagTorusOrth (m := m) (F := F) ≤
      Subgroup.normalizer (plusDerivedUnipotent m F : Set (StatedOmega (StatedQuadPlus m F))) := by
  have h3 : 3 ≤ m := by omega
  have hTorus : ∀ t : StatedOmega (StatedQuadPlus m F), t ∈ diagTorusOrth m F →
      (plusDerivedEquiv m F h3 t).val ∈ posBorel m F := by
    intro t ht
    have ht' : (t : GL (Fin m ⊕ Fin m) F) ∈ diagTorusPlus m F := by
      simpa [diagTorusOrth, Subgroup.mem_subgroupOf] using ht
    obtain ⟨d, hd⟩ := ht'
    have htdiag : toLinEquiv (Fin m ⊕ Fin m) F (t : GL (Fin m ⊕ Fin m) F) =
        torusElt m F d := by
      rw [← hd]
      exact toLinEquiv_diagGLPlusHom d
    rw [plusDerivedEquiv_val, htdiag]
    exact torusElt_mem_posBorel d
  have hConj : ∀ t ∈ diagTorusOrth m F, ∀ u ∈ plusDerivedUnipotent m F,
      t * u * t⁻¹ ∈ plusDerivedUnipotent m F := by
    intro t ht u hu
    have hB := hTorus t ht
    have huMat : (u : GL (Fin m ⊕ Fin m) F) ∈ plusMatrixUnipotent m F :=
      Subgroup.mem_subgroupOf.mp hu
    have huLin : toLinEquiv (Fin m ⊕ Fin m) F (u : GL (Fin m ⊕ Fin m) F) ∈ posUnip m F :=
      Subgroup.mem_comap.mp huMat
    have huPos : (plusDerivedEquiv m F h3 u).val ∈ posUnip m F := by
      simpa [plusDerivedEquiv_val] using huLin
    have hmem : plusDerivedEquiv m F h3 (t * u * t⁻¹) ∈
        (plusDerivedUnipotent m F).map (plusDerivedEquiv m F h3).toMonoidHom := by
      rw [plusDerivedUnipotent_map (n := m) (K := F) h3, Subgroup.mem_subgroupOf]
      have hconj : (plusDerivedEquiv m F h3 (t * u * t⁻¹)).val =
          (plusDerivedEquiv m F h3 t).val * (plusDerivedEquiv m F h3 u).val *
            ((plusDerivedEquiv m F h3 t).val)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        rfl
      rw [hconj]
      exact conj_mem_posUnip hB huPos
    exact (Subgroup.mem_map_iff_mem (plusDerivedEquiv m F h3).injective).mp hmem
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact hConj h hh u
  · intro hu
    have hz := hConj h⁻¹ (inv_mem hh) (h * u * h⁻¹) hu
    have heq : h⁻¹ * (h * u * h⁻¹) * h = u := by group
    simpa [heq] using hz

end CFSG.ClassicalGroups.Orthogonal
