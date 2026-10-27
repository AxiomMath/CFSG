module

public import CFSG.LocalAnalysis.SectionRank.QTK.EvenPlus8M
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenIsom
public import CFSG.LocalAnalysis.SectionRank.QTK.Witness3
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.SectionRank.QTK

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

variable (K : Type) [Field K] [CharP K 2]

@[expose] noncomputable def castGLι {ι : Type} [Fintype ι] [DecidableEq ι] :
    GL ι (ZMod 2) →* GL ι K :=
  Units.map (RingHom.mapMatrix (cast2 K)).toMonoidHom

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem coe_castGLι (A : GL ι (ZMod 2)) :
    ((castGLι K A : GL ι K) : Matrix ι ι K) = castMat K (A : Matrix ι ι (ZMod 2)) :=
  rfl

theorem castGLι_injective : Function.Injective (castGLι K (ι := ι)) := by
  intro A B h
  apply Units.ext
  have h' := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
  simp only [coe_castGLι] at h'
  exact Matrix.map_injective (ZMod.castHom_injective K) h'

theorem castGLι_isometry {M : GL (Fin 4 ⊕ Fin 4) (ZMod 2)}
    (hM : PlusBasisIsom (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)))
    (v : Fin 4 ⊕ Fin 4 → K) :
    StatedQuadPlus 4 K ((castGLι K M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) =
      StatedQuadPlus 4 K v := by
  rw [coe_castGLι, ← CFSG.LieType.Universal.Spin.coe_quadPlus 4 K]
  exact isometry_castMat_of_basis (CFSG.LieType.Universal.Spin.quadPlus 4 K)
    (StatedQuadPlus 4 (ZMod 2)) (fun w => by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      exact statedQuadPlus_comp_cast w) _ hM.1 hM.2 v

theorem three_le_localRank_statedOmega_of_plusHom [Finite K] {Q : (ι → K) → K}
    (φ : GL (Fin 4 ⊕ Fin 4) K →* GL ι K) (hφ : Function.Injective φ)
    (hQ : ∀ g : GL (Fin 4 ⊕ Fin 4) K,
      (∀ v, StatedQuadPlus 4 K ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) =
        StatedQuadPlus 4 K v) → ∀ v, Q ((φ g : Matrix ι ι K) *ᵥ v) = Q v) :
    3 ≤ localRank 3 ↥(StatedOmega Q) := by
  obtain ⟨h3, h1, h2, hZA, hZZ, hAZ⟩ := plus₃_relations
  obtain ⟨ht, ht2, htc, hZt⟩ := plus_involution
  obtain ⟨hZ, hA, hX₁, hX₂⟩ := plus_basisIsom
  set π := φ.comp (castGLι K)
  have hcomm : ∀ {a b : GL (Fin 4 ⊕ Fin 4) (ZMod 2)},
      PlusBasisIsom (a : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) →
      PlusBasisIsom (b : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) →
      π ⁅a, b⁆ ∈ StatedOmega Q := fun ha hb => by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure (hQ _ (castGLι_isometry K ha)))
      (Subgroup.subset_closure (hQ _ (castGLι_isometry K hb)))
  refine le_localRank_of_witness_involution π ?_ plusZ₃ plusA₃ h3 h1 h2 hZA hZZ ht2 ?_ hZt ?_ ?_
  · rw [(MonoidHom.ker_eq_bot_iff π).2 (hφ.comp (castGLι_injective K))]
    exact bot_le
  · intro h
    exact htc (Subgroup.mem_center_iff.1 h pRg₁).symm
  · intro i
    rw [← hAZ i]
    exact hcomm (hA i) (hZ i)
  · rw [← ht]
    exact hcomm hX₁ hX₂

end CFSG.SectionRank.QTK
