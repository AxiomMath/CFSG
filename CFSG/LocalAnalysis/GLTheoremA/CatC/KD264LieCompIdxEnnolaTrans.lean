module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem compIdxEnnolaAt_of_mulEquiv {p : ℕ} {d : TauCeti.LieTypeIndex} {S S' : Type} [Group S]
    [Group S'] (e : S ≃* S') (h : CompIdxEnnolaAt p d S) : CompIdxEnnolaAt p d S' := by
  intro b hbmem hbp hb1 K' hK'
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hαp : α ^ p = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hbp
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (fixSubgroup b).map (e.symm : S' →* S) = fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hKcomp : IsComponentOf K (fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  obtain ⟨i, ⟨φ⟩, j, hj, hrel⟩ := h α hαmem hαp hα1 K hKcomp
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  refine ⟨i, ⟨?_, j, hj, hrel⟩⟩
  let ε : ↥K ≃* ↥K' :=
    (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
  exact ⟨(QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K') ε
    (Subgroup.map_center_eq ε)).symm.trans φ⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
