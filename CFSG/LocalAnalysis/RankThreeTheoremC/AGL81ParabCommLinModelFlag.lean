module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinModelMat
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LeviBlock
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

section Flag

variable {K : Type*} [Field K] {n : ℕ} {I : Set ℕ}

theorem finrank_map_mulVecLin_gl (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) =
      Module.finrank K W := by
  have hinj : Function.Injective (mulVecLin (A : Matrix (Fin n) (Fin n) K)) :=
    Matrix.mulVec_injective_iff_isUnit.2 A.isUnit
  exact (Submodule.equivMapOfInjective _ hinj W).finrank_eq.symm

theorem blockPat_of_mulVec_mem {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ c ∈ I, ∀ v ∈ flagSpace n K c, M *ᵥ v ∈ flagSpace n K c) : BlockPat I M := by
  intro c hc k l hl hk
  have hv : (Pi.single l (1 : K) : Fin n → K) ∈ flagSpace n K c :=
    Submodule.subset_span ⟨l, hl, rfl⟩
  have h1 := hM c hc _ hv
  rw [mem_flagSpace] at h1
  have h2 := h1 k hk
  rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h2

theorem blockPat_of_conj_mem (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (A : GL (Fin n) K)
    (hconj : ∀ g ∈ flagStabilizer n K I, slConjugation n K A g ∈ flagStabilizer n K I) :
    BlockPat I ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      BlockPat I (A : Matrix (Fin n) (Fin n) K) := by
  have hF : ∀ c ∈ I, (flagSpace n K c).map
      (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = flagSpace n K c := by
    intro c hc
    obtain ⟨hc1, hcn⟩ := hI c hc
    set W := (flagSpace n K c).map
      (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) with hW
    have hrank : Module.finrank K W = c := by
      rw [hW, finrank_map_mulVecLin_gl, finrank_flagSpace hcn.le]
    have hinv : ∀ g ∈ flagStabilizer n K I, ∀ v ∈ W,
        (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W := by
      intro g hg v hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hst := mem_stabilizer.mp (mem_flagStabilizer.mp (hconj g hg) c hc)
      have hmem : ((slConjugation n K A g : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ w ∈ flagSpace n K c := by
        have h1 : ((slConjugation n K A g : SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ w ∈ (flagSpace n K c).map (mulVecLin
              ((slConjugation n K A g : SpecialLinearGroup (Fin n) K) :
                Matrix (Fin n) (Fin n) K)) := ⟨w, hw, rfl⟩
        rwa [hst] at h1
      refine ⟨_, hmem, ?_⟩
      rw [mulVecLin_apply, mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        slConjugation_matrix, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
    rcases ((subflag_stabilizer_generation (K := K) (n := n) I).2.1 W).mp hinv with
      h | h | ⟨i, hi, h⟩
    · rw [h, finrank_bot] at hrank
      omega
    · rw [h, finrank_top, Module.finrank_fin_fun] at hrank
      omega
    · have h1 := finrank_flagSpace (K := K) (hI i hi).2.le
      rw [← h, hrank] at h1
      rw [h, ← h1]
  have hA' : BlockPat I ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    refine blockPat_of_mulVec_mem fun c hc v hv => ?_
    rw [← hF c hc]
    exact ⟨v, hv, rfl⟩
  refine ⟨hA', blockPat_of_mulVec_mem fun c hc v hv => ?_⟩
  have h1 : v ∈ (flagSpace n K c).map
      (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [hF c hc]
    exact hv
  obtain ⟨w, hw, rfl⟩ := h1
  rw [mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact hw

end Flag

section Norm

variable {K : Type} [Field K] {n : ℕ} {I : Set ℕ}

theorem conj_mem_of_map_projFlag {A : GL (Fin n) K} {σ : K ≃+* K}
    (h : (projFlag K n I).map (conjAut n K A * fieldAut n K σ).toMonoidHom = projFlag K n I) :
    ∀ g ∈ flagStabilizer n K I, slConjugation n K A g ∈ flagStabilizer n K I := by
  intro g hg
  set g' : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.map σ.symm.toRingHom g with hg'
  have hg'Q : g' ∈ flagStabilizer n K I := map_mem_flagStabilizer _ hg
  have hmem : (conjAut n K A * fieldAut n K σ) (proj n K g') ∈ projFlag K n I := by
    rw [← h]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hg'Q)
  obtain ⟨h₀, hh₀, hh₀eq⟩ := Subgroup.mem_map.mp hmem
  have hσg : SpecialLinearGroup.map σ.toRingHom g' = g := by
    apply Subtype.ext
    ext i j
    simp [hg']
  have hcalc : (conjAut n K A * fieldAut n K σ) (proj n K g') =
      proj n K (slConjugation n K A g) := by
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, hσg]
  rw [hcalc] at hh₀eq
  have hz := scalars_le_flagStabilizer (n := n) (K := K) I (proj_eq_proj_iff.mp hh₀eq)
  simpa using mul_mem hh₀ hz

end Norm

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
