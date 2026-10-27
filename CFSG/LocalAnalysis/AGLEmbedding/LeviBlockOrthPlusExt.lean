module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusLevi
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusUnip

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def plusResExt {t m : ℕ} (htm : t + m = r) :
    ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) →*
      ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  (matrixEquiv r K).toMonoidHom.comp ((plusExtGL (plusResIdx_injective htm)).comp
    (matrixEquiv m K).symm.toMonoidHom)

theorem autMat_plusResExt {t m : ℕ} (htm : t + m = r)
    (h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) :
    autMat (plusResExt K htm h) = extendMat (plusResIdx_injective htm) (autMat h) := by
  have h1 : autMat h = (((matrixEquiv m K).symm h : GL _ K) : Matrix _ _ K) := by
    conv_lhs => rw [← (matrixEquiv m K).apply_symm_apply h]
    exact toMatrix'_matrixEquiv _
  rw [h1]
  exact toMatrix'_matrixEquiv _

theorem plusResExt_apply_comp {t m : ℕ} (htm : t + m = r)
    (h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (v : Fin r ⊕ Fin r → K) : plusResExt K htm h v ∘ plusResIdx htm = h (v ∘ plusResIdx htm) := by
  funext s
  rw [Function.comp_apply, apply_eq_autMat_mulVec, autMat_plusResExt, extendMat_mulVec_map,
    ← apply_eq_autMat_mulVec]

theorem plusResExt_apply_of_not_mem {t m : ℕ} (htm : t + m = r)
    (h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (v : Fin r ⊕ Fin r → K) {x : Fin r ⊕ Fin r} (hx : x ∉ Set.range (plusResIdx htm)) :
    plusResExt K htm h v x = v x := by
  rw [apply_eq_autMat_mulVec, autMat_plusResExt, extendMat_mulVec_of_not_mem _ _ _ hx]

theorem plusResExt_mem_orthogonalGroup {t m : ℕ} (htm : t + m = r)
    {h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)) :
    plusResExt K htm h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [quadPlus_eq_add_res htm, quadPlus_eq_add_res htm v, plusResExt_apply_comp,
    map_of_mem hh]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [plusResExt_apply_of_not_mem _ _ _ (low_not_mem_range_plusResIdx htm i).1,
    plusResExt_apply_of_not_mem _ _ _ (low_not_mem_range_plusResIdx htm i).2]

theorem plusResExt_mem_orthElementaryGroup [CharP K 2] {t m : ℕ} (htm : t + m = r) (hm : 3 ≤ m)
    {h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)}
    (hh : h ∈ orthElementaryGroup (quadPlus m K)) :
    plusResExt K htm h ∈ orthElementaryGroup (quadPlus r K) := by
  rw [← OrthogonalSplit.commutator_orthogonalGroup_quadPlus hm] at hh
  rw [← OrthogonalSplit.commutator_orthogonalGroup_quadPlus (by omega : 3 ≤ r)]
  have hmap : (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)).map
      (plusResExt K htm) ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := by
    rintro _ ⟨g, hg, rfl⟩
    exact plusResExt_mem_orthogonalGroup htm hg
  have h1 : plusResExt K htm h ∈ (⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)⁆).map (plusResExt K htm) :=
    ⟨h, hh, rfl⟩
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hmap hmap h1

theorem plusPos_plusResIdx {t m : ℕ} (htm : t + m = r) (x : Fin m ⊕ Fin m) :
    plusPos r (plusResIdx htm x) = t + plusPos m x := by
  rcases x with s | s
  · rw [plusResIdx_inl, plusPos_inl, plusPos_inl]
  · rw [plusResIdx_inr, plusPos_inr, plusPos_inr]
    have := s.isLt
    simp only
    omega

theorem plusCut_plusResExt {t m : ℕ} (htm : t + m = r)
    (h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) {c : ℕ}
    (hc : c ≤ t ∨ 2 * r - t ≤ c ∨ ∃ c', c = t + c' ∧ PlusCut h c') :
    PlusCut (plusResExt K htm h) c := by
  intro u w hw hu
  rw [autMat_plusResExt]
  rcases hc with hc | hc | ⟨c', rfl, hc'⟩
  · exact extendMat_apply_eq_zero _ _ (fun x hx => (mem_range_plusResIdx htm x).1 hx) _
      (Or.inl hc) hw hu
  · exact extendMat_apply_eq_zero _ _ (fun x hx => (mem_range_plusResIdx htm x).1 hx) _
      (Or.inr hc) hw hu
  · by_cases hmem : u ∈ Set.range (plusResIdx htm) ∧ w ∈ Set.range (plusResIdx htm)
    · obtain ⟨⟨s, rfl⟩, ⟨s', rfl⟩⟩ := hmem
      rw [extendMat_apply_map]
      rw [plusPos_plusResIdx] at hw hu
      exact hc' s s' (by omega) (by omega)
    · rw [not_and_or] at hmem
      rw [extendMat_apply_of_not_mem _ _ hmem, one_apply_ne]
      rintro rfl
      omega

end CFSG.AGLEmbedding.LeviBlock
