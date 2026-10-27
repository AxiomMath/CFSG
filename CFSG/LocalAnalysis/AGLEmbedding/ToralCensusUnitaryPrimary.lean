module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryInvariant

public section

namespace CFSG.AGLEmbedding

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  Matrix

theorem kitInvariantPrimarySU :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n q : ℕ), Nat.card K = q ^ 2 →
      ∀ t : StatedSU n q K,
        Squarefree (minpoly K (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) →
        ∀ W : Submodule K (Fin n → K), IsTotallyIsotropicSU q W →
          (∀ g : StatedSU n q K, Commute g t → ∀ w ∈ W,
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) →
          W = ⨆ (a ∈ primaryFactors (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
            (_ : primaryComponent (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a ≤
              W), primaryComponent (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a := by
  intro K _ _ _ n q hK t hsq W hW hC
  obtain ⟨f, hf, rfl⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    GeneralLinearGroup.toLin (t : GL (Fin n) K) with hxdef
  have hxSU : x ∈ sesqSpecialUnitaryGroup (stdHermForm h n) := by
    rw [stdHermForm_eq_gramForm, hxdef, toLin_mem_sesqSpecialUnitaryGroup_iff,
      ← unitarySU_eq_gramSU h]
    exact t.2
  have hx : (x : Module.End K (Fin n → K)) =
      mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    GeneralLinearGroup.coe_toLin _
  rw [← hx] at hsq ⊢
  have H : UnitaryPrimaryData h.bar (stdHermForm h n) x :=
    ⟨fun c => h.bar_bar c, stdHermForm_isSymm h n, stdHermForm_separatingLeft h n,
      sesqSpecialUnitaryGroup_le _ hxSU, hsq⟩
  refine ToralCensus.eq_iSup_primaryComponent_of_forall_commute h H
    (mem_sesqSpecialUnitaryGroup.mp hxSU).2 ((ToralCensus.isTotallyIsotropicSU_iff h W).mp hW)
    fun g hg hgx w hw => ?_
  set A := GeneralLinearGroup.toLin.symm g with hAdef
  have hgA : g = GeneralLinearGroup.toLin A := (MulEquiv.apply_symm_apply _ _).symm
  have hA : A ∈ StatedSU n (2 ^ f) K := by
    rw [hgA, stdHermForm_eq_gramForm, toLin_mem_sesqSpecialUnitaryGroup_iff] at hg
    rwa [← unitarySU_eq_gramSU h] at hg
  have hcomm : Commute (⟨A, hA⟩ : StatedSU n (2 ^ f) K) t := by
    have h1 : GeneralLinearGroup.toLin (A * (t : GL (Fin n) K)) =
        GeneralLinearGroup.toLin ((t : GL (Fin n) K) * A) := by
      rw [map_mul, map_mul, ← hgA, ← hxdef]
      exact Units.ext hgx.eq
    exact Subtype.ext (GeneralLinearGroup.toLin.injective h1)
  rw [hgA]
  exact hC ⟨A, hA⟩ hcomm w hw

theorem exists_eq_iSup_primaryComponent_of_normalizer_le {K : Type} [Field K] [Finite K]
    [CharP K 2] {n q : ℕ} (hK : Nat.card K = q ^ 2) {J : Subgroup (StatedSU n q K)}
    {S₀ : Sylow 2 (StatedSU n q K)}
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU n q K)) : Set (StatedSU n q K)) ≤ J)
    (hJ : J ≠ ⊤) (t : StatedSU n q K)
    (hsq : Squarefree (minpoly K (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (htJ : ∀ g : StatedSU n q K, Commute g t → g ∈ J) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ IsTotallyIsotropicSU q W ∧
      (∀ y ∈ J, ∀ w ∈ W, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) ∧
      W = ⨆ (a ∈ primaryFactors (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
        (_ : primaryComponent (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a ≤
          W), primaryComponent (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a := by
  obtain ⟨W, hW0, hWt, hJW⟩ := exists_isTotallyIsotropicSU_of_normalizer_le hK hNJ hJ
  exact ⟨W, hW0, hWt, hJW, kitInvariantPrimarySU K n q hK t hsq W hWt
    fun g hg => hJW g (htJ g hg)⟩

end CFSG.AGLEmbedding
