module

public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Quotient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbedding.LieOut

section Link

variable
  {τ : Tag} {K : Type} [Field K]

theorem map_rootGroup_eq_rootSubgroup {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (rootGroup (rootOperatorFamily τ) K γ).map (adjointGroup τ K).subtype =
      Blueprint.Chevalley.rootSubgroup τ K γ := by
  have hs := (rootOperatorFamily τ).pinnedFamilySign_eq γ
  set s : K := ((rootOperatorFamily τ).pinnedFamilySign γ : K) with hsdef
  have hss : s * s = 1 := by
    rcases hs with h | h <;> simp [hsdef, h]
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup hγ hg
    refine Subgroup.subset_closure ⟨s * c, ?_⟩
    rw [(rootOperatorFamily τ).pinnedX_eq_eltUnit K hγ, ← mul_assoc, hss, one_mul]
    rfl
  · rw [Blueprint.Chevalley.rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    refine ⟨(rootOperatorFamily τ).eltElement ⟨γ, hγ⟩ (s * c), ?_, ?_⟩
    · rw [rootGroup_of_isRoot hγ]
      exact (rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _
    · rw [(rootOperatorFamily τ).pinnedX_eq_eltUnit K hγ]
      rfl

theorem map_leviRad_eq_parabolicRadical (I : Set (Fin τ.rank)) :
    (leviRad (adjDatum (rootOperatorFamily τ) K) I).map (adjointGroup τ K).subtype =
      parabolicRadical τ K I := by
  set D := adjDatum (rootOperatorFamily τ) K with hD
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun j hj => iSup₂_le fun γ hγ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hroot : IsRoot τ γ := mem_adjDatum_roots.1 hγ.1
    have hpos : 0 < γ j := hγ.2
    have hD' : (adjDatum (rootOperatorFamily τ) K).rootGroup γ =
        rootGroup (rootOperatorFamily τ) K γ := rfl
    show (D.rootGroup γ).map (adjointGroup τ K).subtype ≤ _
    rw [hD', map_rootGroup_eq_rootSubgroup hroot]
    refine le_iSup₂_of_le (f := fun α (_ : α ∈ parabolicRadicalRoots τ I) =>
      Blueprint.Chevalley.rootSubgroup τ K α) γ ?_ le_rfl
    refine ⟨⟨hroot, ?_⟩, fun h => ?_⟩
    · exact ht_pos_of_coord (D := D) hγ.1 hpos
    · have := h.1.2 j hj
      omega
  · refine iSup₂_le fun α hα => ?_
    obtain ⟨⟨hroot, hht⟩, hnot⟩ := hα
    have hαD : α ∈ D.roots := mem_adjDatum_roots.2 hroot
    obtain ⟨i, hi, hαi⟩ : ∃ i, i ∉ I ∧ α i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hnot ⟨⟨hroot, fun i hi => hcon i hi⟩, hroot, hht⟩
    have hnn := coord_nonneg_of_ht_pos (D := D) hαD hht i
    have hpos : 0 < α i := lt_of_le_of_ne hnn (Ne.symm hαi)
    rw [← map_rootGroup_eq_rootSubgroup hroot]
    exact Subgroup.map_mono ((rootGroup_le_radical (D := D) hαD hpos).trans
      (radical_le_leviRad (D := D) hi))

theorem centOb_adjoint {I : Set (Fin τ.rank)} (hI : I ≠ Set.univ) :
    CentOb (adjDatum (rootOperatorFamily τ) K) I := by
  intro k hk
  set D := adjDatum (rootOperatorFamily τ) K with hD
  have hkC : ((k : ModGL τ K)) ∈ Subgroup.centralizer (parabolicRadical τ K I : Set (ModGL τ K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [← map_leviRad_eq_parabolicRadical] at hg
    obtain ⟨u, hu, rfl⟩ := hg
    exact congrArg Subtype.val (hk u hu).symm
  have hkN : (k : ModGL τ K) ∈ adjointGroup τ K ⊓
      Subgroup.normalizer (parabolicRadical τ K I : Set (ModGL τ K)) :=
    ⟨k.2, Subgroup.centralizer_le_normalizer _ hkC⟩
  rw [adjointGroup_inf_normalizer_parabolicRadical] at hkN
  have hkQ : (k : ModGL τ K) ∈ parabolicRadical τ K I :=
    (Chevalley_proper_parabolic_root_radical_self_centralizing τ K hI).2 ⟨hkN, hkC⟩
  rw [← map_leviRad_eq_parabolicRadical] at hkQ
  obtain ⟨u, hu, huk⟩ := hkQ
  have : u = k := Subtype.ext huk
  rw [← this]
  exact Subgroup.mem_sup_left hu

end Link

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
