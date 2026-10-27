module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Rank

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem exists_enum_kStarComponents (N' : Subgroup G) :
    ∃ (K : Fin (kStarComponents N').ncard → Subgroup G), Function.Injective K ∧
      ∀ J : Subgroup G, (IsTwoComponentIn J N' ∧ J ∈ solomonKStar G) ↔ ∃ i, K i = J := by
  classical
  set S := kStarComponents N' with hS
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥S
  have hr : S.ncard = r := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fin]
  rw [hr]
  refine ⟨fun i => (e.symm i : Subgroup G), fun i j h => e.symm.injective (Subtype.ext h), ?_⟩
  intro J
  constructor
  · intro hJ
    exact ⟨e ⟨J, hJ⟩, by simp only [Equiv.symm_apply_apply]⟩
  · rintro ⟨i, rfl⟩
    exact (e.symm i).2

theorem isKBalanced_of_three_le_ncard (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G)
    {N' : Subgroup G} (h3 : 3 ≤ (kStarComponents N').ncard) : IsKBalanced N' := by
  classical
  obtain ⟨Kf, hinj, hiff⟩ := exists_enum_kStarComponents N'
  have hKf : ∀ i, Kf i ∈ kStarComponents N' := fun i => (hiff (Kf i)).mpr ⟨i, rfl⟩
  obtain ⟨X, hX, Y, hY, Z, hZ, hXY, hXZ, hYZ⟩ := (Set.two_lt_ncard (Set.toFinite _)).mp h3
  refine ⟨_, Kf, hinj, hiff, by omega, ?_, ?_, Or.inl h3⟩
  · intro i j hij
    exact FooteLit.commutator_le_oddCoreIn_of_ne (hKf i).1 (hKf j).1 fun h => hij (hinj h)
  · obtain ⟨i, hi⟩ := (hiff Z).mp hZ
    refine ⟨i, ?_⟩
    rw [hi, SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
    have hle : X ⊔ Y ≤ (oddTwoCoreIn N' ⊔ twoLayerIn N') ⊓ coreActionKernel Z := by
      refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
      · exact (le_twoLayerIn_of_isTwoComponentIn hX.1).trans le_sup_right
      · exact GSThmB.B5a.le_coreActionKernel_of_ne hZ.1.1 hX.1.1 hZ.1.2 hX.1.2 (Ne.symm hXZ)
      · exact (le_twoLayerIn_of_isTwoComponentIn hY.1).trans le_sup_right
      · exact GSThmB.B5a.le_coreActionKernel_of_ne hZ.1.1 hY.1.1 hZ.1.2 hY.1.2 (Ne.symm hYZ)
    obtain ⟨t, htX, ht2, htc⟩ := exists_noncentral_involution_of_isTwoComponentIn hq hX.1
      (catalog_coreQuotient_of_mem_solomonKStar hKK hX.1 hX.2)
      (two_le_pRank_of_mem_solomonKStar hX.2)
    exact (three_le_pRank_sup_of_isTwoComponentIn hX.1 hY.1 hXY htX ht2 htc
      (two_le_pRank_of_mem_solomonKStar hY.2)).trans (SectionRank.pRank_mono (by norm_num) hle)

theorem ncard_le_of_isSolomonChoice {N N' : Subgroup G} (hN : IsSolomonChoice N)
    (hN' : IsKBalanced N') (hv : ¬ solomonKStarOf N' ≤ solomonKStarOf (⊤ : Subgroup G)) :
    (kStarComponents N').ncard ≤ (kStarComponents N).ncard := by
  have hmeas := hN.2.2 N' hN' hv
  unfold kStarMeasure at hmeas
  exact (Prod.Lex.toLex_le_toLex'.mp hmeas).1

theorem kernel_measure_le_of_isSolomonChoice {N N' : Subgroup G} (hN : IsSolomonChoice N)
    (hN' : IsKBalanced N') (hv : ¬ solomonKStarOf N' ≤ solomonKStarOf (⊤ : Subgroup G))
    (heq : (kStarComponents N').ncard = (kStarComponents N).ncard) :
    CFSG.pRank 2 ↥(kStarKernel N') ≤ CFSG.pRank 2 ↥(kStarKernel N) ∧
      (CFSG.pRank 2 ↥(kStarKernel N') = CFSG.pRank 2 ↥(kStarKernel N) →
        (Nat.card ↥(kStarKernel N')).factorization 2 ≤
          (Nat.card ↥(kStarKernel N)).factorization 2) := by
  have hmeas := hN.2.2 N' hN' hv
  unfold kStarMeasure at hmeas
  have h2 := (Prod.Lex.toLex_le_toLex'.mp hmeas).2 heq
  exact Prod.Lex.toLex_le_toLex'.mp h2

end CFSG.ComponentClassification.Sol76T13
