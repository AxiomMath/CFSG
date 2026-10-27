module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Measure

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem isKBalanced_of_central {N J M : Subgroup G} {t : G} (htN : t ∈ N)
    (hcent : ∀ n ∈ N, n * t = t * n) (ht : orderOf t = 2) (hJ : J ∈ kStarComponents N)
    (hM : M ∈ kStarComponents N) (hJM : J ≠ M) (hJ3 : 3 ≤ CFSG.pRank 2 ↥J) :
    IsKBalanced N := by
  classical
  have h2 : 2 ≤ (kStarComponents N).ncard := by
    rw [← Set.ncard_pair hJM]
    exact Set.ncard_le_ncard (Set.insert_subset hJ (Set.singleton_subset_iff.mpr hM))
  obtain ⟨Kf, hinj, hiff⟩ := Sol76T13.exists_enum_kStarComponents N
  have hKf : ∀ i, Kf i ∈ kStarComponents N := fun i => (hiff (Kf i)).mpr ⟨i, rfl⟩
  obtain ⟨i₀, hi₀⟩ := (hiff M).mp hM
  refine ⟨_, Kf, hinj, hiff, h2, fun i j hij => ?_, ⟨i₀, ?_⟩, Or.inr (Or.inl ?_)⟩
  · exact commutator_le_oddCoreIn_of_ne (hKf i).1 (hKf j).1 fun h => hij (hinj h)
  · rw [hi₀]
    have hle : J ≤ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel M :=
      le_inf ((le_twoLayerIn_of_isTwoComponentIn hJ.1).trans le_sup_right)
        (GSThmB.B5a.le_coreActionKernel_of_ne hM.1.1 hJ.1.1 hM.1.2 hJ.1.2 (Ne.symm hJM))
    have h := SectionRank.pRank_mono (by norm_num : 1 < 2) hle
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at hJ3
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
    omega
  · have htY : t ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N) :=
      mem_inf.mpr ⟨mem_sup_left (mem_oddTwoCoreIn_of_central htN hcent ht),
        mem_coreActionKernel_of_le_centralizer fun x hx =>
          mem_centralizer_singleton_iff.mpr (hcent x (solomonKStarOf_le N hx))⟩
    exact one_le_pRank_of_orderOf_eq_two (g := ⟨t, htY⟩) (by rw [Subgroup.orderOf_mk]; exact ht)

theorem eq_of_mem_kStarComponents_of_simple (h13 : Sol76T13.SolomonThm13Simple)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) {N J M : Subgroup G} {t : G}
    (htN : t ∈ N) (hcent : ∀ n ∈ N, n * t = t * n) (ht : orderOf t = 2)
    (hJ : J ∈ kStarComponents N) (hJ3 : 3 ≤ CFSG.pRank 2 ↥J) (hM : M ∈ kStarComponents N) :
    M = J := by
  by_contra hMJ
  exact h13 G inferInstance hnab hKP N
    (isKBalanced_of_central htN hcent ht hJ hM (Ne.symm hMJ) hJ3)

theorem solomonKStarOf_eq_of_simple (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog G)
    {N J : Subgroup G} {t : G} (htN : t ∈ N) (hcent : ∀ n ∈ N, n * t = t * n)
    (ht : orderOf t = 2) (hJ : J ∈ kStarComponents N) (hJ3 : 3 ≤ CFSG.pRank 2 ↥J) :
    solomonKStarOf N = J :=
  le_antisymm
    (iSup₂_le fun _ hM =>
      (eq_of_mem_kStarComponents_of_simple h13 hnab hKP htN hcent ht hJ hJ3 hM).le)
    (le_iSup₂_of_le J hJ le_rfl)

theorem solomonKStarOf_centralizer_eq_of_simple (h13 : Sol76T13.SolomonThm13Simple)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) {t : G} (ht : orderOf t = 2)
    {J : Subgroup G} (hJ : J ∈ kStarComponents (centralizer ({t} : Set G)))
    (hJ3 : 3 ≤ CFSG.pRank 2 ↥J) : solomonKStarOf (centralizer ({t} : Set G)) = J :=
  solomonKStarOf_eq_of_simple h13 hnab hKP (mem_centralizer_singleton_iff.mpr rfl)
    (fun _ hn => mem_centralizer_singleton_iff.mp hn) ht hJ hJ3

end CFSG.ComponentClassification.Sol76
