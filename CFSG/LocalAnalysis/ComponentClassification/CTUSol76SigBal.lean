module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Rank

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem isKBalanced_of_three_le (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G)
    {X : Subgroup G} (h3 : 3 ≤ (kStarComponents X).ncard) : IsKBalanced X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := kStarComponents X with hS
  obtain ⟨X₁, X₂, X₃, hX₁, hX₂, hX₃, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite S)).mp (by omega)
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥S
  set Kf : Fin r → Subgroup G := fun i => (e.symm i : Subgroup G) with hKfdef
  have hKf : ∀ i, Kf i ∈ S := fun i => (e.symm i).2
  have hinj : Function.Injective Kf := fun i j h => e.symm.injective (Subtype.ext h)
  have hiff : ∀ J : Subgroup G, (IsTwoComponentIn J X ∧ J ∈ solomonKStar G) ↔ ∃ i, Kf i = J := by
    intro J
    constructor
    · intro hJ
      refine ⟨e ⟨J, hJ⟩, ?_⟩
      simp only [hKfdef, Equiv.symm_apply_apply]
    · rintro ⟨i, rfl⟩
      exact hKf i
  have hr : S.ncard = r := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fin]
  have h3r : 3 ≤ r := hr ▸ h3
  refine ⟨r, Kf, hinj, hiff, by omega, ?_, ?_, Or.inl h3r⟩
  · intro i j hij
    exact FooteLit.commutator_le_oddCoreIn_of_ne (hKf i).1 (hKf j).1 fun h => hij (hinj h)
  ·
    obtain ⟨i, hi⟩ := (hiff X₃).mp hX₃
    refine ⟨i, ?_⟩
    rw [hi, SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
    have hle : X₁ ⊔ X₂ ≤ (oddTwoCoreIn X ⊔ twoLayerIn X) ⊓ coreActionKernel X₃ := by
      refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
      · exact (le_twoLayerIn_of_isTwoComponentIn hX₁.1).trans le_sup_right
      · exact GSThmB.B5a.le_coreActionKernel_of_ne hX₃.1.1 hX₁.1.1 hX₃.1.2 hX₁.1.2 h13.symm
      · exact (le_twoLayerIn_of_isTwoComponentIn hX₂.1).trans le_sup_right
      · exact GSThmB.B5a.le_coreActionKernel_of_ne hX₃.1.1 hX₂.1.1 hX₃.1.2 hX₂.1.2 h23.symm
    obtain ⟨t, htX, ht2, htc⟩ := exists_noncentral_involution_of_isTwoComponentIn hq hX₁.1
      (catalog_coreQuotient_of_mem_solomonKStar hKK hX₁.1 hX₁.2)
      (two_le_pRank_of_mem_solomonKStar hX₁.2)
    exact (three_le_pRank_sup_of_isTwoComponentIn hX₁.1 hX₂.1 h12 htX ht2 htc
      (two_le_pRank_of_mem_solomonKStar hX₂.2)).trans (SectionRank.pRank_mono (by norm_num) hle)

theorem two_le_ncard_kStarComponents (hN : IsSolomonChoice N) :
    2 ≤ (kStarComponents N).ncard := by
  obtain ⟨K₁, hK₁, -⟩ := exists_mem_kStarComponents_ne hN ⊥
  obtain ⟨K₂, hK₂, hK₂₁⟩ := exists_mem_kStarComponents_ne hN K₁
  rw [← Set.ncard_pair (Ne.symm hK₂₁)]
  exact Set.ncard_le_ncard (Set.insert_subset hK₁ (Set.singleton_subset_iff.mpr hK₂))

theorem ncard_kStarComponents_le_of_cover (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G)
    (hN : IsSolomonChoice N) {X : Subgroup G}
    (hcov : ∀ K ∈ kStarComponents N, ∃ K' ∈ kStarComponents X, K ≤ K') :
    (kStarComponents X).ncard ≤ (kStarComponents N).ncard := by
  by_contra hlt
  push Not at hlt
  have h2 := two_le_ncard_kStarComponents hN
  have hX := isKBalanced_of_three_le hq hKK (by omega : 3 ≤ (kStarComponents X).ncard)
  have hle : solomonKStarOf N ≤ solomonKStarOf X := iSup₂_le fun K hK => by
    obtain ⟨K', hK', hKK'⟩ := hcov K hK
    exact hKK'.trans (le_iSup₂_of_le K' hK' le_rfl)
  have hviol : ¬ solomonKStarOf X ≤ solomonKStarOf (⊤ : Subgroup G) := fun h =>
    hN.2.1 (hle.trans h)
  have hmeas := hN.2.2 X hX hviol
  apply absurd hmeas
  rw [not_le]
  unfold kStarMeasure
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)

theorem eq_kStarComponents_of_subset (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G)
    (hN : IsSolomonChoice N) {X : Subgroup G} (hsub : kStarComponents N ⊆ kStarComponents X) :
    kStarComponents X = kStarComponents N :=
  (Set.eq_of_subset_of_ncard_le hsub
    (ncard_kStarComponents_le_of_cover hq hKK hN fun K hK => ⟨K, hsub hK, le_rfl⟩)).symm

theorem mem_kStarComponents_normalizer_solomonKStarOf {K : Subgroup G}
    (hK : K ∈ kStarComponents N) :
    K ∈ kStarComponents (normalizer (solomonKStarOf N : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKD : K ≤ solomonKStarOf N := le_iSup₂_of_le K hK le_rfl
  have hKDc := isTwoComponentIn_of_le hK.1 hKD (solomonKStarOf_le N)
  have hDn : ((solomonKStarOf N).subgroupOf
      (normalizer ((solomonKStarOf N : Subgroup G) : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  refine ⟨⟨hKD.trans le_normalizer, ?_⟩, hK.2⟩
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hKD le_normalizer
    hDn.isSubnormal).mpr hKDc.2

theorem solomonKStarOf_normalizer_eq (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G)
    (hN : IsSolomonChoice N) :
    solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N := by
  have h := eq_kStarComponents_of_subset hq hKK hN
    fun K hK => mem_kStarComponents_normalizer_solomonKStarOf hK
  rw [solomonKStarOf_eq_sSup, h, ← solomonKStarOf_eq_sSup]

theorem ncard_kStarComponents_le_of_simple (hq : QuasisimpleTwoPartInput) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (X : Subgroup G) :
    (kStarComponents X).ncard ≤ (kStarComponents N).ncard := by
  have := hG.1
  by_contra hlt
  push Not at hlt
  have h2 := two_le_ncard_kStarComponents hN
  have hX := isKBalanced_of_three_le hq (kStarKProper_of_simple hG.2.1 hG.2.2)
    (by omega : 3 ≤ (kStarComponents X).ncard)
  have hmeas := hN.2.2 X hX (not_le_solomonKStarOf_top_of_simple hG hX)
  apply absurd hmeas
  rw [not_le]
  unfold kStarMeasure
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)

end CFSG.ComponentClassification.Sol76.Sig
