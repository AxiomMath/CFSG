module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralizerSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.SignalizerFunctor.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem odd_normal_le_full_core
    (S : Sylow 2 G) (hrank : 3 ≤ pRank 2 (S : Subgroup G))
    (R : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R)) :
    R ≤ properTwoGenCoreGamma (S : Subgroup G) 2 := by
  obtain ⟨E, hES, hE, hEcard⟩ := pRank_attained 2 (S : Subgroup G) (by omega)
  have hElarge : 2 ^ (2 + 1) ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (by decide) hrank
  have hnormal : E ≤ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  rw [← elementary_abelian_centralizer_generation 2 2 Nat.prime_two E R hE
    hElarge hnormal (Nat.coprime_two_left.mpr hRodd)]
  apply iSup_le
  intro V
  apply iSup_le
  intro hV
  have hVrank : 2 ≤ pRank 2 V := by
    exact le_csSup (pRank_set_bddAbove 2 (by decide) V)
      ⟨V, le_rfl, elementary_abelian_of_le 2 hE hV.1, hV.2⟩
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (V : Set G)).trans
    ((gamma_le_iff _ _ 2).mp le_rfl V (hV.1.trans hES) hVrank))

omit [Finite G] in
theorem quotient_normalizer_preimage_eq
    (R U : Subgroup G) [R.Normal] :
    (Subgroup.normalizer (U.map (QuotientGroup.mk' R) : Set (G ⧸ R))).comap
      (QuotientGroup.mk' R) = Subgroup.normalizer ((U ⊔ R : Subgroup G) : Set G) := by
  rw [Subgroup.comap_normalizer_eq_of_le_range (by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective R)]
    exact le_top), Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem odd_normal_normalizer_sup_eq
    (R U : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R))
    (hU : IsPGroup 2 U) :
    Subgroup.normalizer ((U ⊔ R : Subgroup G) : Set G) =
      Subgroup.normalizer (U : Set G) ⊔ R := by
  have heq := congrArg (Subgroup.comap (QuotientGroup.mk' R))
    (coprime_quotient_normalizer_image 2 Nat.prime_two R U
      (Nat.coprime_two_left.mpr hRodd) hU)
  rw [quotient_normalizer_preimage_eq, Subgroup.comap_map_eq,
    QuotientGroup.ker_mk'] at heq
  exact heq.symm

theorem sylow_subgroup_rank_eq_odd_quotient
    (S : Sylow 2 G) (R : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R))
    (U : Subgroup G) (hUS : U ≤ (S : Subgroup G)) :
    pRank 2 (U.map (QuotientGroup.mk' R)) = pRank 2 U := by
  have hkernel : Nat.Coprime 2 (Nat.card (QuotientGroup.mk' R).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mpr hRodd
  obtain ⟨e⟩ := coprime_kernel_pGroup_equiv_image 2 Nat.prime_two
    (QuotientGroup.mk' R) hkernel U (IsPGroup.to_le S.isPGroup' hUS)
  calc
    _ = twoRank (U.map (QuotientGroup.mk' R)) :=
      pRank_subgroup_eq_internal_top 2 (by decide) _
    _ = twoRank U := (pRank_top_eq_of_equiv 2 (by decide) e).symm
    _ = pRank 2 U := (pRank_subgroup_eq_internal_top 2 (by decide) U).symm

theorem gamma_image_odd_normal_quotient
    (S : Sylow 2 G) (R : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R))
    (k : ℕ) :
    (properTwoGenCoreGamma (S : Subgroup G) k).map (QuotientGroup.mk' R) =
      properTwoGenCoreGamma ((S : Subgroup G).map (QuotientGroup.mk' R)) k := by
  let pi := QuotientGroup.mk' R
  apply le_antisymm
  · change (⨆ U : Subgroup G, ⨆ (_ : U ≤ (S : Subgroup G)),
      ⨆ (_ : k ≤ pRank 2 U), Subgroup.normalizer (U : Set G)).map pi ≤ _
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro U
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hUS
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hUr
    rw [coprime_quotient_normalizer_image 2 Nat.prime_two R U
      (Nat.coprime_two_left.mpr hRodd) (IsPGroup.to_le S.isPGroup' hUS)]
    exact (gamma_le_iff _ _ k).mp le_rfl (U.map pi) (Subgroup.map_mono hUS)
      (by rwa [sylow_subgroup_rank_eq_odd_quotient S R hRodd U hUS])
  · apply (gamma_le_iff _ _ k).mpr
    intro W hWS hWr
    let U := (W.comap pi) ⊓ (S : Subgroup G)
    have hUS : U ≤ (S : Subgroup G) := inf_le_right
    have himage : U.map pi = W := by
      apply le_antisymm
      · exact (Subgroup.map_le_iff_le_comap).mpr inf_le_left
      · intro w hw
        obtain ⟨s, hs, hsw⟩ := hWS hw
        exact ⟨s, ⟨by change pi s ∈ W; rwa [hsw], hs⟩, hsw⟩
    have hUr : k ≤ pRank 2 U := by
      have hrank := sylow_subgroup_rank_eq_odd_quotient S R hRodd U hUS
      rw [himage] at hrank
      rwa [← hrank]
    rw [← himage, ← coprime_quotient_normalizer_image 2 Nat.prime_two R U
      (Nat.coprime_two_left.mpr hRodd) (IsPGroup.to_le S.isPGroup' hUS)]
    exact Subgroup.map_mono ((gamma_le_iff _ _ k).mp le_rfl U hUS hUr)

theorem full_core_eq_top_iff_odd_normal_quotient
    (S : Sylow 2 G) (hrank : 3 ≤ pRank 2 (S : Subgroup G))
    (R : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R)) :
    properTwoGenCoreGamma (S : Subgroup G) 2 = ⊤ ↔
      properTwoGenCoreGamma ((S : Subgroup G).map (QuotientGroup.mk' R)) 2 = ⊤ := by
  rw [← gamma_image_odd_normal_quotient S R hRodd 2]
  constructor
  · intro htop
    rw [htop]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)
  · intro htop
    have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' R)) htop
    rw [Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk',
      sup_eq_left.mpr (odd_normal_le_full_core S hrank R hRodd)] at hcomap
    exact hcomap

theorem odd_normal_full_core_quotient
    (S : Sylow 2 G) (hrank : 3 ≤ twoRank G)
    (R : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R)) :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective R)
    let K := properTwoGenCoreGamma (S : Subgroup G) 2
    let Kbar := properTwoGenCoreGamma (Sbar : Subgroup (G ⧸ R)) 2
    R ≤ K ∧ K.map (QuotientGroup.mk' R) = Kbar ∧ (K = ⊤ ↔ Kbar = ⊤) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSr : 3 ≤ pRank 2 (S : Subgroup G) := by rwa [sylow_two_rank_eq]
  dsimp only
  rw [Sylow.coe_mapSurjective]
  exact ⟨odd_normal_le_full_core S hSr R hRodd,
    gamma_image_odd_normal_quotient S R hRodd 2,
    full_core_eq_top_iff_odd_normal_quotient S hSr R hRodd⟩

end CFSG.ProperTwoGeneratedCore
