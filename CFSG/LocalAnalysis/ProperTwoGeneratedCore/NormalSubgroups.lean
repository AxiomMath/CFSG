module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SubgroupNormalizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralizerSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.BenderSuzuki.External

universe u

variable {G : Type u} [Group G] [Finite G]

theorem normal_rank_two_not_le_overgroup
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (N : Subgroup G) [N.Normal] (hrank : 2 ≤ pRank 2 N) : ¬ N ≤ H := by
  intro hNH
  have hnormalizer := two_generated_core_subgroup_normalizer_le S H hSH hcore N hNH hrank
  rw [Subgroup.normalizer_eq_top] at hnormalizer
  exact hH (top_le_iff.mp hnormalizer)

theorem normal_sylow_intersection_eq
    (S : Sylow 2 G) (N : Subgroup G) [N.Normal] :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    ((hallSylowSubgroupOfNormal S N : Subgroup N).map N.subtype : Subgroup G) =
      (S : Subgroup G) ⊓ N := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hallSylowSubgroupOfNormal_coe, Subgroup.comap_subtype,
    Subgroup.subgroupOf_map_subtype]

theorem normal_subgroup_full_core_le
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (N : Subgroup G) [N.Normal] :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    properTwoGenCoreGamma (hallSylowSubgroupOfNormal S N : Subgroup N) 2 ≤
      H.subgroupOf N := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply (gamma_le_iff _ _ 2).mpr
  intro U hUT hUrank
  have himage : U.map N.subtype ≤ (S : Subgroup G) ⊓ N := by
    rw [← normal_sylow_intersection_eq S N]
    exact Subgroup.map_mono hUT
  have himageRank : 2 ≤ pRank 2 (U.map N.subtype) := by
    have heq := pRank_top_eq_of_equiv 2 (by decide)
      (U.equivMapOfInjective N.subtype N.subtype_injective)
    rw [← pRank_subgroup_eq_internal_top 2 (by decide) U,
      ← pRank_subgroup_eq_internal_top 2 (by decide) (U.map N.subtype)] at heq
    rwa [← heq]
  have hnormalizer := normalizer_le_overgroup S H 2 hSH hcore (U.map N.subtype)
    ((IsPGroup.to_le (hallSylowSubgroupOfNormal S N).isPGroup' hUT).map N.subtype)
    ((himage.trans inf_le_left).trans hSH) himageRank
  intro n hn
  exact hnormalizer (Subgroup.le_normalizer_map N.subtype
    (Subgroup.mem_map_of_mem N.subtype hn))

theorem normal_rank_two_centralizer_rank_le_one
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (N : Subgroup G) [N.Normal] (hrank : 2 ≤ pRank 2 N) :
    pRank 2 (Subgroup.centralizer (N : Set G)) ≤ 1 := by
  let C := Subgroup.centralizer (N : Set G)
  let : C.Normal := inferInstance
  by_contra hsmall
  change ¬ pRank 2 C ≤ 1 at hsmall
  have hCrank : 2 ≤ pRank 2 C := by omega
  obtain ⟨V, hVC, hV, hVcard⟩ := pRank_attained 2 C (by omega)
  obtain ⟨a, ha⟩ := pGroup_conjugate_into_sylow_within_overgroup 2 Nat.prime_two S ⊤
    le_top V (elementary_isPGroup 2 V hV) le_top
  let W := V.map (MulAut.conj (a : G)).toMonoidHom
  have hWS : W ≤ (S : Subgroup G) := ha
  have hWC : W ≤ C := by
    rintro x ⟨v, hv, rfl⟩
    exact (inferInstance : C.Normal).conj_mem v (hVC hv) (a : G)
  have hWrank : 2 ≤ pRank 2 W := by
    rw [pRank_map_automorphism 2 (by decide)]
    apply hCrank.trans
    exact le_csSup (pRank_set_bddAbove 2 (by decide) V) ⟨V, le_rfl, hV, hVcard⟩
  have hNH : N ≤ H := by
    apply le_trans _ ((gamma_le_iff _ _ 2).mp hcore W hWS hWrank)
    apply le_trans _ (Subgroup.centralizer_le_normalizer (W : Set G))
    intro n hn
    apply Subgroup.mem_centralizer_iff.mpr
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWC hw) n hn).symm
  exact normal_rank_two_not_le_overgroup S H hH hSH hcore N hrank hNH

theorem proper_full_core_normal_subgroup_restrictions
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (N : Subgroup G) [N.Normal] (hrank : 2 ≤ pRank 2 N) :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let T := hallSylowSubgroupOfNormal S N
    let J := properTwoGenCoreGamma (T : Subgroup N) 2
    (T : Subgroup N).map N.subtype = (S : Subgroup G) ⊓ N ∧
      J ≤ H.subgroupOf N ∧ H.subgroupOf N < ⊤ ∧
        pRank 2 (Subgroup.centralizer (N : Set G)) ≤ 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨normal_sylow_intersection_eq S N,
    normal_subgroup_full_core_le S H hSH hcore N, ?_,
    normal_rank_two_centralizer_rank_le_one S H hH hSH hcore N hrank⟩
  exact lt_top_iff_ne_top.mpr (fun heq =>
    normal_rank_two_not_le_overgroup S H hH hSH hcore N hrank
      (Subgroup.subgroupOf_eq_top.mp heq))

end CFSG.ProperTwoGeneratedCore
