module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorRightOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairRightCoset
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssembly

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem exists_sylow_map_eq_of_eq {p : ℕ} {X Y : Subgroup G} (hXY : X = Y) (T : Sylow p X) :
    ∃ T' : Sylow p Y, (T' : Subgroup Y).map Y.subtype = (T : Subgroup X).map X.subtype := by
  subst hXY
  exact ⟨T, rfl⟩

theorem omega_one_sylow_eq_of_normal_elementary {P U : Subgroup G} (hUP : U ≤ P)
    (hnormal : (U.subgroupOf P).Normal) (helem : IsElementaryAbelian 2 U)
    (hinv : ∀ x ∈ P, orderOf x = 2 → x ∈ U) (R : Sylow 2 P) :
    (CFSG.omega₁ (G := R) (p := 2)).map (P.subtype.comp (R : Subgroup P).subtype) = U := by
  have hUR : U.subgroupOf P ≤ R := by
    have : (U.comap P.subtype).Normal := hnormal
    exact (IsElementaryAbelian.isPGroup 2 U).comap_subtype.le_sylow_of_normal R
  change (Subgroup.closure {x : R | x ^ 2 ^ 1 = 1}).map _ = U
  rw [MonoidHom.map_closure]
  convert Subgroup.closure_eq U using 2
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change ((r : P) : G) ∈ (U : Set G)
    by_cases h1 : ((r : P) : G) = 1
    · rw [h1]
      exact U.one_mem
    · refine hinv ((r : P) : G) (r : P).2 (orderOf_eq_prime ?_ h1)
      have h := congrArg (fun y : R => ((y : P) : G)) hr
      simpa using h
  · intro hx
    refine ⟨⟨⟨x, hUP hx⟩, hUR (Subgroup.mem_subgroupOf.mpr hx)⟩, ?_, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian (A := U) x hx

theorem inter_mul_centralizer_inf_eq {A L M : Subgroup G} (hA : A ≤ M) (hL : L ≤ M) :
    (A : Set G) ∩ ((L : Set G) * ((M ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) =
      (A : Set G) ∩ ((L : Set G) * (Subgroup.centralizer (L : Set G) : Set G)) := by
  ext x
  constructor
  · rintro ⟨hxA, l, hl, c, hc, rfl⟩
    exact ⟨hxA, l, hl, c, hc.2, rfl⟩
  · rintro ⟨hxA, l, hl, c, hc, rfl⟩
    have hcM : c ∈ M := by
      simpa using M.mul_mem (M.inv_mem (hL hl)) (hA hxA)
    exact ⟨hxA, l, hl, c, ⟨hcM, hc⟩, rfl⟩

variable [Finite G]

theorem rightCosetTranslate_faithful {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) :
    ∀ g : G, (∀ ω : rightCosetSpace H, rightCosetTranslate H ω g = ω) → g = 1 := by
  obtain ⟨hsimple, -⟩ := minimalLocalFailure_nonabelian_simple h
  intro g hg
  have hcore : g ∈ H.normalCore := (point_right_coset_kernel_iff H g).mp fun ω => by
    rw [pointRightCosetMul_eq_translate]
    exact hg ω
  rcases H.normalCore_normal.eq_bot_or_eq_top with hbot | htop
  · rw [hbot] at hcore
    exact Subgroup.mem_bot.mp hcore
  · exact absurd (top_le_iff.mp (htop ▸ H.normalCore_le)) h.local_datum.proper

theorem involution_conjugate_into_point_centralizer_sylow
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : pointRightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (hfix : elementFixedSet H u =
      numeratorRightOrbit H (Subgroup.centralizer ({u} : Set G)) (rightCosetMk H 1))
    (T₁ : Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G))) {v : G} (hv : orderOf v = 2) :
    ∃ g : G, g⁻¹ * v * g ∈
      (T₁ : Subgroup ↥(H ⊓ Subgroup.centralizer ({u} : Set G))).map
        (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype := by
  let M := Subgroup.centralizer ({u} : Set G)
  have hdoubly := (minimalLocalFailureSylowFixedPointsFromProperCommutingImages h hcomm).2.2.1
  have hdoubly' : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d := by
    intro a b c d hab hcd
    obtain ⟨g, hac, hbd⟩ := hdoubly a b c d hab hcd
    rw [pointRightCosetMul_eq_translate] at hac hbd
    exact ⟨g, hac, hbd⟩
  have hrank : CFSG.Open.pRank 2
      (rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta) = 1 := by
    rw [pRank_subgroup_eq_internal_top 2 (by norm_num)]
    exact hpairRank
  have htransitive : ∀ γ δ : rightCosetSpace H, rightCosetTranslate H γ u = γ →
      rightCosetTranslate H δ u = δ → ∃ c ∈ M, rightCosetTranslate H γ c = δ := by
    intro γ δ hγ hδ
    have hγ' : γ ∈ elementFixedSet H u := by
      change pointRightCosetMul H γ u = γ
      rwa [pointRightCosetMul_eq_translate]
    have hδ' : δ ∈ elementFixedSet H u := by
      change pointRightCosetMul H δ u = δ
      rwa [pointRightCosetMul_eq_translate]
    rw [hfix] at hγ' hδ'
    obtain ⟨c₁, hc₁, rfl⟩ := hγ'
    obtain ⟨c₂, hc₂, rfl⟩ := hδ'
    refine ⟨c₁⁻¹ * c₂, M.mul_mem (M.inv_mem hc₁) hc₂, ?_⟩
    rw [← pointRightCosetMul_eq_translate, pointRightCosetMul_mul, mul_inv_cancel_left]
  have hstab : H ⊓ M = M ⊓ rightCosetStabilizer H (rightCosetMk H 1) := by
    rw [rightCosetStabilizer_base, inf_comm]
  obtain ⟨T', hT'⟩ := exists_sylow_map_eq_of_eq hstab T₁
  obtain ⟨g, hg⟩ := rightCoset_odd_degree_rank_one_pair_centralizer_meets_involution_classes H
    (rightCosetTranslate_faithful h) hdoubly'
    (LocalCriterionSubgroupSylow.local_embedding_index_odd h.local_datum) hbeta.symm hrank huB hu
    htransitive T' v hv
  exact ⟨g, hT' ▸ hg⟩

end CFSG.ProperTwoGeneratedCore.RankOnePair
