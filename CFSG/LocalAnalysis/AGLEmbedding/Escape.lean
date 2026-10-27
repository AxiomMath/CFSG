module

public import CFSG.LocalAnalysis.AGLEmbedding.CharCore
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.AGLEmbedding.Statements
public import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

structure D1Escape {G : Type*} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M H R : Subgroup G) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  sylow_le : (P : Subgroup G) ≤ M
  weakCore_le : GLBWeakCore p (P : Subgroup G) ≤ M
  maxTwoLocal_M : GLBIsMaxTwoLocal M
  maxTwoLocal_H : GLBIsMaxTwoLocal H
  le_H : R ≤ H
  le_P : R ≤ (P : Subgroup G)
  isSylow : ∃ T : Sylow p H, (T : Subgroup H).map H.subtype = R
  three_le_pRank : 3 ≤ pRank p R
  not_le : ¬ H ≤ M

namespace D1Escape

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem le_M (h : D1Escape p P M H R) : R ≤ M := h.le_P.trans h.sylow_le

theorem le_inf (h : D1Escape p P M H R) : R ≤ H ⊓ M := _root_.le_inf h.le_H h.le_M

theorem three_le_pRank_inf (h : D1Escape p P M H R) : 3 ≤ pRank p (H ⊓ M) :=
  h.three_le_pRank.trans (pRank_mono p h.prime h.le_inf)

theorem primeCore_le (h : D1Escape p P M H R) : GLBPrimeCore p H ≤ M :=
  intersecting_local_primeCore_le p h.prime P h.sylow_le h.weakCore_le h.three_le_pRank_inf

theorem twoCore_le (h : D1Escape p P M H R) : pCoreOf 2 H ≤ M :=
  intersecting_local_twoCore_le p h.prime h.ne_two P h.sylow_le h.weakCore_le
    h.three_le_pRank_inf

theorem normalizer_le (h : D1Escape p P M H R) : Subgroup.normalizer (R : Set G) ≤ M :=
  (normalizer_le_weakCore p h.le_P (by have := h.three_le_pRank; omega)
    (h.three_le_pRank.trans (pRank_mono p h.prime le_sup_left))).trans h.weakCore_le

theorem inf_lt_left (h : D1Escape p P M H R) : H ⊓ M < H :=
  lt_of_le_of_ne inf_le_left fun heq => h.not_le (inf_eq_left.mp heq)

theorem inf_lt_right (h : D1Escape p P M H R) : H ⊓ M < M := by
  refine lt_of_le_of_ne inf_le_right fun heq => h.not_le ?_
  have hMH : M ≤ H := heq ▸ inf_le_left
  exact (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 hMH).le

theorem cgsIn_eq (h : D1Escape p P M H R) :
    CFSG.Quasithin.cgsIn M (pCoreOf 2 H) = M ⊓ H :=
  maxTwoLocal_cgsIn_eq_inf h.maxTwoLocal_H M

theorem twoCore_inf_eq_of_hasPrimeConstraint (h : D1Escape p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := by
  obtain ⟨T, hT⟩ := h.isSylow
  exact (primeCore_twoCore_eq_of_hasPrimeConstraint h.prime h.ne_two hcon T
    (hT ▸ h.le_M) h.primeCore_le).2

end D1Escape

theorem D1Escape.of_maxCase {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M) {H : Subgroup G}
    (hH : GLBIsMaxTwoLocal H) (T : Sylow p H) (hTP : (T : Subgroup H).map H.subtype ≤ P)
    (hTrank : 3 ≤ pRank p ((T : Subgroup H).map H.subtype)) (hnot : ¬ H ≤ M) :
    D1Escape p P M H ((T : Subgroup H).map H.subtype) where
  prime := hloc.beta.1
  ne_two := hloc.beta.2.1
  sylow_le := by
    have : Fact p.Prime := ⟨hloc.beta.1⟩
    have hPrank : 3 ≤ pRank p (P : Subgroup G) := by
      rw [pRank_sylow_eq_globalRank p hloc.beta.1 P]
      exact hTrank.trans (pRank_mono p hloc.beta.1 le_top)
    exact (subgroup_le_weakCore_of_rank p hloc.beta.1 _ hPrank).trans hloc.core
  weakCore_le := hloc.core
  maxTwoLocal_M := hloc.maxLocal
  maxTwoLocal_H := hH
  le_H := Subgroup.map_subtype_le _
  le_P := hTP
  isSylow := ⟨T, rfl⟩
  three_le_pRank := hTrank
  not_le := hnot

end CFSG.AGLEmbedding
