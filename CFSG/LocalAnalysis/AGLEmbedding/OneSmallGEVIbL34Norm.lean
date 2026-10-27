module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34PU
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUCons
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.normalizer_twoCore_inf_le_ib (hUE : KFactUPrimeExc)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K)
    (hp3 : p = 3) (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H := by
  by_contra hN
  refine hd.false_of_l34_pu_ib hUE hO hNO h93 hD2 hp3 hL hS fun C hCU hC1 hchar hHC => hN ?_
  have hNC : Subgroup.normalizer (C : Set G) = H :=
    hd.cfg.ext.maxTwoLocal_H.2 _
      ⟨C, hC1, (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).to_le hCU,
        rfl⟩ hHC
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := pCoreOf 2 (H ⊓ M)) (C.subgroupOf (pCoreOf 2 (H ⊓ M)))
  rw [Subgroup.map_subgroupOf_eq_of_le hCU] at h1
  exact h1.trans hNC.le

theorem D1OneSmallData.normalizer_twoCore_inf_eq_ib (hUE : KFactUPrimeExc)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K)
    (hp3 : p = 3) (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M ∧
      M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M ∧
      pCoreOf 2 (M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G)) = pCoreOf 2 (H ⊓ M) ∧
      pCoreOf 2 M ≤ pCoreOf 2 (H ⊓ M) := by
  have hNH := hd.normalizer_twoCore_inf_le_ib hUE hO hNO h93 hD2 hp3 hL hS
  have hNHM := hd.inf_normalizer_twoCore_inf hUE hp3 hL hS
  have hN : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M :=
    (inf_eq_right.mpr hNH).symm.trans hNHM
  have hNM : M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M := by
    rw [hN, inf_comm, inf_assoc, inf_idem]
  exact ⟨hN, hNM, by rw [hNM], pCoreOf_two_le_of_normalizer_le hNH⟩

theorem D1OneSmallData.mSideAt_twoCore_inf_ib (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3)
    (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hA : Asc81bHyp M (pCoreOf 2 (H ⊓ M))) : D1MSideAt M (pCoreOf 2 (H ⊓ M)) := by
  obtain ⟨hN, -, -, hQU⟩ := hd.normalizer_twoCore_inf_eq_ib hUE hO hNO h93 hD2 hp3 hL hS
  refine ⟨(hd.cfg.ext.isKGroup_of_isKProper hd.cfg.glob.kProper).1, hd.cfg.glob.toAGLGlobal,
    hd.cfg.ext.maxTwoLocal_M, hA, hQU, fun hle => ?_⟩
  have hUQ : pCoreOf 2 (H ⊓ M) = pCoreOf 2 M := le_antisymm hle hQU
  have hNM : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
    (maxTwoLocal_eq_normalizer_pCoreOf M hd.cfg.ext.maxTwoLocal_M).symm
  rw [hUQ, hNM] at hN
  exact hd.cfg.ext.inf_lt_right.ne hN.symm

theorem exists_perfect_lift_of_le_barM {M X : Subgroup G} (hQX : pCoreOf 2 M ≤ X)
    {V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hVX : V ≤ barM M X) (hVp : ⁅V, V⁆ = V) :
    ∃ V₁ : Subgroup G, V₁ ≤ X ∧ ⁅V₁, V₁⁆ = V₁ ∧ Nat.card V ∣ Nat.card V₁ := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set Y : Subgroup ↥M := V.comap mk
  have hYV : Y.map mk = V := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) V
  set W := perfectCore Y
  have hWV : W.map mk = V := by
    rw [map_perfectCore, hYV]
    exact perfectCore_eq_self_of_perfect hVp
  refine ⟨W.map M.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact coe_mem_of_mk_mem_barM hQX m (hVX (perfectCore_le Y hm))
  · rw [← Subgroup.map_commutator, perfectCore_perfect]
  · rw [Subgroup.card_map_of_injective M.subtype_injective, ← hWV]
    exact Subgroup.card_map_dvd W mk

theorem D1OneSmallData.not_nine_dvd_card_barM (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hQ : pCoreOf 2 M ≤ H ⊓ M) :
    ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ¬ 3 ^ 2 ∣ Nat.card V := by
  intro V hV hVp h9
  obtain ⟨V₁, hV₁, hV₁p, hdvd⟩ := exists_perfect_lift_of_le_barM hQ hV hVp
  exact hd.not_nine_dvd_card_of_perfect hUE hSch hΓ3 hp3 hL hR hV₁ hV₁p
    ((by norm_num : (9 : ℕ) = 3 ^ 2) ▸ h9 |>.trans hdvd)

end CFSG.AGLEmbedding
