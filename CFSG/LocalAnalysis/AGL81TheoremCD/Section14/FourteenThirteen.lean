module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteenHs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Component
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteenI
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.OPPrimeHullStar
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Elem
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def SevenThreeInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ L : Subgroup X,
    CFSG.IsComponent L → CFSG.generalizedFitting X = L → CFSG.pPrimeCore 3 X = ⊥ →
    CFSG.Open.pRank 3 L = 3 → ∀ T Hs : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    T ≤ Hs → Nonempty (↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9)) →
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 Hs : Set X) ≤
      Subgroup.normalizer (CFSG.Quasithin.twoResidual Hs : Set X) →
    Nonempty (↥L ≃* alternatingGroup (Fin 9)) ∨ Nonempty (↥L ≃* alternatingGroup (Fin 11))

theorem pCore_three_eq_bot_of_a9 {X : Type} [Group X] [Finite X]
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {I : Subgroup X}
    (f : ↥I →* alternatingGroup (Fin 9)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : CFSG.pCore 3 X = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup X := CFSG.pCore 3 X
  have hP3 : IsPGroup 3 P := CFSG.pCore_isPGroup (p := 3) (G := X)
  have hIP : I ≤ Subgroup.normalizer (P : Set X) := Subgroup.le_normalizer_of_normal
  have hPI : P ⊓ I = ⊥ := inf_eq_bot_of_isPGroup_three_of_a9 hP3 hIP f hf hker
  obtain ⟨A, hAI, hAelem, hAcard, -⟩ :=
    exists_elemAbelian_27_disjoint_ker_of_a9 (X := X) (I := I) (f := f) hf hker
  by_contra hPne
  have hHne : P ⊓ Subgroup.centralizer (A : Set X) ≠ ⊥ :=
    CFSG.Walter.inf_centralizer_ne_bot_of_isPGroup Nat.prime_three
      (CFSG.Open.IsElemAbelian.isPGroup hAelem) hP3
      (hAI.trans hIP) hPne
  let H : Subgroup X := P ⊓ Subgroup.centralizer (A : Set X)
  haveI : Nontrivial H := (nontrivial_iff_ne_bot H).mpr hHne
  have hH3 : IsPGroup 3 H := hP3.to_le inf_le_left
  obtain ⟨k, hk, hHcard⟩ := hH3.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := H) 3
    (by rw [hHcard]; exact dvd_pow_self 3 (by omega))
  have hzordX : orderOf (z : X) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hzord
  have hzmem : (z : X) ∈ P ⊓ Subgroup.centralizer (A : Set X) := z.2
  have hzP : (z : X) ∈ P := hzmem.1
  have hzC : (z : X) ∈ Subgroup.centralizer (A : Set X) := hzmem.2
  have hzA : (z : X) ∉ A := by
    intro hzA
    have hzPI : (z : X) ∈ P ⊓ I := ⟨hzP, hAI hzA⟩
    have hz1 : (z : X) = 1 := by simpa [hPI] using hzPI
    rw [hz1, orderOf_one] at hzordX
    omega
  obtain ⟨hEelem, hEcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.isElemAbelian_sup_zpowers
      Nat.prime_three hAelem hAcard hzordX hzC hzA
  have hEcard4 : Nat.card (A ⊔ Subgroup.zpowers (z : X) : Subgroup X) = 3 ^ 4 := by
    simpa using hEcard
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank (p := 3) (k := 4) (by norm_num) le_top hEelem hEcard4
  omega

private theorem pRank_quotient_pPrimeCore_le_three {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrankM : CFSG.Open.pRank 3 M ≤ 3 :=
    h.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num)
      h.hypCGen.not_mem_sigmaA h.maxLocal.1
  have hO3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M))
  have htopM : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) = CFSG.Open.pRank 3 M := by
    have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
      M.subtype M.subtype_injective ⊤
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap.symm
  calc CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M))
      = CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) :=
        CFSG.SectionRank.pRank_quotient_eq (p := 3) (G := ↥M)
          (CFSG.pPrimeCore 3 ↥M) hO3
    _ = CFSG.Open.pRank 3 M := htopM
    _ ≤ 3 := hrankM

private theorem exists_component_alternating {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use)
    (h525 : FiveTwentyFiveS11Use) (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h73 : SevenThreeInput)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) :
    ∃ L : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M),
      CFSG.generalizedFitting (↥M ⧸ CFSG.pPrimeCore 3 ↥M) = L ∧
      Subgroup.centralizer (L : Set (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) = ⊥ ∧
      (Nonempty (↥L ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (↥L ≃* alternatingGroup (Fin 11))) := by
  classical
  haveI : IsSimpleGroup G := h.cstar.simple
  have hMtop : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let X := ↥M ⧸ O
  haveI : O.Normal := CFSG.pPrimeCore_normal
  have hKX : CFSG.Open.IsKGroup X := (h.cstar.kProper.isKGroup M hMtop).quotient O
  have hOquot : CFSG.pPrimeCore 3 X = ⊥ := by
    simpa [X, O] using
      (CFSG.pPrimeCore_quotient_eq_bot (p := 3) (G := ↥M) Nat.prime_three)
  have hrankX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 := by
    simpa [X, O] using pRank_quotient_pPrimeCore_le_three (G := G) h
  obtain ⟨I, hIperf, f, hfsurj, hfker⟩ := h.exists_perfect_map_onto_a9 h2 hK hU hL hKF
  have hO3X : CFSG.pCore 3 X = ⊥ :=
    pCore_three_eq_bot_of_a9 hrankX f hfsurj hfker
  obtain ⟨L, hLcomp, hFstar, hCent, -, hprankL⟩ :=
    exists_isComponent_of_a9 h711 hKX hOquot hO3X hrankX hIperf f hfsurj hfker
  obtain ⟨T, Hs, hTsyl, hTHs, hHsQuot, hHsNorm⟩ :=
    h.exists_sevenThreeData hA h2 hpre hK hU hL hKF h514 h525 hX
  refine ⟨L, hFstar, hCent, ?_⟩
  exact h73 X hKX L hLcomp hFstar hOquot hprankL T Hs hTsyl hTHs hHsQuot hHsNorm

theorem S14Choice.fourteenThirteen {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h73 : SevenThreeInput)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) :
    Nonempty (threeStar (CFSG.LocalAnalysis.RankThreeUC.AGL81C.oPPrimeHull 3 M) ≃*
        alternatingGroup (Fin 9)) ∨
      Nonempty (threeStar (CFSG.LocalAnalysis.RankThreeUC.AGL81C.oPPrimeHull 3 M) ≃*
        alternatingGroup (Fin 11)) := by
  classical
  obtain ⟨L, hFstar, hCent, hLiso⟩ :=
    exists_component_alternating h hA h2 hpre hK hU hL hKF h514 h525 hX h73 h711
  haveI hLnormal : L.Normal :=
    hFstar ▸ (CFSG.LocalCores.generalized_fitting_characteristic
      (G := ↥M ⧸ CFSG.pPrimeCore 3 ↥M)).2
  obtain ⟨eT⟩ := nonempty_threeStar_oPPrimeHull_mulEquiv M
  rcases hLiso with h9 | h11
  · obtain ⟨e9⟩ := h9
    left
    have hOtop : oPPrimeHull 3 (⊤ : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) = L :=
      oPPrimeHull_three_top_eq_of_alternating (L := L) hCent (by norm_num) (by norm_num) e9
    exact ⟨eT.trans ((MulEquiv.subgroupCongr hOtop).trans e9)⟩
  · obtain ⟨e11⟩ := h11
    right
    have hOtop : oPPrimeHull 3 (⊤ : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) = L :=
      oPPrimeHull_three_top_eq_of_alternating (L := L) hCent (by norm_num) (by norm_num) e11
    exact ⟨eT.trans ((MulEquiv.subgroupCongr hOtop).trans e11)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
