module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedTransport
public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316L33

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup FooteLit UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem oddCore_sup_twoLayerIn_centralizer_le_of_marked
    {T : Type} [Group T] [IsSimpleGroup T]
    {family : Set (Subgroup G)} (hfamily : IsomorphicFamily family T)
    {M K : Subgroup G} (hKM : IsTwoComponentIn K M) (hKmarked : Marked family T K)
    (hCK : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M)
    {t : G} {k : ℕ} (htk : t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (htK : t ∈ coreActionKernel K) (hKrank : 2 ≤ CFSG.Open.pRank 2 K) :
    oddCoreIn (centralizer ({t} : Set G)) ⊔ twoLayerIn (centralizer ({t} : Set G)) ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := zpowers t with hU
  have hU2 : IsPGroup 2 U := Sol76.isPGroup_zpowers_of_pow htk
  have hUne : U ≠ ⊥ := fun h => ht1 (zpowers_eq_bot.mp h)
  have hUK : U ≤ coreActionKernel K := zpowers_le.mpr htK
  obtain ⟨H, hHcomp, -, hHclosure, hHcover⟩ :=
    markedST_of_isomorphicFamily hfamily K hKmarked U hU2 hUK hUne
  let C : Subgroup G := centralizer (U : Set G)
  let Y : Subgroup G := fixedShadow K U
  let E : Subgroup G := twoLayerIn C
  have hCU : C = centralizer ({t} : Set G) := by
    dsimp only [C, U]
    exact UnbalancedLayer.centralizer_zpowers_eq t
  have hH2 : IsTwoComponentIn H C := hHcomp
  have hYC : Y ≤ C := (fixedShadow_le_inf K U).trans inf_le_right
  have hYH : Y ≤ H := by
    rw [← hHclosure]
    exact FooteLit.le_conjClosure Y E
  have hYL : Y ≤ E := hYH.trans (le_twoLayerIn_of_isTwoComponentIn hH2)
  have hYK : Y ≤ K := fixedShadow_le K U
  have hYM : Y ≤ M := hYK.trans hKM.1
  have hCY : ∀ b ∈ Y, orderOf b = 2 → centralizer ({b} : Set G) ≤ M := fun b hb hb2 =>
    hCK b (hYK hb) hb2
  have hKq : IsQuasisimple (K ⧸ pPrimeCore 2 K) := hKmarked.quotient_quasisimple hfamily
  obtain ⟨hYcover, -, -⟩ := fixedShadow_cover_quotient hKq hU2 hUK
  have hYr : 2 ≤ CFSG.Open.pRank 2 Y :=
    hKrank.trans (Sol76T13.pRank_le_of_sup_oddCoreIn hYK hYcover)
  have hOHC : oddCoreIn H ≤ oddCoreIn C := oddCoreIn_le_of_isTwoComponentIn hH2
  have hclosure : conjClosure Y E ≤ oddCoreIn C ⊔ Y := by
    rw [hHclosure]
    calc H = Y ⊔ oddCoreIn H := hHcover.symm
      _ ≤ Y ⊔ oddCoreIn C := sup_le_sup_left hOHC Y
      _ = oddCoreIn C ⊔ Y := sup_comm Y (oddCoreIn C)
  have hmain := Sol76T13.oddCore_sup_twoLayerIn_le_of_shadow hYC hYL hYM hYr hCY hclosure
  rwa [hCU] at hmain

theorem oddCore_sup_twoLayerIn_centralizer_le_of_marked_topRank
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    {family : Set (Subgroup G)} (hfamily : IsomorphicFamily family T)
    {M K : Subgroup G} (hKM : IsTwoComponentIn K M) (hKmarked : Marked family T K)
    (hCK : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M)
    {t : G} {k : ℕ} (htk : t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (htK : t ∈ coreActionKernel K) (hTrank : 2 ≤ CFSG.pRank 2 T) :
    oddCoreIn (centralizer ({t} : Set G)) ⊔ twoLayerIn (centralizer ({t} : Set G)) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eK⟩ := hKmarked.2.1
  have hKrank : 2 ≤ CFSG.Open.pRank 2 K := by
    have hker : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (pPrimeCore_coprime_card (p := 2) (G := ↥K))
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      ← CFSG.SectionRank.pRank_quotient_eq (p := 2) (N := pPrimeCore 2 ↥K) hker,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num) eK,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 T]
    exact hTrank
  exact oddCore_sup_twoLayerIn_centralizer_le_of_marked hfamily hKM hKmarked hCK htk ht1 htK
    hKrank

end CFSG.ComponentClassification.FooteMarked
