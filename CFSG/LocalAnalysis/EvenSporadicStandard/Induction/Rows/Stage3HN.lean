module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNFixes
public import CFSG.Sporadic.GLQ.HNTwoRank
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.Mult.PPart
public import CFSG.Sporadic.NativeFinite

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.TwoHS
  CFSG.RankThree.PartOne.Mult

section Proved

theorem hnPair_eq : HNPair = PairShape (· = 88704000) := rfl

theorem hnPinnedFacts : PinnedFacts .HN (· = 88704000) 44352000 273030912000000 where
  finite := CFSG.Sporadic.finite_carrier_of_ne_M .HN (by decide)
  simple := hn_isSimpleGroup_of_isSporadic (X := Carrier .HN) ⟨MulEquiv.refl _⟩
  nonabelian := hn_exists_not_commute (X := Carrier .HN) ⟨MulEquiv.refl _⟩
  card := by
    have h := hn_card_eq (G := Carrier .HN) (L := ⊤) ⟨Subgroup.topEquiv⟩
    rwa [Subgroup.card_top] at h
  even_card := ⟨136515456000000, by norm_num⟩
  rank := fun X _ _ h => by
    have := (CFSG.Sporadic.GLQ.hn_two_rank_at_least_five.2.2.2.2.2 X h).2
    omega
  outTwo := hn_outTwo_of_isSporadic (Y := Carrier .HN) ⟨MulEquiv.refl _⟩
  pair := fun u K hQ => by
    have : Finite (Carrier .HN) := CFSG.Sporadic.finite_carrier_of_ne_M .HN (by decide)
    obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
    obtain ⟨hcov, -⟩ := hn_pair_cover (G := Carrier .HN) (L := ⊤) ⟨Subgroup.topEquiv⟩ huL hu2
      hKL hKu hcard
    have hKC : K ≤ ⊤ ⊓ centralizer ({u} : Set (Carrier .HN)) := fun k hk =>
      ⟨mem_top _, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
    refine ⟨?_, hcard.trans (by norm_num)⟩
    rw [← card_center_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKC)]
    exact hcov.card_center
  two_le := by norm_num
  even_N := ⟨22176000, by norm_num⟩
  lt := by norm_num
  cube := ⟨445, by norm_num, by norm_num⟩
  ne_a7 := by norm_num

theorem hn_exists_pair :
    ∃ (u : Carrier .HN) (K : Subgroup (Carrier .HN)),
      PairShape (· = 88704000) (Carrier .HN) ⊤ K u := by
  obtain ⟨z, hz2, E, hE, -, -⟩ := hnCentralizerFacts
  refine ⟨z, E.map (centralizer ({z} : Set (Carrier .HN))).subtype, mem_top _, hz2, le_top,
    ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 k.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact card_eq_of_double_cover hE.card_center hE.quotient

theorem hn_fit (G : Type) [Group G] [Finite G] (L K : Subgroup G) (_ : IsSporadic ↥L .HN)
    (_ : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K) (hO : CFSG.oddCore ↥K ≤ center ↥K)
    (hK : IsKPinned .HN (· = 88704000) (↥K ⧸ CFSG.oddCore ↥K)) :
    Nat.card ↥K = 88704000 := by
  obtain ⟨u', K', hQ', ⟨f⟩⟩ := hK
  have : Finite (Carrier .HN) := CFSG.Sporadic.finite_carrier_of_ne_M .HN (by decide)
  have : Group.IsPerfect ↥K := hKq.1
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ'
  obtain ⟨hcov, -⟩ := hn_pair_cover (G := Carrier .HN) (L := ⊤) ⟨Subgroup.topEquiv⟩ huL hu2
    hKL hKu hcard
  have hKC : K' ≤ ⊤ ⊓ centralizer ({u'} : Set (Carrier .HN)) := fun k hk =>
    ⟨mem_top _, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  obtain ⟨e₀⟩ := hcov.quotient
  set C : Subgroup (Carrier .HN) := ⊤ ⊓ centralizer ({u'} : Set (Carrier .HN)) with hC
  have e1 : ↥K ⧸ center ↥K ≃* (↥K ⧸ CFSG.oddCore ↥K) ⧸ center (↥K ⧸ CFSG.oddCore ↥K) :=
    (quotientCenterOddCoreEquiv hO).symm
  have e2 : (↥K ⧸ CFSG.oddCore ↥K) ⧸ center (↥K ⧸ CFSG.oddCore ↥K) ≃* ↥K' ⧸ center ↥K' :=
    quotientCenterEquiv' f
  have e3 : ↥K' ⧸ center ↥K' ≃* ↥(K'.subgroupOf C) ⧸ center ↥(K'.subgroupOf C) :=
    (quotientCenterEquiv' (Subgroup.subgroupOfEquivOfLe hKC)).symm
  have e4 : ↥(K'.subgroupOf C) ⧸ center ↥(K'.subgroupOf C) ≃* NativeSporadic.HS := e₀
  have eK : ↥K ⧸ center ↥K ≃* NativeSporadic.HS := e1.trans (e2.trans (e3.trans e4))
  have hZ : Nat.card (center ↥K) ≤ 2 :=
    CFSG.Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate hKq.1 eK
  have h1 : Nat.card (CFSG.oddCore ↥K) ≤ 2 := (Subgroup.card_le_of_le hO).trans hZ
  have h2 : Odd (Nat.card (CFSG.oddCore ↥K)) :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  have h3 : Nat.card (CFSG.oddCore ↥K) = 1 := by
    obtain ⟨j, hj⟩ := h2
    omega
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K)
  rw [h3, mul_one, Nat.card_congr f.toEquiv] at h4
  exact h4.trans hcard

noncomputable def stage3Row_hn (hmult : OddMultTrivial .HN) :
    Stage3Row [.HN] (fun _ => HNPair) :=
  stage3Row_of_pinned hnPair_eq hnPinnedFacts hmult
    (lemma36DataQ_hn hmult (hnFixesElem_of_mult hmult)) (by norm_num) hn_exists_pair
    (fun G _ _ L K hL hKL hKq hO hK => hn_fit G L K hL hKL hKq hO hK)

end Proved

end CFSG.EvenSporadicStandard.Induction
