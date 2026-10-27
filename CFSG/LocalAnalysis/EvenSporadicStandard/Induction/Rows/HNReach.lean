module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3HN
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ReachGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNHostHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Reach
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm24Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.TwoHS
  CFSG.EvenSporadicStandard.Induction.Hyp

section HNReach

abbrev IsKHN : GroupClass := IsKPinned .HN (· = 88704000)

theorem hn_pinned_card (Y : Type) [Group Y] (h : IsSporadic Y .HN) :
    Nat.card Y = 273030912000000 := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.HN := e
  rw [Nat.card_congr e'.toEquiv]
  exact CFSG.Sporadic.HN.card_HN

theorem hs_pinned_card (Y : Type) [Group Y] (h : IsSporadic Y .HS) :
    Nat.card Y = 44352000 := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.HS := e
  rw [Nat.card_congr e'.toEquiv]
  exact CFSG.Sporadic.HS.card_HS

theorem hs_pinned_simple (Y : Type) [Group Y] (h : IsSporadic Y .HS) : IsSimpleGroup Y := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.HS := e
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e'

theorem hs_cover_card_center_le_two {K₂ : Type} [Group K₂] (hperf : Group.IsPerfect K₂)
    (hS : IsSporadic (K₂ ⧸ center K₂) .HS) : Nat.card (center K₂) ≤ 2 := by
  obtain ⟨e⟩ := hS
  have e' : K₂ ⧸ center K₂ ≃* CFSG.Blueprint.NativeSporadic.HS := e
  exact CFSG.Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate hperf e'

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup

theorem hn_pair_data {u : Carrier .HN} {K : Subgroup (Carrier .HN)}
    (h : PairShape (· = 88704000) (Carrier .HN) ⊤ K u) :
    CFSG.IsQuasisimple ↥K ∧ Nat.card (center ↥K) = 2 ∧ IsSporadic (↥K ⧸ center ↥K) .HS := by
  have : Finite (Carrier .HN) := CFSG.Sporadic.finite_carrier_of_ne_M .HN (by decide)
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := h
  obtain ⟨hcov, -⟩ := hn_pair_cover (G := Carrier .HN) (L := ⊤) ⟨Subgroup.topEquiv⟩ huL hu2
    hKL hKu hcard
  have hKC : K ≤ ⊤ ⊓ centralizer ({u} : Set (Carrier .HN)) := fun k hk =>
    ⟨mem_top _, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  let φ := Subgroup.subgroupOfEquivOfLe hKC
  have hq := (isComponent_of_isHSCover hcov).1
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hq, ?_, ?_⟩
  · rw [← card_center_of_mulEquiv' φ]
    exact hcov.card_center
  · obtain ⟨e⟩ := hcov.quotient
    exact ⟨(quotientCenterEquiv' φ).symm.trans e⟩

theorem isKHN_data {X : Type} [Group X] (h : IsKHN X) :
    CFSG.IsQuasisimple X ∧ Nat.card (center X) = 2 ∧ IsSporadic (X ⧸ center X) .HS ∧
      Nat.card X = 88704000 := by
  obtain ⟨u, K, hQ, ⟨f⟩⟩ := h
  obtain ⟨hq, hz, ⟨e⟩⟩ := hn_pair_data hQ
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv f.symm hq, ?_,
    ⟨(quotientCenterEquiv' f).trans e⟩, ?_⟩
  · rw [card_center_of_mulEquiv' f]
    exact hz
  · rw [Nat.card_congr f.toEquiv]
    exact hQ.2.2.2.2

theorem isKHN_of_doubleCover {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hZ : Nat.card (center X) = 2) (hX : IsSporadic (X ⧸ center X) .HS) : IsKHN X := by
  obtain ⟨u, K, hQ⟩ := hn_exists_pair
  obtain ⟨hKq, hKZ, hKS⟩ := hn_pair_data hQ
  have : Finite (Carrier .HN) := CFSG.Sporadic.finite_carrier_of_ne_M .HN (by decide)
  have : Finite ↥K := inferInstance
  have hXp : Group.IsPerfect X := hq.1
  have hKp : Group.IsPerfect ↥K := hKq.1
  obtain ⟨f⟩ := nonempty_mulEquiv_of_doubleCover_hs hXp hKp hZ hKZ hX hKS
  exact ⟨u, K, hQ, ⟨f⟩⟩

theorem isKHN_iso {X Y : Type} [Group X] [Group Y] (hX : IsKHN X) (hY : IsKHN Y) :
    Nonempty (X ≃* Y) := by
  obtain ⟨hXq, hXz, hXs, hXc⟩ := isKHN_data hX
  obtain ⟨hYq, hYz, hYs, hYc⟩ := isKHN_data hY
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hXc]; norm_num)
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hYc]; norm_num)
  exact nonempty_mulEquiv_of_doubleCover_hs hXq.1 hYq.1 hXz hYz hXs hYs

theorem isKHN_oddCore {X : Type} [Group X] (h : IsKHN X) : CFSG.oddCore X = ⊥ := by
  obtain ⟨hq, hz, hs, hc⟩ := isKHN_data h
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have : IsSimpleGroup (X ⧸ center X) := hs_pinned_simple _ hs
  refine oddCore_eq_bot_of_card_center_two ?_ hz
  rw [hs_pinned_card _ hs]
  exact ⟨22176000, by norm_num⟩

theorem hn_kEven : KEven IsKHN := fun X _ hX => by
  obtain ⟨-, hz, -, -⟩ := isKHN_data hX
  rw [hz]
  exact even_two

theorem hn_false_of_isAlt {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2) (hAlt : Balance.IsAltType ↥N') {v : Y}
    (hv : orderOf v = 2) {M : Subgroup Y} (hMC : IsCompIn M (centralizer ({v} : Set Y)))
    (hM : OddCover .HS M) : False :=
  Balance.false_of_isAlt hN hidx hAlt (s := .HS) (c := 44352000)
    (hs_pinned_card _ ⟨MulEquiv.refl _⟩) (by norm_num)
    (fun m _ => factorial_div_two_ne_of_between (n₀ := 11) (N := 44352000)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) m) hv hMC hM

theorem hn_false_of_catalog (hC : Balance.CatalogNoHSOdd) {Y : Type} [Group Y] [Finite Y]
    {N' : Subgroup Y} (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hcat : CFSG.Blueprint.Catalog ↥N') {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P) (hodd : Odd (Nat.card ↥(center ↥P)))
    (hPS : IsSporadic (↥P ⧸ center ↥P) .HS) : False := by
  obtain ⟨v, hv2, hcomp⟩ := hP.2
  have hcov : OddCover .HS P := ⟨hPq, hodd, hPS⟩
  by_cases halt : Balance.IsAltType ↥N'
  · exact hn_false_of_isAlt hN hidx halt hv2 hcomp hcov
  · exact hC Y N' hN hidx hcat halt P v hv2 hcomp hcov

theorem hn_closure (hC : Balance.CatalogNoHSOdd) {Y : Type} [Group Y]
    [Finite Y] (hT : TwoHSHostAt Y) {N' : Subgroup Y} (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P) (hPS : IsSporadic (↥P ⧸ center ↥P) .HS)
    (hscope : ClosureScope IsKHN N' P) : IsSporadic ↥N' .HS ∨ IsSporadic ↥N' .HN := by
  have hle2 := hs_cover_card_center_le_two hPq.1 hPS
  have hpos : 0 < Nat.card ↥(center ↥P) := Nat.card_pos
  rcases (by omega : Nat.card ↥(center ↥P) = 1 ∨ Nat.card ↥(center ↥P) = 2) with h1 | h2
  · exfalso
    have hodd : Odd (Nat.card ↥(center ↥P)) := by rw [h1]; exact odd_one
    rcases hscope with hcat | hK | hnK
    · exact hn_false_of_catalog hC hN hidx hcat hP hPq hodd hPS
    · exact (Nat.not_even_iff_odd.2 hodd) (even_center_of_klike hPq hK hn_kEven)
    · obtain ⟨u, K, hQ⟩ := hn_exists_pair
      have hXK : IsKHN ↥K := ⟨u, K, hQ, ⟨MulEquiv.refl _⟩⟩
      obtain ⟨-, -, ⟨f⟩, -⟩ := isKHN_data hXK
      obtain ⟨g⟩ := hPS
      exact hnK ↥K hXK ⟨g.trans f.symm⟩
  · exact Or.inr (hT N' hN hidx hkp P hP hPq h2 hPS)

theorem hn_pair_into (hC : Balance.CatalogNoHSOdd) {Y : Type} [Group Y] [Finite Y]
    {N' : Subgroup Y} (hN : FStarSimple N') (hidx : N'.index ≤ 2) {P : Subgroup Y}
    (hP : SolStd P) (hPq : CFSG.IsQuasisimple ↥P) (hPS : IsSporadic (↥P ⧸ center ↥P) .HS)
    (hN' : IsSporadic ↥N' .HN) : IsKHN (↥P ⧸ CFSG.oddCore ↥P) := by
  have hle2 := hs_cover_card_center_le_two hPq.1 hPS
  have hpos : 0 < Nat.card ↥(center ↥P) := Nat.card_pos
  rcases (by omega : Nat.card ↥(center ↥P) = 1 ∨ Nat.card ↥(center ↥P) = 2) with h1 | h2
  · exfalso
    exact hn_false_of_catalog hC hN hidx (Or.inr (Or.inr (Or.inr (Or.inr ⟨.HN, hN'⟩)))) hP hPq
      (by rw [h1]; exact odd_one) hPS
  · have hK : IsKHN ↥P := isKHN_of_doubleCover hPq h2 hPS
    exact isKPinned_isoInv .HN _ ↥P (↥P ⧸ CFSG.oddCore ↥P)
      (quotientOddCoreEquiv (isKHN_oddCore hK)).symm hK

theorem hn_notR {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} (hN : FStarSimple N)
    (hidx : N.index ≤ 2) {L : Subgroup Y} (hL : InL L) (hcov : OddCover .HN L)
    (hR : IsSporadic ↥N .HS ∨ IsSporadic ↥N .HN) : False := by
  have : N.Normal := hN.normal
  have hLN : L ≤ N := le_of_perfect_of_index_le_two hidx hcov.1.1
  have hne : L ≠ N := inL_ne_of_fStarSimple hN hL
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
  have h2 := hn_pinned_card _ hcov.2.2
  have h3 : 0 < Nat.card ↥(center ↥L) := hcov.2.1.pos
  have h4 : Nat.card ↥L ≤ Nat.card ↥N := Subgroup.card_le_of_le hLN
  rcases hR with hHS | hHN
  · have := hs_pinned_card _ hHS
    rw [h2] at h1
    have : 273030912000000 ≤ Nat.card ↥L := by rw [h1]; exact Nat.le_mul_of_pos_right _ h3
    omega
  · have h5 := hn_pinned_card _ hHN
    rw [h2] at h1
    have : 273030912000000 ≤ Nat.card ↥L := by rw [h1]; exact Nat.le_mul_of_pos_right _ h3
    exact hne (Subgroup.eq_of_le_of_card_ge hLN (by omega))

theorem hn_fi23 : Fi23Excl .HN :=
  fi23Excl_of_card (n := 273030912000000) hn_pinned_card (by norm_num)

theorem hn_sp_not_exc : SporadicNotExc .HN :=
  sporadicNotExc_of_card (N := 273030912000000) (c := 81736) hn_pinned_card (by norm_num)
    (by norm_num) (by norm_num)

theorem hs_sp_not_exc : SporadicNotExc .HS :=
  sporadicNotExc_of_card (N := 44352000) (c := 445) hs_pinned_card (by norm_num)
    (by norm_num) (by norm_num)

end HNReach

end CFSG.EvenSporadicStandard.Induction
