module

public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementInverted
public import CFSG.CharacterTheory.Semidihedral.PrimeOrderCyclicConfinementLift
public import CFSG.CharacterTheory.Semidihedral.StationaryLayerCover

public section

open scoped Pointwise commutatorElement

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.SignalizerFunctor.Helpers
open CFSG.Semidihedral.PrimeOrderCyclicConfinementLift (original_positive_power_prime_order)
open CFSG.Semidihedral.TwoCoverOddCore
  (two_commuting_involution_local_layer_covers_force_trivial_subgroup_odd_core)
open CFSG.Semidihedral.StationaryLayerCover
  (stationary_layer_cover_local_prime_is_centralized_or_inverted)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem inverted_prime_order_normalizer_le
    (hEsc : EscapingCentralizer.EscapingCentralizerStatement.{0})
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : allLocalPrimeStationaryCovers t s)
    {u : G} (huNa : u ∈ (N t).map (C t).subtype) (hu : (orderOf u).Prime)
    (hsu : s * u * s⁻¹ = u⁻¹) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ C t := by
  obtain ⟨hK4, htV, hsV, hV2, ht1, hs1, hVt, hVs, hts'⟩ := pair_facts t s ht hs hsC hts
  set V := Subgroup.closure ({t, s} : Set G) with hVdef
  set Na := (N t).map (C t).subtype with hNadef
  have hNaodd : Odd (Nat.card Na) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  set r := orderOf u with hrdef
  have hrN : r ∣ Nat.card (N t) := by
    have h := Subgroup.orderOf_dvd_natCard Na huNa
    rwa [Subgroup.card_map_of_injective (C t).subtype_injective] at h
  obtain ⟨P, hP⟩ := hcov r hu hrN
  obtain ⟨hVP, -, -⟩ := stationaryCovered_explicit t s P hP
  obtain ⟨Q, hQ⟩ := StationaryOddLocalization.ambient_sylow_from_intrinsic hu (C t) (N t) P
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have htu : t * u = u * t := (Subgroup.mem_centralizer_singleton_iff.mp (hNaC huNa)).symm
  have hVz : V ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact mem_normalizer_zpowers_of_commute htu
    · exact mem_normalizer_zpowers_of_conj (Or.inr hsu)
  have hVQ : V ≤ Subgroup.normalizer ((Q : Subgroup Na).map Na.subtype : Set G) := by
    rw [hQ]
    exact hVP
  have hVNa : V ≤ Subgroup.normalizer (Na : Set G) :=
    StationaryOddLocalization.actual_centralizer_core_normalized t V hVt
  have hzp : IsPGroup r (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one])
  obtain ⟨c, hc, hle⟩ := StationaryOddLocalization.invariant_pgroup_le_fixed_conjugate_sylow
    hu V Na (Subgroup.zpowers u) hV2 hVNa hNaodd Q hVQ (Subgroup.zpowers_le.mpr huNa) hzp hVz
  obtain ⟨u', hu'Q, hu'⟩ := hle (Subgroup.mem_zpowers u)
  change c * u' * c⁻¹ = u at hu'
  rw [hQ] at hu'Q
  have hcs : c⁻¹ * s = s * c⁻¹ := by
    have h : s * c = c * s := Subgroup.mem_centralizer_iff.mp hc.2 s hsV
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_assoc, mul_inv_cancel, mul_one]
  have hu'eq : u' = c⁻¹ * u * c⁻¹⁻¹ := by rw [← hu', inv_inv]; group
  have hu'ord : orderOf u' = r := by
    rw [hrdef, ← hu']
    exact ((MulAut.conj c).orderOf_eq u').symm
  have hsu' : s * u' * s⁻¹ = u'⁻¹ := by
    rw [hu'eq]
    exact (conj_inverted_iff hcs).mpr hsu
  have h := inverted_supplied_prime_order_normalizer_le hEsc hGnonab hrecognition n hn S0 f0
    t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hu hrN P hP hu'Q
    hu'ord hsu'
  rw [← hu']
  exact normalizer_zpowers_conj_le (hNaC hc.1) h

theorem fixed_supplied_prime_order_normalizer_le
    (hEsc : EscapingCentralizer.EscapingCentralizerStatement.{0})
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : allLocalPrimeStationaryCovers t s)
    {r : ℕ} (hr : r.Prime) (hrN : r ∣ Nat.card (N t)) (P : Sylow r (N t))
    (hP : stationaryCoveredLocalSylow t s P)
    {u : G} (huP : u ∈ ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype)
    (hur : orderOf u = r) (hsu : s * u * s⁻¹ = u) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ C t := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨hK4, htV, hsV, hV2, ht1, hs1, hVt, hVs, hts'⟩ := pair_facts t s ht hs hsC hts
  set V := Subgroup.closure ({t, s} : Set G) with hVdef
  let := hK4
  set Na := (N t).map (C t).subtype with hNadef
  have hNaodd : Odd (Nat.card Na) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have huNa : u ∈ Na := by
    obtain ⟨x, hx, rfl⟩ := huP
    obtain ⟨y, -, rfl⟩ := hx
    exact ⟨y, y.2, rfl⟩
  have huodd : Odd (orderOf u) := hNaodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Na huNa)
  have hrodd : Odd r := hur ▸ huodd
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hur
    exact hr.one_lt.ne hur
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have htu : t * u = u * t := (Subgroup.mem_centralizer_singleton_iff.mp (hNaC huNa)).symm
  have hus : u * s = s * u := by
    nth_rewrite 1 [← hsu]
    group
  set Hu := Subgroup.normalizer (Subgroup.zpowers u : Set G) with hHudef
  by_contra hHC
  have hVu : V ≤ Hu := by
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact mem_normalizer_zpowers_of_commute htu
    · exact mem_normalizer_zpowers_of_conj (Or.inl hsu)
  obtain ⟨hJN, hJimage, hJY, -⟩ := localCentralizingLayer_facts n hn S0 f0 hG t s ht hnonab
    hcentral hnc p f hp hpodd hf hq.le hmodel hcov
  have hJH : (localCentralizingLayer t).map (C t).subtype ≤ Hu := fun j hj =>
    mem_normalizer_zpowers_of_commute (layer_commute_odd_core t _ hJN hj huNa)
  have huR : u ∈ (CFSG.pPrimeCore 2 Hu).map Hu.subtype :=
    le_ambient_core_of_normal_odd Hu (Subgroup.zpowers u) (Subgroup.le_normalizer) le_rfl
      (by rw [Nat.card_zpowers]; exact huodd) (Subgroup.mem_zpowers u)
  have hR : CFSG.pPrimeCore 2 Hu ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.map_bot, Subgroup.mem_bot] at huR
    exact hu1 huR
  have hcover := cover_of_layer_le t Hu _ hJY hJimage hJH
  obtain ⟨hfact, -⟩ :=
    PerfectLayerNormalization.original_full_layer_cover_forces_core_centralizer_factorization
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC (Ne.symm hts) hnonab hcentral hnc
      p f hp hpodd hf hq.le hmodel Hu hVu hR hcover
  have hRC : ¬ (CFSG.pPrimeCore 2 Hu).map Hu.subtype ≤ C t := by
    intro hle
    apply hHC
    rw [← hfact]
    exact sup_le hle inf_le_right
  obtain ⟨ell, hell, hdiv, W, hVW, hescape⟩ :=
    exists_invariant_core_sylow_not_le Hu V (C t) hV2 hVu hRC
  obtain ⟨-, hab, hinv, -, -, d, -, -, -, -, -, -, -, hWtsne, -⟩ :=
    escaping_local_odd_sylow_has_original_exchanged_fixed_eigensubgroups hGnonab hrecognition
      n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq.le hmodel hcov
      Hu hVu hJH hR hell hdiv W hVW hescape
  set Wa := coveringOddSylowAmbient Hu W with hWadef
  have hWaR : Wa ≤ (CFSG.pPrimeCore 2 Hu).map Hu.subtype := by
    rw [hWadef, coveringOddSylowAmbient, ← Subgroup.map_map]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hRodd : Odd (Nat.card ((CFSG.pPrimeCore 2 Hu).map Hu.subtype)) := by
    rw [Subgroup.card_map_of_injective Hu.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hWodd : ∀ w ∈ Wa, Odd (orderOf w) := fun w hw =>
    hRodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ (hWaR hw))
  have hWaH : Wa ≤ Hu := hWaR.trans (Subgroup.map_subtype_le _)
  have hWu : ∀ w ∈ Wa, w * u = u * w := fun w hw =>
    commute_of_inverted_mem_normalizer (hWodd w hw) (hinv w hw) (hWaH hw) htu
  obtain ⟨g, -, -, -, hs2, htCs, hst, hsimple, hnonabs, hcentrals, hncs, -, -, -, -, hmodels,
      -, -, hcovs⟩ :=
    original_all_stationary_covers_produce_same_parameter_local_data hGnonab n hn S0 f0
      t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq.le hmodel hcov s (Or.inl rfl)
  let := hsimple
  obtain ⟨Us, hUs, -, -, -, -, -, -, hJsN, hYs, hJsimage, -, -, -, htriv⟩ :=
    hEsc G hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd
      hf hq hmodel hcov Hu hVu hJH hR ell hell hdiv W hVW hescape s (Or.inl rfl)
  set Ws := localFixedGroup Wa s with hWsdef
  have hF : Ws ⊓ Us = ⊥ := by
    by_contra hFne
    obtain ⟨⟨v0, hv0F⟩, hv01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hFne
    have hv01' : v0 ≠ 1 := fun h => hv01 (Subtype.ext h)
    obtain ⟨k, r', -, hr', -, hvF, hvord⟩ :=
      original_positive_power_prime_order hv0F hv01'
    obtain ⟨hvN, htv⟩ := (hUs _).mp hvF.2
    have hconf := inverted_prime_order_normalizer_le hEsc hGnonab hrecognition n hn S0 f0
      s t hs ht htCs hst hnonabs hcentrals hncs p f hp hpodd hf hq hmodels hcovs hvN
      (hvord ▸ hr') htv
    obtain ⟨⟨w, hwWts⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hWtsne
    have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hwv : w * v0 ^ k = v0 ^ k * w :=
      congrArg Subtype.val (hab.is_comm.comm ⟨w, hwWts.1⟩ ⟨v0 ^ k, hvF.1.1⟩)
    have hwCs : w ∈ C s := hconf (mem_normalizer_zpowers_of_commute hwv)
    have hsw : s * w * s⁻¹ = w := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp hwCs).symm, mul_inv_cancel_right]
    have hts2 : (t * s) * w * (t * s)⁻¹ = w := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hwWts.2
      rw [← h, mul_inv_cancel_right]
    have htinv : t⁻¹ = t := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, ← ht, pow_orderOf_eq_one]
    have hsw' : s * w * s⁻¹ = w⁻¹ := by
      have h1 : s = t⁻¹ * (t * s) := by group
      calc s * w * s⁻¹ = t⁻¹ * ((t * s) * w * (t * s)⁻¹) * t⁻¹⁻¹ := by rw [h1]; group
        _ = t * w * t⁻¹ := by rw [hts2, inv_inv, htinv]
        _ = w⁻¹ := hinv w hwWts.1
    exact hw1' (eq_one_of_conj_fixed_inverted (hWodd w hwWts.1) hsw hsw')
  obtain ⟨hellp, -, -, -, -, -, hPicard, -, -, -, hz2, -, ⟨e, -⟩, -⟩ := htriv hF
  have hrell : orderOf u ≠ ell :=
    orderOf_ne_of_normal_inverted_core_sylow Hu le_rfl huR hell W hinv htu huodd hu1
  have hrp : r ≠ p := by
    rw [← hur, ← hellp]
    exact hrell
  have huCs : u ∈ C s := Subgroup.mem_centralizer_singleton_iff.mpr hus
  set uC : C s := ⟨u, huCs⟩ with huCdef
  set Pi := (Ws.subgroupOf (C s)).map (nu s) with hPidef
  have hcentPi : nu s uC ∈ Subgroup.centralizer (Pi : Set (H s)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hWu w hw.1
  have hcard : Nat.card (Subgroup.centralizer (Pi : Set (H s))) = p ^ f * 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hPicard, Nat.card_zpowers, hz2]
  have hord : orderOf (nu s uC) ∣ r := by
    have h1 := orderOf_map_dvd (nu s) uC
    have h2 : orderOf uC = r := by
      rw [← hur, ← Subgroup.orderOf_coe]
    exact h2 ▸ h1
  have hnu1 : nu s uC = 1 :=
    eq_one_of_orderOf_dvd_odd_prime _ hcentPi hr hrodd hp hrp hcard hord
  have huNs : uC ∈ N s := (QuotientGroup.eq_one_iff uC).mp hnu1
  have hJsH : (localCentralizingLayer s).map (C s).subtype ≤ Hu := fun j hj =>
    mem_normalizer_zpowers_of_commute (layer_commute_odd_core s _ hJsN hj ⟨uC, huNs, rfl⟩)
  have hJsY : localCentralizingLayer s ≤ localLayerPreimage s := by
    rw [hYs]
    exact le_sup_left
  have hJsimage' : (localCentralizingLayer s).map (nu s) =
      (CFSG.generalizedFitting (Gamma s)).comap (barKappa s) := by
    rw [hJsimage]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hcovers := cover_of_layer_le s Hu _ hJsY hJsimage' hJsH
  exact hR (two_commuting_involution_local_layer_covers_force_trivial_subgroup_odd_core
    G hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf
    hq.le hmodel hnonabs hcentrals hncs p f hp hpodd hf hq.le hmodels Hu hVu hcover hcovers)

theorem prime_order_normalizer_le
    (hEsc : EscapingCentralizer.EscapingCentralizerStatement.{0})
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : allLocalPrimeStationaryCovers t s)
    {u : G} (huNa : u ∈ (N t).map (C t).subtype) (hu : (orderOf u).Prime) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ C t := by
  set Na := (N t).map (C t).subtype with hNadef
  have hNaodd : Odd (Nat.card Na) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  set r := orderOf u with hrdef
  have hrN : r ∣ Nat.card (N t) := by
    have h := Subgroup.orderOf_dvd_natCard Na huNa
    rwa [Subgroup.card_map_of_injective (C t).subtype_injective] at h
  obtain ⟨P, hP⟩ := hcov r hu hrN
  obtain ⟨hVP, hstat, hcovP⟩ := stationaryCovered_explicit t s P hP
  have hscalar :=
    ((stationary_layer_cover_local_prime_is_centralized_or_inverted
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf
      hq.le hmodel hu P hrN hVP hstat).1.mp hcovP)
  obtain ⟨Q, hQ⟩ := StationaryOddLocalization.ambient_sylow_from_intrinsic hu (C t) (N t) P
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have hzp : IsPGroup r (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one])
  obtain ⟨c, hc, hle⟩ := StationaryOddLocalization.invariant_pgroup_le_fixed_conjugate_sylow
    hu ⊥ Na (Subgroup.zpowers u) IsPGroup.of_bot bot_le hNaodd Q bot_le
    (Subgroup.zpowers_le.mpr huNa) hzp bot_le
  obtain ⟨u', hu'Q, hu'⟩ := hle (Subgroup.mem_zpowers u)
  change c * u' * c⁻¹ = u at hu'
  rw [hQ] at hu'Q
  have hu'ord : orderOf u' = r := by
    rw [hrdef, ← hu']
    exact ((MulAut.conj c).orderOf_eq u').symm
  rw [← hu']
  apply normalizer_zpowers_conj_le (hNaC hc.1)
  rcases hscalar with hcen | hinv
  · exact fixed_supplied_prime_order_normalizer_le hEsc hGnonab hrecognition n hn S0 f0
      t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hu hrN P hP hu'Q
      hu'ord (hcen u' hu'Q)
  · exact inverted_supplied_prime_order_normalizer_le hEsc hGnonab hrecognition n hn S0 f0
      t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hu hrN P hP hu'Q
      hu'ord (hinv u' hu'Q)

end CFSG.Semidihedral.StationaryConfinement
