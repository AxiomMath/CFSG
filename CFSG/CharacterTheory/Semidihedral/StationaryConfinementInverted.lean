module

public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementSupport
public import CFSG.CharacterTheory.Semidihedral.EscapingCentralizerStatement

public section

open scoped Pointwise commutatorElement

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.SignalizerFunctor.Helpers
open CFSG.Semidihedral.StationaryOddLocalization
  (stationary_centralizer_cover_prime_forces_local_invariant_subgroup_centralization)

section Setting

variable {G : Type*} [Group G]

theorem stationaryCovered_explicit (t s : G) {ell : ℕ} (P : Sylow ell (N t))
    (hP : stationaryCoveredLocalSylow t s P) :
    Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G) ∧
    (∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) ∧
    ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  obtain ⟨hV, ⟨P0, hP0⟩, hcover⟩ := hP
  exact ⟨hV, ⟨P0, by rw [Subgroup.map_map]; exact hP0⟩, hcover⟩

theorem cover_of_layer_le (t : G) (H : Subgroup G) (J : Subgroup (C t))
    (hJY : J ≤ localLayerPreimage t)
    (hJimage : J.map (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hJH : J.map (C t).subtype ≤ H) :
    (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
  · have hle : J ≤ H.subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) :=
      fun x hx => ⟨hJH (Subgroup.mem_map_of_mem _ hx), hJY hx⟩
    exact hJimage.symm.le.trans (Subgroup.map_mono hle)

theorem layer_commute_odd_core (t : G) (J : Subgroup (C t)) (hJN : ⁅J, N t⁆ = ⊥)
    {j x : G} (hj : j ∈ J.map (C t).subtype) (hx : x ∈ (N t).map (C t).subtype) :
    j * x = x * j := by
  obtain ⟨j', hj', rfl⟩ := hj
  obtain ⟨x', hx', rfl⟩ := hx
  have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN hj'
  have h' := Subgroup.mem_centralizer_iff.mp h x' hx'
  exact congrArg Subtype.val h'.symm

theorem le_ambient_core_of_normal_odd [Finite G] (H U : Subgroup G) (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hUodd : Odd (Nat.card U)) :
    U ≤ (CFSG.pPrimeCore 2 H).map H.subtype := by
  have hUknormal : (U.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hHU
  have hUkodd : Odd (Nat.card (U.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]
    exact hUodd
  have hUcore : U.subgroupOf H ≤ CFSG.pPrimeCore 2 H :=
    le_sSup ⟨hUknormal, Nat.coprime_two_left.mpr hUkodd⟩
  have h := Subgroup.map_mono (f := H.subtype) hUcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hUH] at h

theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem conj_inverted_iff {t v x : G} (hvt : v * t = t * v) :
    t * (v * x * v⁻¹) * t⁻¹ = (v * x * v⁻¹)⁻¹ ↔ t * x * t⁻¹ = x⁻¹ := by
  have h : t * (v * x * v⁻¹) * t⁻¹ = v * (t * x * t⁻¹) * v⁻¹ := by
    calc t * (v * x * v⁻¹) * t⁻¹ = (t * v) * x * (t * v)⁻¹ := by group
      _ = (v * t) * x * (v * t)⁻¹ := by rw [hvt]
      _ = v * (t * x * t⁻¹) * v⁻¹ := by group
  rw [h, show (v * x * v⁻¹)⁻¹ = v * x⁻¹ * v⁻¹ by group]
  constructor
  · intro h'
    exact mul_left_cancel (mul_right_cancel h')
  · intro h'
    rw [h']

theorem mem_normalizer_inverted [Finite G] {Na U : Subgroup G} {t v : G}
    (hU : ∀ x : G, x ∈ U ↔ x ∈ Na ∧ t * x * t⁻¹ = x⁻¹)
    (hvN : v ∈ Subgroup.normalizer (Na : Set G)) (hvt : v * t = t * v) :
    v ∈ Subgroup.normalizer (U : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  rw [SetLike.mem_coe, hU] at hx ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.mp hvN x).mp hx.1, (conj_inverted_iff hvt).mpr hx.2⟩

theorem normalizer_zpowers_conj_le {K : Subgroup G} {c u : G} (hc : c ∈ K)
    (h : Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ K) :
    Subgroup.normalizer (Subgroup.zpowers (c * u * c⁻¹) : Set G) ≤ K := by
  apply normalizer_zpowers_le_of_conj (K.inv_mem hc)
  rw [show c⁻¹ * (c * u * c⁻¹) * c⁻¹⁻¹ = u by group]
  exact h

end Setting

section Actual

variable {G : Type} [Group G] [Finite G]

theorem localCentralizingLayer_facts (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : allLocalPrimeStationaryCovers t s) :
    ⁅localCentralizingLayer t, N t⁆ = ⊥ ∧
      (localCentralizingLayer t).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ∧
      localCentralizingLayer t ≤ localLayerPreimage t ∧ (localCentralizingLayer t).Normal := by
  obtain ⟨-, hJnormal, -, hJimage, hJN, -⟩ :=
    (Local.all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel).1
      (all_stationary_covers_give_original_layer_coverage t s hcov)
  exact ⟨hJN, hJimage, (Subgroup.map_subtype_le _).trans inf_le_left, hJnormal⟩

omit [Finite G] in
theorem pair_facts (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t)
    (hts : t ≠ s) :
    IsKleinFour (Subgroup.closure ({t, s} : Set G)) ∧
      t ∈ Subgroup.closure ({t, s} : Set G) ∧ s ∈ Subgroup.closure ({t, s} : Set G) ∧
      IsPGroup 2 (Subgroup.closure ({t, s} : Set G)) ∧ t ≠ 1 ∧ s ≠ 1 ∧
      Subgroup.closure ({t, s} : Set G) ≤ C t ∧ Subgroup.closure ({t, s} : Set G) ≤ C s ∧
      t * s = s * t := by
  have hcomm : Commute t s := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have hK := TwoCoverOddCore.original_four_group_isKleinFour t s ht hs hcomm hts
  have htV : t ∈ Subgroup.closure ({t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hsV : s ∈ Subgroup.closure ({t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hV2 : IsPGroup 2 (Subgroup.closure ({t, s} : Set G)) :=
    IsPGroup.of_card (n := 2) (by rw [@IsKleinFour.card_four _ _ hK]; norm_num)
  have ht1 : t ≠ 1 := by rintro rfl; simp at ht
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hVt : Subgroup.closure ({t, s} : Set G) ≤ C t := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact hsC
  have hVs : Subgroup.closure ({t, s} : Set G) ≤ C s := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  exact ⟨hK, htV, hsV, hV2, ht1, hs1, hVt, hVs, hcomm.eq⟩

variable [IsSimpleGroup G]

theorem inverted_supplied_prime_order_normalizer_le
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
    (hur : orderOf u = r) (hsu : s * u * s⁻¹ = u⁻¹) :
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
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hur
    exact hr.one_lt.ne hur
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have htu : t * u = u * t := (Subgroup.mem_centralizer_singleton_iff.mp (hNaC huNa)).symm
  set H := Subgroup.normalizer (Subgroup.zpowers u : Set G) with hHdef
  by_contra hHC
  have hVu : V ≤ H := by
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact mem_normalizer_zpowers_of_commute htu
    · exact mem_normalizer_zpowers_of_conj (Or.inr hsu)
  obtain ⟨hJN, hJimage, hJY, -⟩ := localCentralizingLayer_facts n hn S0 f0 hG t s ht hnonab
    hcentral hnc p f hp hpodd hf hq.le hmodel hcov
  have hJH : (localCentralizingLayer t).map (C t).subtype ≤ H := fun j hj =>
    mem_normalizer_zpowers_of_commute (layer_commute_odd_core t _ hJN hj huNa)
  have huR : u ∈ (CFSG.pPrimeCore 2 H).map H.subtype :=
    le_ambient_core_of_normal_odd H (Subgroup.zpowers u) (Subgroup.le_normalizer) le_rfl
      (by rw [Nat.card_zpowers]; exact huodd) (Subgroup.mem_zpowers u)
  have hR : CFSG.pPrimeCore 2 H ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.map_bot, Subgroup.mem_bot] at huR
    exact hu1 huR
  have hcover := cover_of_layer_le t H _ hJY hJimage hJH
  obtain ⟨hfact, -⟩ :=
    PerfectLayerNormalization.original_full_layer_cover_forces_core_centralizer_factorization
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC (Ne.symm hts) hnonab hcentral hnc
      p f hp hpodd hf hq.le hmodel H hVu hR hcover
  have hRC : ¬ (CFSG.pPrimeCore 2 H).map H.subtype ≤ C t := by
    intro hle
    apply hHC
    rw [← hfact]
    exact sup_le hle inf_le_right
  obtain ⟨ell, hell, hdiv, W, hVW, hescape⟩ :=
    exists_invariant_core_sylow_not_le H V (C t) hV2 hVu hRC
  obtain ⟨-, -, hinv, -⟩ :=
    escaping_local_odd_sylow_has_original_exchanged_fixed_eigensubgroups hGnonab hrecognition
      n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq.le hmodel hcov
      H hVu hJH hR hell hdiv W hVW hescape
  set Wa := coveringOddSylowAmbient H W with hWadef
  have hWaR : Wa ≤ (CFSG.pPrimeCore 2 H).map H.subtype := by
    rw [hWadef, coveringOddSylowAmbient, ← Subgroup.map_map]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hRodd : Odd (Nat.card ((CFSG.pPrimeCore 2 H).map H.subtype)) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hWodd : ∀ w ∈ Wa, Odd (orderOf w) := fun w hw =>
    hRodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ (hWaR hw))
  have hWaH : Wa ≤ H := hWaR.trans (Subgroup.map_subtype_le _)
  have hWu : ∀ w ∈ Wa, w * u = u * w := fun w hw =>
    commute_of_inverted_mem_normalizer (hWodd w hw) (hinv w hw) (hWaH hw) htu
  obtain ⟨Us, hUs, hUsNa, -, -, -, -, -, -, -, -, -, hUsK, hKs, -⟩ :=
    hEsc G hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd
      hf hq hmodel hcov H hVu hJH hR ell hell hdiv W hVW hescape s (Or.inl rfl)
  set Ws := localFixedGroup Wa s with hWsdef
  set Ks := Subgroup.centralizer (Ws : Set G) with hKsdef
  set Ds := (CFSG.pPrimeCore 2 Ks).map Ks.subtype with hDsdef
  have huK : u ∈ Ks := by
    rw [hKsdef, Subgroup.mem_centralizer_iff]
    intro w hw
    exact hWu w hw.1
  have hu2D : u ^ 2 ∈ Ds := by
    apply hKs
    rw [← commutatorElement_of_inverted hsu]
    exact Subgroup.commutator_mem_commutator huK (Subgroup.mem_zpowers s)
  have huD : u ∈ Ds := Subgroup.zpowers_le.mpr hu2D (mem_zpowers_sq_of_odd huodd)
  have hVWs : V ≤ Subgroup.normalizer (Ws : Set G) := fun v hv =>
    mem_normalizer_localFixedGroup (hVW hv)
      (Subgroup.mem_centralizer_singleton_iff.mp (hVs hv))
  have hVKs : V ≤ Subgroup.normalizer (Ks : Set G) :=
    hVWs.trans (normalizer_le_normalizer_centralizer' Ws)
  have hVDs : V ≤ Subgroup.normalizer (Ds : Set G) :=
    characteristic_subgroup_map_normalized V Ks hVKs (CFSG.pPrimeCore 2 Ks)
  have hVNs : V ≤ Subgroup.normalizer ((N s).map (C s).subtype : Set G) :=
    StationaryOddLocalization.actual_centralizer_core_normalized s V hVs
  have hVUs : V ≤ Subgroup.normalizer (Us : Set G) := fun v hv =>
    mem_normalizer_inverted hUs (hVNs hv)
      (Subgroup.mem_centralizer_singleton_iff.mp (hVt hv))
  have hDsodd : Odd (Nat.card Ds) := by
    rw [Subgroup.card_map_of_injective Ks.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hNsodd : Odd (Nat.card ((N s).map (C s).subtype)) := by
    rw [Subgroup.card_map_of_injective (C s).subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hUsodd : Odd (Nat.card Us) := hNsodd.of_dvd_nat (Subgroup.card_dvd_of_le hUsNa)
  have hDsnormal : (Ds.subgroupOf Ks).Normal := by
    have h : Ds.subgroupOf Ks = CFSG.pPrimeCore 2 Ks :=
      Subgroup.comap_map_eq_self_of_injective Ks.subtype_injective _
    rw [h]
    infer_instance
  have hModd : Odd (Nat.card (Ds ⊔ Us : Subgroup G)) :=
    StationaryOddLocalization.odd_card_sup_in_parent Ks Ds Us (Subgroup.map_subtype_le _)
      hUsK hDsnormal hDsodd hUsodd
  have hVM : V ≤ Subgroup.normalizer ((Ds ⊔ Us : Subgroup G) : Set G) := fun v hv =>
    mem_normalizer_sup (hVDs hv) (hVUs hv)
  obtain ⟨g, -, hgt, hgs, -, -, -, -, -, -, -, -, -, -, -, -, hlocal, -⟩ :=
    original_all_stationary_covers_produce_same_parameter_local_data hGnonab n hn S0 f0
      t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq.le hmodel hcov s (Or.inl rfl)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hNamb, -⟩ := hlocal
  have hw0N : g * u * g⁻¹ ∈ (N s).map (C s).subtype := by
    rw [← hNamb]
    exact ⟨u, huNa, rfl⟩
  have hw0inv : t * (g * u * g⁻¹) * t⁻¹ = (g * u * g⁻¹)⁻¹ := by
    rw [← hgs]
    calc g * s * g⁻¹ * (g * u * g⁻¹) * (g * s * g⁻¹)⁻¹ = g * (s * u * s⁻¹) * g⁻¹ := by group
      _ = (g * u * g⁻¹)⁻¹ := by rw [hsu]; group
  have hw0Us : g * u * g⁻¹ ∈ Us := (hUs _).mpr ⟨hw0N, hw0inv⟩
  have hw0ord : orderOf (g * u * g⁻¹) = r := by
    rw [← hur]
    exact (MulAut.conj g).orderOf_eq u
  have hrUs : r ∣ Nat.card Us := hw0ord ▸ Subgroup.orderOf_dvd_natCard Us hw0Us
  obtain ⟨Qs, hVQs, hQsne⟩ := normalized_subgroup_invariant_sylow_nontrivial 2 r Nat.prime_two
    hr V Us hV2 hVUs hUsodd.coprime_two_left hrUs
  set F := (Qs : Subgroup Us).map Us.subtype with hFdef
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQsne
  have hFUs : F ≤ Us := Subgroup.map_subtype_le _
  have hwt : t * (w : G) * t⁻¹ = (w : G)⁻¹ := ((hUs _).mp (hFUs w.2)).2
  obtain ⟨y, hy1, hyp, hty, hyu⟩ := exists_inverted_centralizing_witness V htV hsV ht1 hs1 hts
    hr (Ds ⊔ Us) hModd hVM (Subgroup.mem_sup_left huD) hur htu hVu F
    (hFUs.trans le_sup_right) (Qs.isPGroup'.map Us.subtype) hVQs w.2
    (fun h => hw1 (Subtype.ext h)) hwt
  obtain ⟨hVP, hstat, hcovP⟩ := stationaryCovered_explicit t s P hP
  have hloc :=
    stationary_centralizer_cover_prime_forces_local_invariant_subgroup_centralization
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf
      hq.le hmodel hr P hrN hVP hcovP hstat
  have hzu : Subgroup.zpowers u ≠ ⊥ := by
    intro h
    apply hu1
    have := Subgroup.mem_zpowers u
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hyH : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_zpowers_of_commute hyu)
  have hty' : t ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
    mem_normalizer_zpowers_of_conj (Or.inr hty)
  have hyC := ((hloc (Subgroup.zpowers u) hzu (Subgroup.zpowers_le.mpr huP) hVu).1
    (Subgroup.zpowers y) hyH hyp hty').1 (Subgroup.mem_zpowers y)
  have hyt : t * y * t⁻¹ = y := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hyC).symm, mul_inv_cancel_right]
  have hyodd : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := hyp.exists_card_eq
    rw [← Nat.card_zpowers, hk]
    exact (hur ▸ huodd : Odd r).pow
  exact hy1 (eq_one_of_conj_fixed_inverted hyodd hyt hty)

end Actual

end CFSG.Semidihedral.StationaryConfinement
