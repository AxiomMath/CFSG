module

public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactorFree
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinement
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactorNormal

public section

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups

theorem le_normalizer_map_of_normal {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (Y : Subgroup K) [Y.Normal] :
    K ≤ Subgroup.normalizer ((Y.map K.subtype : Subgroup G) : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance y hy _, rfl⟩

theorem mul_comm_of_isCyclic {G : Type*} [Group G] {W : Subgroup G} [IsCyclic W] :
    ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w := by
  intro w hw w' hw'
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, hw⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w', hw'⟩)
  have h := congrArg Subtype.val ((Commute.zpow_zpow_self g i j).eq)
  rw [hi, hj] at h
  exact h

theorem stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
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
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t s) :
    let qe := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let Na := (N t).map (C t).subtype
    let Ya := Y.map (C t).subtype
    let Ja := J.map (C t).subtype
    let Ea := (J ⊓ N t).map (C t).subtype
    let A₀ := Na ⊓ Subgroup.centralizer ({s} : Set G)
    let D := C t ⊓ Subgroup.centralizer ({s} : Set G)
    let R := (CFSG.pPrimeCore 2 D).map D.subtype
    let M := Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G)
    ∃ U W : Subgroup G,
      (∀ x : G, x ∈ U ↔ x ∈ Na ∧ s * x * s⁻¹ = x⁻¹) ∧
      (∀ x : G, x ∈ W ↔ x ∈ Ja ⊓ Subgroup.centralizer ({s} : Set G) ∧ Odd (orderOf x)) ∧
      U ≤ Na ∧ IsMulCommutative U ∧ (U.subgroupOf Na).Characteristic ∧
      Nat.Coprime (Nat.card U) (U.relIndex Na) ∧ (U.subgroupOf Na).Normal ∧
      U ⊔ A₀ = Na ∧ U ⊓ A₀ = ⊥ ∧ Nat.card U = A₀.relIndex Na ∧
      Subgroup.normalizer (Na : Set G) ≤ Subgroup.normalizer (U : Set G) ∧
      IsCyclic A₀ ∧ Nat.card A₀ ∣ qe / 2 ∧
      W ⊓ A₀ = ⊥ ∧ (∀ w ∈ W, ∀ a ∈ A₀, Commute w a) ∧ W ⊔ A₀ = R ⊓ Ya ∧
      W ⊔ A₀ ≤ M ∧ M ≤ Subgroup.normalizer ((W ⊔ A₀ : Subgroup G) : Set G) ∧
      (∀ a ∈ A₀, a ≠ 1 → U ⊓ Subgroup.centralizer ({a} : Set G) = ⊥) ∧
      (U ≠ ⊥ → A₀ ≠ ⊥ → ∀ a ∈ A₀, a ≠ 1 → ∀ x ∈ U, a * x * a⁻¹ = x → x = 1) ∧
      Ea ≤ U ⊓ (Subgroup.center Na).map Na.subtype ∧
      (Ea ≠ ⊥ → p ^ f = 9 ∧ Nat.card Ea = 3 ∧ A₀ = ⊥ ∧ Na = U ∧
        IsMulCommutative Na ∧ ∀ x ∈ Na, s * x * s⁻¹ = x⁻¹) := by
  intro qe T₀ Y H₀ J Na Ya Ja Ea A₀ D R M
  classical
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.index_ne_two_of_isSimpleGroup hGnonab
  let : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  obtain ⟨-, htV, hsV, -, ht1, -, -, -, hts'⟩ := pair_facts t s ht hs hsC hts
  have hcomm : Commute t s := hts'
  have hcovL := all_stationary_covers_give_original_layer_coverage t s hcov
  have hprimes := (all_original_stationary_cover_predicates_equivalent t s).mp hcov
  obtain ⟨hNaodd, -, -, -, U, hU, -, -, hUNa, hUab, hUchar, hUhall, hUnormal, hUA, hUA', -,
      hUcard, -, -, hUnorm, -, hA0U, -, -⟩ :=
    LocalInvertedHallSubgroups.original_all_prime_stationary_local_inverted_hall_subgroup
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf
      hq.le hmodel hprimes
  obtain ⟨W, hWmem, hWcyc, hWcard, hWR, hWA, hWAcomm, hBR, hEinv, ⟨d, hdJ, -, hd2, hds, hdW⟩,
      hCV, hRR, hX⟩ :=
    fixed_factor_ambient_data n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq.le
      hmodel hcovL s hsC hs hts
  obtain ⟨-, hcent3, hTI, -⟩ :=
    stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element G hGnonab
      hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  obtain ⟨hJN, -, hJY, -⟩ := localCentralizingLayer_facts n hn S0 f0 hG t s ht hnonab hcentral
    hnc p f hp hpodd hf hq.le hmodel hcov
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have hA₀Na : A₀ ≤ Na := inf_le_left
  have hcommJN : ∀ j ∈ Ja, ∀ x ∈ Na, j * x = x * j := fun j hj x hx =>
    layer_commute_odd_core t _ hJN hj hx
  have hDeq : Subgroup.centralizer (Subgroup.closure ({t, s} : Set G) : Set G) = D :=
    centralizer_closure_pair t s
  have hDM : D ≤ M := hDeq ▸ Subgroup.centralizer_le_normalizer _
  have hMD : M ≤ Subgroup.normalizer (D : Set G) := by
    rw [← hDeq]
    exact normalizer_le_normalizer_centralizer' _
  have hRn : M ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized M D hMD
      (CFSG.pPrimeCore 2 D)
  have hRodd : Odd (Nat.card R) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hRD : R ≤ D := Subgroup.map_subtype_le _
  have hLnormal : (CFSG.generalizedFitting (Gamma t)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hT₀normal : T₀.Normal := hLnormal.comap _
  have hYnormal : Y.Normal := hT₀normal.comap _
  have hYn : C t ≤ Subgroup.normalizer (Ya : Set G) := le_normalizer_map_of_normal (C t) Y
  have hdC : d ∈ C t := Subgroup.map_subtype_le _ hdJ
  have hdY : d ∈ Ya := Subgroup.map_mono hJY hdJ
  have hdA : ∀ a ∈ A₀, d * a = a * d := fun a ha => hcommJN d hdJ a (hA₀Na ha)
  have hWab := mul_comm_of_isCyclic (W := W)
  have hWAc : ∀ w ∈ W, ∀ a ∈ A₀, w * a = a * w := fun w hw a ha => (hWAcomm w hw a ha).eq
  have hAodd : ∀ a ∈ A₀, Odd (orderOf a) := fun a ha =>
    hNaodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Na (hA₀Na ha))
  have hWs : W ≤ Subgroup.centralizer ({s} : Set G) := fun w hw => ((hWmem w).mp hw).1.2
  have hBn : M ≤ Subgroup.normalizer ((W ⊔ A₀ : Subgroup G) : Set G) :=
    fixed_factor_product_normal n hn S0 f0 t s ht hs hsC hts R Ya W A₀ d hRD hRn hRodd
      hCV hYn hBR hWR hWab hWAc hAodd inf_le_right hWs
      hdY hdC hd2 hds hdW hdA hRR hX
  have hBM : W ⊔ A₀ ≤ M := by
    rw [hBR]
    exact inf_le_left.trans (hRD.trans hDM)
  obtain ⟨g, hgM, hgt, -⟩ :=
    OrderedPairLocalTransport.original_ordered_pair_normalizer_conjugator n hn S0 f0 t s s
      ht hs hcomm hts (Or.inl rfl)
  have hgC : g ∉ C t := by
    intro h
    apply hts
    rw [← hgt, Subgroup.mem_centralizer_singleton_iff.mp h, mul_inv_cancel_right]
  obtain ⟨hA₀cyc, hA₀dvd⟩ := fixed_factor_cyclic Na W A₀ g hWAc hA₀Na (hBn hgM) (hTI g hgC)
  rw [hWcard] at hA₀dvd
  obtain ⟨g', hg'M, hg't, -⟩ :=
    OrderedPairLocalTransport.original_ordered_pair_normalizer_conjugator n hn S0 f0 t s (t * s)
      ht hs hcomm hts (Or.inr rfl)
  have hg'inv : g'⁻¹ * (t * s) * g'⁻¹⁻¹ = t := by
    rw [← hg't]
    group
  have hUW : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u := fun u hu w hw =>
    (hcommJN w ((hWmem w).mp hw).1.1 u (hUNa hu)).symm
  have hfree := fixed_factor_fixed_point_free t s Na U A₀ W g'⁻¹ hNaC hNaodd hU hA₀Na hWAc hWA
    hUW (hBn (M.inv_mem hg'M)) hg'inv hcent3
  have hthus : U ≠ ⊥ → A₀ ≠ ⊥ → ∀ a ∈ A₀, a ≠ 1 → ∀ x ∈ U, a * x * a⁻¹ = x → x = 1 := by
    intro _ _ a ha ha1 x hx hax
    have hmem : x ∈ U ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      nth_rewrite 1 [← hax]
      group
    rw [hfree a ha ha1, Subgroup.mem_bot] at hmem
    exact hmem
  have hEU : Ea ≤ U ⊓ (Subgroup.center Na).map Na.subtype := by
    rintro _ ⟨e, he, rfl⟩
    have heNa : (e : G) ∈ Na := ⟨e, he.2, rfl⟩
    have heJ : (e : G) ∈ Ja := ⟨e, he.1, rfl⟩
    refine ⟨(hU _).mpr ⟨heNa, hEinv _ ⟨e, he, rfl⟩⟩,
      ⟨⟨e, heNa⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩⟩
    exact Subtype.ext (hcommJN _ heJ _ y.2).symm
  have hEne : Ea ≠ ⊥ → p ^ f = 9 ∧ Nat.card Ea = 3 ∧ A₀ = ⊥ ∧ Na = U ∧
      IsMulCommutative Na ∧ ∀ x ∈ Na, s * x * s⁻¹ = x⁻¹ := by
    intro hE
    have hEint : J ⊓ N t ≠ ⊥ := by
      intro h
      apply hE
      change (J ⊓ N t).map (C t).subtype = ⊥
      rw [h, Subgroup.map_bot]
    obtain ⟨-, -, -, -, hne9, h9⟩ :=
      Local.all_local_prime_covers_split_actual_layer_except_central_three_at_nine n hn S0 f0
        hG t ht hnonab hcentral hnc p f hp hpodd hf hq.le hmodel (Or.inl hcovL)
    have hq9 : p ^ f = 9 := by
      by_contra h
      exact hEint (hne9 h).1
    obtain ⟨-, hcard, -⟩ := h9 hq9
    have hEcard : Nat.card Ea = Nat.card (J ⊓ N t : Subgroup (C t)) :=
      Subgroup.card_map_of_injective (C t).subtype_injective
    have hEcard3 : Nat.card Ea = 3 := by
      rw [hEcard]
      rcases hcard with h1 | h3
      · exact absurd ((Subgroup.card_eq_one).mp h1) hEint
      · exact h3
    have hA₀bot : A₀ = ⊥ := by
      by_contra hA
      obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      apply hE
      rw [eq_bot_iff, ← hfree a ha ha1']
      intro x hx
      obtain ⟨hxU, ⟨z, hz, hzx⟩⟩ := hEU hx
      refine ⟨hxU, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← hzx]
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨a, hA₀Na ha⟩).symm
    have hNaU : Na = U := (hA0U hA₀bot).symm
    refine ⟨hq9, hEcard3, hA₀bot, hNaU, hNaU ▸ hUab, fun x hx => ((hU x).mp (hNaU ▸ hx)).2⟩
  exact ⟨U, W, hU, hWmem, hUNa, hUab, hUchar, hUhall, hUnormal, hUA, hUA', hUcard, hUnorm,
    hA₀cyc, hA₀dvd, hWA, hWAcomm, hBR, hBM, hBn, hfree, hthus, hEU, hEne⟩

end CFSG.Semidihedral.StationaryConfinement
