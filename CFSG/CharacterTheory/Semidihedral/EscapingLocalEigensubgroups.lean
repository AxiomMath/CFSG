module

public import CFSG.CharacterTheory.Semidihedral.ExchangedEigensubgroups
public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupNormalizer
public import CFSG.CharacterTheory.Semidihedral.LocalSylowNormalizerFactorization
public import CFSG.CharacterTheory.Semidihedral.LocalLayerAbelianQuotients
public import CFSG.CharacterTheory.Semidihedral.LocalProjectiveKernelQuotients
public import CFSG.CharacterTheory.Semidihedral.FullRootSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.NontrivialInvertedIntersectionCentrality

public noncomputable section

namespace CFSG.Semidihedral.EscapingLocalEigensubgroups

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryOddLocalization
open scoped IsMulCommutative

universe u v

variable {G : Type u} [Group G]

@[expose] def localLayerPreimage (t : G) : Subgroup (C t) :=
  ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)

@[expose] def localCentralizingLayer (t : G) : Subgroup (C t) :=
  let D := localLayerPreimage t ⊓ Subgroup.centralizer (N t : Set (C t))
  (CFSG.perfectResidual D).map D.subtype

@[expose] def localFixedGroup (W : Subgroup G) (i : G) : Subgroup G :=
  W ⊓ Subgroup.centralizer ({i} : Set G)

@[expose] def subgroupNormalizerAction (J W : Subgroup G)
    (hJW : J ≤ Subgroup.normalizer (W : Set G)) : J →* MulAut W :=
  W.normalizerMonoidHom.comp (Subgroup.inclusion hJW)

theorem subgroupNormalizerAction_value (J W : Subgroup G)
    (hJW : J ≤ Subgroup.normalizer (W : Set G)) (j : J) (w : W) :
    (subgroupNormalizerAction J W hJW j w : G) = (j : G) * w * (j : G)⁻¹ := by
  exact Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion hJW j) w

theorem two_power_element_in_normal_factor
    (J N0 : Subgroup G) [J.Normal] (hNodd : Odd (Nat.card N0))
    (x : G) (hx : x ∈ J ⊔ N0) (k : ℕ) (hxorder : orderOf x ∣ 2 ^ k) : x ∈ J := by
  let q := QuotientGroup.mk' J
  have hqodd : Odd (Nat.card (N0.map q)) := hNodd.of_dvd_nat (N0.card_map_dvd q)
  have hqx : q x ∈ N0.map q := by
    obtain ⟨j, hj, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hqj : q j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
    rw [map_mul, hqj, one_mul]
    exact Subgroup.mem_map_of_mem q hn
  have horderodd : Odd (orderOf (q x)) :=
    hqodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (N0.map q) hqx)
  have horderpower : orderOf (q x) ∣ 2 ^ k := (orderOf_map_dvd q x).trans hxorder
  have hone : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes (horderodd.coprime_two_left.pow_left k)
      horderpower (dvd_refl _)
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hone)

theorem positive_eigensubgroup_ambient_image (W : Subgroup G) [IsMulCommutative W]
    (i : G) (hiW : i ∈ Subgroup.normalizer (W : Set G)) :
    (ExchangedEigensubgroups.positiveGroup (W.normalizerMonoidHom ⟨i, hiW⟩)).map W.subtype =
      localFixedGroup W i := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    apply (StationaryOddLocalization.conj_fixed_iff i (x : G)).mp
    change W.normalizerMonoidHom ⟨i, hiW⟩ x = x at hx
    have h := congrArg Subtype.val hx
    simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  · rintro ⟨hw, hi⟩
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    apply Subtype.ext
    change (W.normalizerMonoidHom ⟨i, hiW⟩ ⟨w, hw⟩ : G) = w
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (StationaryOddLocalization.conj_fixed_iff i w).mpr hi

theorem odd_subgroup_intersection_kernel_join_involution
    (N0 W : Subgroup G) [N0.Normal] (hWodd : Odd (Nat.card W))
    (i : G) (hi : orderOf i = 2) :
    W ⊓ (N0 ⊔ Subgroup.zpowers i) = W ⊓ N0 := by
  apply le_antisymm
  · rintro w ⟨hw, hker⟩
    refine ⟨hw, ?_⟩
    have hwodd : Odd (orderOf w) :=
      hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hw)
    exact PerfectLayerNormalization.odd_element_in_kernel_join_involution
      N0 i w hi hwodd hker
  · exact inf_le_inf_left W le_sup_left

@[expose] def stationaryCoveredLocalSylow (t s : G) {ell : ℕ} (P : Sylow ell (N t)) : Prop :=
  let Pa := LocalSylowNormalizerFactorization.localSylowAmbient t P
  let H := Subgroup.normalizer (Pa : Set G)
  Subgroup.closure ({t, s} : Set G) ≤ H ∧
    (∃ P0 : Sylow ell (CFSG.pPrimeCore 2 H),
      ((P0 : Subgroup (CFSG.pPrimeCore 2 H)).map
        (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)) = Pa) ∧
    ((Subgroup.centralizer (Pa : Set G)).subgroupOf (C t) ⊓
      localLayerPreimage t).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)

@[expose] def allLocalPrimeStationaryCovers (t s : G) : Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (N t) →
    ∃ P : Sylow ell (N t), stationaryCoveredLocalSylow t s P

theorem centralizer_of_original_subtype_image (D : Subgroup G) (P : Subgroup D) :
    (Subgroup.centralizer (P.map D.subtype : Set G)).subgroupOf D =
      Subgroup.centralizer (P : Set D) := by
  ext d
  constructor
  · intro hd
    apply Subgroup.mem_centralizer_iff.mpr
    intro p hp
    change (d : G) ∈ Subgroup.centralizer (P.map D.subtype : Set G) at hd
    have h := Subgroup.mem_centralizer_iff.mp hd p
      (Subgroup.mem_map_of_mem D.subtype hp)
    exact Subtype.ext h
  · intro hd
    change (d : G) ∈ Subgroup.centralizer (P.map D.subtype : Set G)
    apply Subgroup.mem_centralizer_iff.mpr
    rintro p ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hd x hx)

theorem all_stationary_covers_give_original_layer_coverage (t s : G)
    (hcov : allLocalPrimeStationaryCovers t s) :
    ∀ (ell : ℕ) [Fact ell.Prime], ell ∣ Nat.card (N t) → ∃ P : Sylow ell (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype) : Set (C t)) ⊓
        localLayerPreimage t).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  intro ell hprime hdiv
  obtain ⟨P, -, -, hcover⟩ := hcov ell hprime.out hdiv
  refine ⟨P, ?_⟩
  rw [← centralizer_of_original_subtype_image (C t)
    ((P : Subgroup (N t)).map (N t).subtype)]
  exact hcover

@[expose] def coveringOddSylowAmbient (H : Subgroup G) {ell : ℕ}
    (W : Sylow ell (CFSG.pPrimeCore 2 H)) : Subgroup G :=
  (W : Subgroup (CFSG.pPrimeCore 2 H)).map
    (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)

theorem prime_absent_fixed_subgroup_eq_bot (t : G) {ell : ℕ} (hell : ell.Prime)
    (W N0 : Subgroup G) (hWp : IsPGroup ell W) (habsent : ¬ ell ∣ Nat.card N0)
    (hfixed : W ⊓ Subgroup.centralizer ({t} : Set G) ≤ N0) :
    W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro w hw
  apply Subgroup.mem_bot.mpr
  obtain ⟨k, hk⟩ := hWp.exists_orderOf_dvd_pow (⟨w, hw.1⟩ : W)
  have hpower : orderOf w ∣ ell ^ k := by
    have he := orderOf_injective W.subtype W.subtype_injective (⟨w, hw.1⟩ : W)
    exact he.symm ▸ hk
  have hdiv : orderOf w ∣ Nat.card N0 := Subgroup.orderOf_dvd_natCard N0 (hfixed hw)
  have hcop := (hell.coprime_iff_not_dvd.mpr habsent).pow_left k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hpower hdiv)

theorem escaping_local_odd_sylow_is_normalized_abelian_and_inverted
    [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH : (localCentralizingLayer t).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ell (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G))
    (hescape : ¬ coveringOddSylowAmbient H W ≤ C t) :
    let Wa := coveringOddSylowAmbient H W
    (localCentralizingLayer t).map (C t).subtype ≤ Subgroup.normalizer (Wa : Set G) ∧
      IsMulCommutative Wa ∧ (∀ w ∈ Wa, t * w * t⁻¹ = w⁻¹) ∧
      Wa ⊓ C t = ⊥ ∧ Wa ≠ ⊥ := by
  let : Fact ell.Prime := ⟨hell⟩
  let Wa := coveringOddSylowAmbient H W
  let Ra := (CFSG.pPrimeCore 2 H).map H.subtype
  let Na := (N t).map (C t).subtype
  have hcoverage := all_stationary_covers_give_original_layer_coverage t s hcov
  obtain ⟨-, -, -, -, hinter, -, -, -, hJA, hW, -⟩ :=
    PerfectLayerNormalization.original_full_layer_normalization_for_local_odd_sylow
      hGnonab hrecognition n hn S0 f0 t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
        hcoverage s hsC hs hts.symm H hVH hJH hR ell hdiv W hVW
  have hJW : (localCentralizingLayer t).map (C t).subtype ≤
      Subgroup.normalizer (Wa : Set G) := hJA.trans inf_le_right
  have hWp : IsPGroup ell Wa := W.isPGroup'.map
    (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
  have hWRa : Wa ≤ Ra := by
    rintro w ⟨x, hx, rfl⟩
    exact ⟨(x : H), x.property, rfl⟩
  have hfixed : Wa ⊓ C t ≤ Na :=
    ((inf_le_inf hWRa le_rfl).trans_eq hinter).trans inf_le_left
  have hellodd : Odd ell :=
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))).of_dvd_nat hdiv
  have hWaodd : Odd (Nat.card Wa) :=
    StationaryOddLocalization.odd_card_of_pgroup hell hellodd Wa hWp
  have htW : t ∈ Subgroup.normalizer (Wa : Set G) :=
    hVW (Subgroup.subset_closure (by simp))
  refine ⟨hJW, ?_⟩
  by_cases hellN : ell ∣ Nat.card (N t)
  · obtain ⟨P, hVP, hstationary, hcover⟩ := hcov ell hell hellN
    have hscalar :=
      (stationary_localization_forces_scalar_action_on_odd_subgroups_with_local_fixed_points
        hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
        p f hp hpodd hf hq hmodel hell P hellN hVP hcover
        (by
          obtain ⟨P0, hP0⟩ := hstationary
          refine ⟨P0, ?_⟩
          rw [Subgroup.map_map]
          exact hP0)).1 Wa hWp hVW hfixed
    obtain ⟨hchoice, hanti, -⟩ := hscalar
    rcases hchoice with hN | hinv
    · exact False.elim (hescape (hN.trans (Subgroup.map_subtype_le _)))
    · obtain ⟨hab, hbot⟩ := hanti hinv
      exact ⟨hab, hinv, hbot, hW⟩
  · have hNa : Nat.card Na = Nat.card (N t) := Subgroup.card_subtype (C t) (N t)
    have hfixedbot : Wa ⊓ C t = ⊥ := prime_absent_fixed_subgroup_eq_bot t hell Wa Na hWp
      (by rwa [hNa]) hfixed
    have hinv := StationaryOddLocalization.inverted_of_trivial_fixed_subgroup
      t ht Wa hWaodd htW hfixedbot
    exact ⟨StationaryOddLocalization.abelian_of_inverted t Wa hinv, hinv, hfixedbot, hW⟩

theorem original_order_four_exchange_in_layer_univ_zero
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ d : G, d ∈ (localLayerPreimage t).map (C t).subtype ∧
      orderOf d = 4 ∧ d ^ 2 = t ∧ d * s * d⁻¹ = t * s := by
  let sc : C t := ⟨s, hsC⟩
  have hsc : orderOf sc = 2 := (Subgroup.orderOf_coe sc).symm.trans hs
  have hscne : sc ≠ tInC t := fun h => hts (congrArg Subtype.val h).symm
  obtain ⟨⟨-, F, hfield, hfinite, A, a, hcard, hA, -, -, -, -, -, haF, -, -, -, hchoice⟩,
      hall⟩ := ActualFourGroupNormalizer.actual_simple_layer_four_group_normalizer_action
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  obtain ⟨Psi, hz, hu, -⟩ := hchoice sc hsc hscne
  obtain ⟨⟨x, y, hxy⟩, hdata⟩ := hall F A (MatrixCover.fixedUnit F A a)
    (ActualFourGroupCentralizer.fixed_coefficient_action F A a) sc hsc hscne Psi hz hu
      hcard hA haF
  obtain ⟨d0, hd0, hdsq, hds, -⟩ := (hdata x y hxy).actual_lift_and_action
  let dc : C t := d0
  have hdorder : orderOf dc = 4 := (Subgroup.orderOf_coe d0).trans hd0
  obtain ⟨F0, hfield0, hfinite0, A0, rho0, mdata⟩ := actual_simple_layer_matrix_data
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F0 := hfield0
  let : Finite F0 := hfinite0
  have hdY : dc ∈ localLayerPreimage t :=
    actual_order_four_image_mem_layer n hn S0 f0 hG t ht F0 A0 p f rho0 mdata dc hdorder
  refine ⟨(dc : G), Subgroup.mem_map_of_mem (C t).subtype hdY,
    (Subgroup.orderOf_coe dc).trans hdorder, ?_, ?_⟩
  · exact congrArg (fun x : ActualFourGroupNormalizer.K sc => ((x : C t) : G)) hdsq
  · exact congrArg Subtype.val hds

theorem original_order_four_exchange_in_layer [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) :
    ∃ d : G, d ∈ (localLayerPreimage t).map (C t).subtype ∧
      orderOf d = 4 ∧ d ^ 2 = t ∧ d * s * d⁻¹ = t * s := by
  obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S0' : Sylow 2 G' := S0.mapSurjective (f := e.toMonoidHom) e.surjective
  let f0' : SemidihedralGroup n ≃* S0' :=
    f0.trans ((S0 : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective)
  let c := PerfectLayerNormalization.originalCentralizerEquiv e t
  let d := PerfectLayerNormalization.originalGeneralizedFittingEquiv e t
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma (e t))) := d.symm.isSimpleGroup
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg (Subgroup.map
      (PerfectLayerNormalization.originalReducedQuotientEquiv e t).toMonoidHom) hcentral
    rw [PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  have hsC' : e s ∈ C (e t) := by
    exact (c ⟨s, hsC⟩).property
  obtain ⟨d', hdY', hdorder', hdsq', hdexchange'⟩ :=
    original_order_four_exchange_in_layer_univ_zero
      n hn S0' f0' (PerfectLayerNormalization.isomorphism_transports_no_index_two e hG)
      (e t) (e s) ((e.orderOf_eq t).trans ht) ((e.orderOf_eq s).trans hs) hsC'
      (fun h => hts (e.injective h))
      (PerfectLayerNormalization.isomorphism_transports_nonabelian d hnonab) hcentral'
      (PerfectLayerNormalization.isomorphism_transports_noncyclic_sylows d 2 hnc)
      p f hp hpodd hf (PerfectLayerNormalization.original_psl_two_model_transport d p f hmodel)
  obtain ⟨dc', hdc', hval⟩ := Subgroup.mem_map.mp hdY'
  have hY : (localLayerPreimage t).map c.toMonoidHom = localLayerPreimage (e t) :=
    (PerfectLayerNormalization.original_local_layer_preimages_transport e t).2
  have hdc : c.symm dc' ∈ localLayerPreimage t := by
    rw [← hY, Subgroup.mem_map_equiv] at hdc'
    exact hdc'
  have heval : e ((c.symm dc' : C t) : G) = d' := by
    change e (e.symm (dc' : G')) = d'
    exact (e.apply_symm_apply _).trans hval
  refine ⟨((c.symm dc' : C t) : G),
    Subgroup.mem_map_of_mem (C t).subtype hdc, ?_, ?_, ?_⟩
  · rw [← e.orderOf_eq, heval, hdorder']
  · apply e.injective
    rw [map_pow, heval, hdsq']
  · apply e.injective
    simpa only [map_mul, map_inv, heval] using hdexchange'

theorem all_stationary_covers_produce_original_order_four_exchange [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s) :
    ∃ d : G, d ∈ (localCentralizingLayer t).map (C t).subtype ∧
      orderOf d = 4 ∧ d ^ 2 = t ∧ d * s * d⁻¹ = t * s := by
  obtain ⟨-, hnormal, -, -, -, hproduct, -⟩ :=
    PerfectLayerNormalization.original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
        (all_stationary_covers_give_original_layer_coverage t s hcov)
  let : (localCentralizingLayer t).Normal := hnormal
  obtain ⟨d, hdY, hdorder, hdsq, hdexchange⟩ := original_order_four_exchange_in_layer
    n hn S0 f0 hG t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨dc, hdc, hval⟩ := Subgroup.mem_map.mp hdY
  have hdcorder : orderOf dc = 4 := by
    exact (Subgroup.orderOf_coe dc).symm.trans ((congrArg orderOf hval).trans hdorder)
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hdcJ : dc ∈ localCentralizingLayer t :=
    two_power_element_in_normal_factor (localCentralizingLayer t) (N t) hNodd dc
      (hproduct ▸ hdc) 2 (by rw [hdcorder]; exact dvd_refl 4)
  exact ⟨d, hval ▸ Subgroup.mem_map_of_mem (C t).subtype hdcJ,
    hdorder, hdsq, hdexchange⟩

theorem original_involution_normalizer_action_square (W : Subgroup G) (s : G)
    (hs : orderOf s = 2) (hsW : s ∈ Subgroup.normalizer (W : Set G)) :
    W.normalizerMonoidHom ⟨s, hsW⟩ ^ 2 = 1 := by
  have hsq : (⟨s, hsW⟩ : Subgroup.normalizer (W : Set G)) ^ 2 = 1 := by
    apply Subtype.ext
    exact hs ▸ pow_orderOf_eq_one s
  rw [← map_pow, hsq, map_one]

theorem original_product_normalizer_action (W : Subgroup G) (t s : G)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G)) :
    W.normalizerMonoidHom ⟨t * s, (Subgroup.normalizer (W : Set G)).mul_mem htW hsW⟩ =
      W.normalizerMonoidHom ⟨t, htW⟩ * W.normalizerMonoidHom ⟨s, hsW⟩ :=
  map_mul W.normalizerMonoidHom ⟨t, htW⟩ ⟨s, hsW⟩

theorem negative_eigensubgroup_ambient_image (W : Subgroup G) [IsMulCommutative W]
    (t s : G) (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) :
    (ExchangedEigensubgroups.negativeGroup (W.normalizerMonoidHom ⟨s, hsW⟩)).map W.subtype =
      localFixedGroup W (t * s) := by
  let rho := W.normalizerMonoidHom
  have ht : ∀ w : W, rho ⟨t, htW⟩ w = w⁻¹ := by
    intro w
    apply Subtype.ext
    exact hinv w w.property
  have hnegative : ExchangedEigensubgroups.negativeGroup (rho ⟨s, hsW⟩) =
      ExchangedEigensubgroups.positiveGroup
        (rho ⟨t * s, (Subgroup.normalizer (W : Set G)).mul_mem htW hsW⟩) := by
    rw [original_product_normalizer_action]
    exact ExchangedEigensubgroups.negativeGroup_eq_twisted_fixed rho ⟨t, htW⟩ ht _
  rw [hnegative]
  exact positive_eigensubgroup_ambient_image W (t * s) _

@[expose] def originalFixedEigenEquiv (W : Subgroup G) [IsMulCommutative W]
    (s : G) (hsW : s ∈ Subgroup.normalizer (W : Set G)) :
    ExchangedEigensubgroups.positiveGroup (W.normalizerMonoidHom ⟨s, hsW⟩) ≃*
      localFixedGroup W s :=
  ((ExchangedEigensubgroups.positiveGroup (W.normalizerMonoidHom ⟨s, hsW⟩)).equivMapOfInjective
    W.subtype W.subtype_injective).trans
      (MulEquiv.subgroupCongr (positive_eigensubgroup_ambient_image W s hsW))

theorem originalFixedEigenEquiv_value (W : Subgroup G) [IsMulCommutative W]
    (s : G) (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (x : ExchangedEigensubgroups.positiveGroup (W.normalizerMonoidHom ⟨s, hsW⟩)) :
    (originalFixedEigenEquiv W s hsW x : G) = ((x : W) : G) := by
  rw [originalFixedEigenEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply]
  rfl

@[expose] def originalNegativeEigenEquiv (W : Subgroup G) [IsMulCommutative W]
    (t s : G) (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) :
    ExchangedEigensubgroups.negativeGroup (W.normalizerMonoidHom ⟨s, hsW⟩) ≃*
      localFixedGroup W (t * s) :=
  ((ExchangedEigensubgroups.negativeGroup (W.normalizerMonoidHom ⟨s, hsW⟩)).equivMapOfInjective
    W.subtype W.subtype_injective).trans
      (MulEquiv.subgroupCongr (negative_eigensubgroup_ambient_image W t s htW hsW hinv))

theorem originalNegativeEigenEquiv_value (W : Subgroup G) [IsMulCommutative W]
    (t s : G) (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)
    (x : ExchangedEigensubgroups.negativeGroup (W.normalizerMonoidHom ⟨s, hsW⟩)) :
    (originalNegativeEigenEquiv W t s htW hsW hinv x : G) = ((x : W) : G) := by
  rw [originalNegativeEigenEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply]
  rfl

@[expose] def originalFixedEigenProductEquiv (W : Subgroup G) [IsMulCommutative W]
    (hWodd : Odd (Nat.card W)) (t s : G) (hs : orderOf s = 2)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) :
    localFixedGroup W s × localFixedGroup W (t * s) ≃* W :=
  ((originalFixedEigenEquiv W s hsW).symm.prodCongr
    (originalNegativeEigenEquiv W t s htW hsW hinv).symm).trans
      (ExchangedEigensubgroups.eigenProductEquiv hWodd (W.normalizerMonoidHom ⟨s, hsW⟩)
        (original_involution_normalizer_action_square W s hs hsW))

theorem originalFixedEigenProductEquiv_value (W : Subgroup G) [IsMulCommutative W]
    (hWodd : Odd (Nat.card W)) (t s : G) (hs : orderOf s = 2)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)
    (x : localFixedGroup W s × localFixedGroup W (t * s)) :
    (originalFixedEigenProductEquiv W hWodd t s hs htW hsW hinv x : G) =
      (x.1 : G) * (x.2 : G) := by
  let ep := originalFixedEigenEquiv W s hsW
  let en := originalNegativeEigenEquiv W t s htW hsW hinv
  have hp := originalFixedEigenEquiv_value W s hsW (ep.symm x.1)
  have hn := originalNegativeEigenEquiv_value W t s htW hsW hinv (en.symm x.2)
  rw [ep.apply_symm_apply] at hp
  rw [en.apply_symm_apply] at hn
  change (((ep.symm x.1 : W) : G) * ((en.symm x.2 : W) : G)) = _
  rw [← hp, ← hn]

theorem original_fixed_eigensubgroups_generate (W : Subgroup G) [IsMulCommutative W]
    (hWodd : Odd (Nat.card W)) (t s : G) (hs : orderOf s = 2)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) :
    localFixedGroup W s ⊔ localFixedGroup W (t * s) = W := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro w hw
  obtain ⟨x, hx⟩ := (originalFixedEigenProductEquiv W hWodd t s hs htW hsW hinv).surjective
    (⟨w, hw⟩ : W)
  have hvalue := (originalFixedEigenProductEquiv_value W hWodd t s hs htW hsW hinv x).symm
  rw [hx] at hvalue
  change (x.1 : G) * (x.2 : G) = w at hvalue
  rw [← hvalue]
  have hp : localFixedGroup W s ≤ localFixedGroup W s ⊔ localFixedGroup W (t * s) :=
    le_sup_left
  have hn : localFixedGroup W (t * s) ≤ localFixedGroup W s ⊔ localFixedGroup W (t * s) :=
    le_sup_right
  exact (localFixedGroup W s ⊔ localFixedGroup W (t * s)).mul_mem
    (hp x.1.property) (hn x.2.property)

theorem original_normalizer_exchange_action (W : Subgroup G) [IsMulCommutative W]
    (t s d : G) (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hdW : d ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) (hexchange : d * s * d⁻¹ = t * s) :
    ∀ w : W, W.normalizerMonoidHom ⟨d, hdW⟩ (W.normalizerMonoidHom ⟨s, hsW⟩ w) =
      (W.normalizerMonoidHom ⟨s, hsW⟩ (W.normalizerMonoidHom ⟨d, hdW⟩ w))⁻¹ := by
  let rho := W.normalizerMonoidHom
  let T : Subgroup.normalizer (W : Set G) := ⟨t, htW⟩
  let S : Subgroup.normalizer (W : Set G) := ⟨s, hsW⟩
  let D : Subgroup.normalizer (W : Set G) := ⟨d, hdW⟩
  have ht : ∀ w : W, rho T w = w⁻¹ := by
    intro w
    apply Subtype.ext
    exact hinv w w.property
  have hrel : D * S * D⁻¹ = T * S := Subtype.ext hexchange
  have haction : rho D * rho S * (rho D)⁻¹ = rho T * rho S := by
    simpa only [map_mul, map_inv] using congrArg rho hrel
  exact ExchangedEigensubgroups.exchange_identity rho T D ht (rho S) haction

@[expose] def originalFixedEigenExchangeEquiv (W : Subgroup G) [IsMulCommutative W]
    (t s d : G) (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hdW : d ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) (hexchange : d * s * d⁻¹ = t * s) :
    localFixedGroup W s ≃* localFixedGroup W (t * s) :=
  (originalFixedEigenEquiv W s hsW).symm.trans
    ((ExchangedEigensubgroups.exchangeEquiv
      (W.normalizerMonoidHom ⟨s, hsW⟩) (W.normalizerMonoidHom ⟨d, hdW⟩)
      (original_normalizer_exchange_action W t s d htW hsW hdW hinv hexchange)).trans
        (originalNegativeEigenEquiv W t s htW hsW hinv))

theorem originalFixedEigenExchangeEquiv_value (W : Subgroup G) [IsMulCommutative W]
    (t s d : G) (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hdW : d ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) (hexchange : d * s * d⁻¹ = t * s)
    (x : localFixedGroup W s) :
    (originalFixedEigenExchangeEquiv W t s d htW hsW hdW hinv hexchange x : G) =
      d * (x : G) * d⁻¹ := by
  let ep := originalFixedEigenEquiv W s hsW
  have hp := originalFixedEigenEquiv_value W s hsW (ep.symm x)
  rw [ep.apply_symm_apply] at hp
  rw [originalFixedEigenExchangeEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    originalNegativeEigenEquiv_value, ExchangedEigensubgroups.exchangeEquiv_apply,
    Subgroup.normalizerMonoidHom_apply_apply_coe]
  change d * ((ep.symm x : W) : G) * d⁻¹ = _
  rw [← hp]

theorem original_fixed_eigensubgroup_conjugation_image (W : Subgroup G)
    [IsMulCommutative W] (t s d : G)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hdW : d ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) (hexchange : d * s * d⁻¹ = t * s) :
    (localFixedGroup W s).map (MulAut.conj d).toMonoidHom = localFixedGroup W (t * s) := by
  let e := originalFixedEigenExchangeEquiv W t s d htW hsW hdW hinv hexchange
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hv := originalFixedEigenExchangeEquiv_value W t s d htW hsW hdW hinv hexchange
      (⟨x, hx⟩ : localFixedGroup W s)
    change d * x * d⁻¹ ∈ localFixedGroup W (t * s)
    rw [← hv]
    exact (e ⟨x, hx⟩).property
  · intro hw
    obtain ⟨x, hx⟩ := e.surjective (⟨w, hw⟩ : localFixedGroup W (t * s))
    refine ⟨(x : G), x.property, ?_⟩
    have hv := originalFixedEigenExchangeEquiv_value W t s d htW hsW hdW hinv hexchange x
    rw [hx] at hv
    exact hv.symm

theorem original_fixed_eigensubgroups_disjoint (W : Subgroup G) [IsMulCommutative W]
    (hWodd : Odd (Nat.card W)) (t s : G)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) :
    Disjoint (localFixedGroup W s) (localFixedGroup W (t * s)) := by
  have hd := Subgroup.disjoint_map W.subtype_injective
    (ExchangedEigensubgroups.eigengroups_disjoint hWodd (W.normalizerMonoidHom ⟨s, hsW⟩))
  rw [positive_eigensubgroup_ambient_image, negative_eigensubgroup_ambient_image W t s htW hsW
    hinv] at hd
  exact hd

theorem original_fixed_eigensubgroups_card_eq (W : Subgroup G) [IsMulCommutative W]
    (t s d : G) (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hdW : d ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) (hexchange : d * s * d⁻¹ = t * s) :
    Nat.card (localFixedGroup W s) = Nat.card (localFixedGroup W (t * s)) :=
  Nat.card_congr (originalFixedEigenExchangeEquiv W t s d htW hsW hdW hinv hexchange).toEquiv

theorem original_fixed_eigensubgroups_nontrivial (W : Subgroup G) [IsMulCommutative W]
    (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W)) (t s d : G) (hs : orderOf s = 2)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G))
    (hdW : d ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) (hexchange : d * s * d⁻¹ = t * s) :
    localFixedGroup W s ≠ ⊥ ∧ localFixedGroup W (t * s) ≠ ⊥ := by
  let : Nontrivial W := W.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨hp, hn⟩ := ExchangedEigensubgroups.eigengroups_nontrivial hWodd
    (W.normalizerMonoidHom ⟨s, hsW⟩)
    (original_involution_normalizer_action_square W s hs hsW)
    (W.normalizerMonoidHom ⟨d, hdW⟩)
    (original_normalizer_exchange_action W t s d htW hsW hdW hinv hexchange)
  let := hp
  let := hn
  have hfp : Nontrivial (localFixedGroup W s) :=
    (originalFixedEigenEquiv W s hsW).symm.toEquiv.nontrivial
  have hfn : Nontrivial (localFixedGroup W (t * s)) :=
    (originalNegativeEigenEquiv W t s htW hsW hinv).symm.toEquiv.nontrivial
  exact ⟨(localFixedGroup W s).nontrivial_iff_ne_bot.mp hfp,
    (localFixedGroup W (t * s)).nontrivial_iff_ne_bot.mp hfn⟩

section OriginalEscaping

open CFSG.Open CFSG.Semidihedral

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
variable (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH : (localCentralizingLayer t).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ell (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G))
    (hescape : ¬ coveringOddSylowAmbient H W ≤ C t)

include hGnonab hrecognition hn f0 ht hs hsC hts hnonab hcentral hnc
  hp hpodd hf hq hmodel hcov hVH hJH hR hell hdiv hVW hescape


theorem escaping_local_odd_sylow_has_original_exchanged_fixed_eigensubgroups :
    let Wa := coveringOddSylowAmbient H W
    (localCentralizingLayer t).map (C t).subtype ≤ Subgroup.normalizer (Wa : Set G) ∧
      IsMulCommutative Wa ∧ (∀ w ∈ Wa, t * w * t⁻¹ = w⁻¹) ∧
      Wa ⊓ C t = ⊥ ∧ Wa ≠ ⊥ ∧
      ∃ d : G, d ∈ (localCentralizingLayer t).map (C t).subtype ∧
        orderOf d = 4 ∧ d ^ 2 = t ∧ d * s * d⁻¹ = t * s ∧
        d ∈ Subgroup.normalizer (Wa : Set G) ∧
        (localFixedGroup Wa s).map (MulAut.conj d).toMonoidHom = localFixedGroup Wa (t * s) ∧
        localFixedGroup Wa s ≠ ⊥ ∧ localFixedGroup Wa (t * s) ≠ ⊥ ∧
        Nat.card (localFixedGroup Wa s) = Nat.card (localFixedGroup Wa (t * s)) ∧
        Disjoint (localFixedGroup Wa s) (localFixedGroup Wa (t * s)) ∧
        localFixedGroup Wa s ⊔ localFixedGroup Wa (t * s) = Wa ∧
        ∃ e : localFixedGroup Wa s × localFixedGroup Wa (t * s) ≃* Wa,
          ∀ x, (e x : G) = (x.1 : G) * (x.2 : G) := by
  let : Fact ell.Prime := ⟨hell⟩
  let Wa := coveringOddSylowAmbient H W
  obtain ⟨hJW, hab, hinv, hfixed, hW⟩ :=
    escaping_local_odd_sylow_is_normalized_abelian_and_inverted
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape
  let : IsMulCommutative Wa := hab
  have hellodd : Odd ell :=
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))).of_dvd_nat hdiv
  have hWp : IsPGroup ell Wa := W.isPGroup'.map
    (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
  have hWaodd : Odd (Nat.card Wa) :=
    StationaryOddLocalization.odd_card_of_pgroup hell hellodd Wa hWp
  have htW : t ∈ Subgroup.normalizer (Wa : Set G) :=
    hVW (Subgroup.subset_closure (by simp))
  have hsW : s ∈ Subgroup.normalizer (Wa : Set G) :=
    hVW (Subgroup.subset_closure (by simp))
  obtain ⟨d, hd, ho, hsq, hex⟩ :=
    all_stationary_covers_produce_original_order_four_exchange n hn S0 f0
      (PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab)
      t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  have hdW := hJW hd
  obtain ⟨hsp, hsn⟩ := original_fixed_eigensubgroups_nontrivial Wa hW hWaodd
    t s d hs htW hsW hdW hinv hex
  refine ⟨hJW, hab, hinv, hfixed, hW, d, hd, ho, hsq, hex, hdW, ?_, hsp, hsn, ?_, ?_, ?_, ?_⟩
  · exact original_fixed_eigensubgroup_conjugation_image Wa t s d htW hsW hdW hinv hex
  · exact original_fixed_eigensubgroups_card_eq Wa t s d htW hsW hdW hinv hex
  · exact original_fixed_eigensubgroups_disjoint Wa hWaodd t s htW hsW hinv
  · exact original_fixed_eigensubgroups_generate Wa hWaodd t s hs htW hsW hinv
  · exact ⟨originalFixedEigenProductEquiv Wa hWaodd t s hs htW hsW hinv,
      originalFixedEigenProductEquiv_value Wa hWaodd t s hs htW hsW hinv⟩

end OriginalEscaping

theorem all_original_stationary_cover_predicates_equivalent (t s : G) :
    allLocalPrimeStationaryCovers t s ↔
      OrderedPairLocalTransport.OriginalAllPrimeStationaryCover t s := by
  constructor
  · intro h r hr hdiv
    obtain ⟨P, hV, hstationary, hcover⟩ := h r hr.out hdiv
    refine ⟨P, ?_, ?_, ?_⟩
    · simpa only [OrderedPairLocalTransport.originalSylowAmbient,
        LocalSylowNormalizerFactorization.localSylowAmbient,
        LocalSylowNormalizerFactorization.localSylowInCentralizer, Subgroup.map_map] using hV
    · unfold OrderedPairLocalTransport.OriginalSylowStationarity
      rw [StationaryOddLocalization.original_oddCore_eq_twoPrimeCore]
      change ∃ Q : Sylow r (CFSG.pPrimeCore 2
        (Subgroup.normalizer (LocalSylowNormalizerFactorization.localSylowAmbient t P : Set G))),
        ((Q : Subgroup _).map (CFSG.pPrimeCore 2
          (Subgroup.normalizer
            (LocalSylowNormalizerFactorization.localSylowAmbient t P : Set G))).subtype).map
          (Subgroup.normalizer
            (LocalSylowNormalizerFactorization.localSylowAmbient t P : Set G)).subtype =
            LocalSylowNormalizerFactorization.localSylowAmbient t P
      simpa only [Subgroup.map_map] using hstationary
    · change (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype) : Set (C t)) ⊓
        localLayerPreimage t).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
      rw [← centralizer_of_original_subtype_image (C t)
        ((P : Subgroup (N t)).map (N t).subtype)]
      simpa only [LocalSylowNormalizerFactorization.localSylowAmbient,
        LocalSylowNormalizerFactorization.localSylowInCentralizer, Subgroup.map_map] using hcover
  · intro h r hr hdiv
    let : Fact r.Prime := ⟨hr⟩
    obtain ⟨P, hV, hstationary, hcover⟩ := h r hdiv
    refine ⟨P, ?_, ?_, ?_⟩
    · simpa only [OrderedPairLocalTransport.originalSylowAmbient,
        LocalSylowNormalizerFactorization.localSylowAmbient,
        LocalSylowNormalizerFactorization.localSylowInCentralizer, Subgroup.map_map] using hV
    · unfold OrderedPairLocalTransport.OriginalSylowStationarity at hstationary
      rw [StationaryOddLocalization.original_oddCore_eq_twoPrimeCore] at hstationary
      change ∃ Q : Sylow r (CFSG.pPrimeCore 2
        (Subgroup.normalizer (OrderedPairLocalTransport.originalSylowAmbient t P : Set G))),
        (Q : Subgroup _).map
          ((Subgroup.normalizer
              (OrderedPairLocalTransport.originalSylowAmbient t P : Set G)).subtype.comp
            (CFSG.pPrimeCore 2
              (Subgroup.normalizer
                (OrderedPairLocalTransport.originalSylowAmbient t P : Set G))).subtype) =
                OrderedPairLocalTransport.originalSylowAmbient t P
      simpa only [Subgroup.map_map] using hstationary
    · unfold LocalSylowNormalizerFactorization.localSylowAmbient
        LocalSylowNormalizerFactorization.localSylowInCentralizer
      rw [centralizer_of_original_subtype_image]
      exact hcover

section OriginalOrderedPairData

open CFSG.Open CFSG.Semidihedral

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)

include hGnonab hn f0 ht hs hsC hts hnonab hcentral hnc hp hpodd hf hq hmodel hcov


theorem original_all_stationary_covers_produce_complete_ordered_pair_transport :
    ∀ i : G, i = s ∨ i = t * s →
      ∃ g : G, OrderedPairLocalTransport.OriginalOrderedPairTransport t s i g p f ∧
        allLocalPrimeStationaryCovers i t := by
  let : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  have hcomm : Commute t s := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have hprimes := (all_original_stationary_cover_predicates_equivalent t s).mp hcov
  intro i hi
  obtain ⟨g, hg⟩ := OrderedPairLocalTransport.original_ordered_pair_complete_local_transport
    n hn S0 f0 t s ht hs hcomm hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hprimes i hi
  exact ⟨g, hg, (all_original_stationary_cover_predicates_equivalent i t).mpr
    hg.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem original_all_stationary_covers_produce_both_complete_ordered_pair_transports :
    ∃ gs gts : G,
      OrderedPairLocalTransport.OriginalOrderedPairTransport t s s gs p f ∧
      allLocalPrimeStationaryCovers s t ∧
      OrderedPairLocalTransport.OriginalOrderedPairTransport t s (t * s) gts p f ∧
      allLocalPrimeStationaryCovers (t * s) t := by
  obtain ⟨gs, hgs, hsprime⟩ :=
    original_all_stationary_covers_produce_complete_ordered_pair_transport
      hGnonab n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
      s (Or.inl rfl)
  obtain ⟨gts, hgts, htsprime⟩ :=
    original_all_stationary_covers_produce_complete_ordered_pair_transport
      hGnonab n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
      (t * s) (Or.inr rfl)
  exact ⟨gs, gts, hgs, hsprime, hgts, htsprime⟩

end OriginalOrderedPairData

theorem original_all_stationary_covers_produce_same_parameter_local_data
    [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s) :
    ∀ i : G, i = s ∨ i = t * s → ∃ g : G,
      g ∈ Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G) ∧
      g * t * g⁻¹ = i ∧ g * s * g⁻¹ = t ∧
      orderOf i = 2 ∧ t ∈ C i ∧ i ≠ t ∧
      IsSimpleGroup (CFSG.generalizedFitting (Gamma i)) ∧
      (∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a) ∧
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥ ∧
      (∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic P) ∧
      p.Prime ∧ Odd p ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      (CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
          Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
            CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) ∧
      OrderedPairLocalTransport.OriginalLocalDataTransport (MulAut.conj g) t i ∧
      OrderedPairLocalTransport.OriginalAllPrimeTransport (MulAut.conj g) t s i t ∧
      allLocalPrimeStationaryCovers i t := by
  let : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : Commute t s := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  intro i hi
  obtain ⟨g, hg, hgt, hgs⟩ :=
    OrderedPairLocalTransport.original_ordered_pair_normalizer_conjugator
      n hn S0 f0 t s i ht hs hcomm hts hi
  let e := MulAut.conj g
  have het : e t = i := hgt
  have hes : e s = t := hgs
  let d := PerfectLayerNormalization.originalGeneralizedFittingEquiv e t
  have hsimple : IsSimpleGroup (CFSG.generalizedFitting (Gamma (e t))) :=
    d.symm.isSimpleGroup
  have hnonab' := PerfectLayerNormalization.isomorphism_transports_nonabelian d hnonab
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg (Subgroup.map
      (PerfectLayerNormalization.originalReducedQuotientEquiv e t).toMonoidHom) hcentral
    rw [PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  have hnc' := PerfectLayerNormalization.isomorphism_transports_noncyclic_sylows d 2 hnc
  have hmodel' : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma (e t)) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) := by
    obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨a⟩⟩ := hmodel
    exact ⟨hadm, F, hfield, hfinite, hcard, ⟨d.symm.trans a⟩⟩
  have hlocal := OrderedPairLocalTransport.original_local_data_transport e t
  have hprimes := OrderedPairLocalTransport.original_all_prime_stationary_cover_transport
    e t s ((all_original_stationary_cover_predicates_equivalent t s).mp hcov)
  rw [het] at hsimple hnonab' hcentral' hnc' hmodel' hlocal
  rw [het, hes] at hprimes
  have hiorder : orderOf i = 2 := by
    rw [← het, e.orderOf_eq]
    exact ht
  have hti : t ∈ C i := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg e hcomm.eq
    simpa only [map_mul, het, hes] using h.symm
  have hine : i ≠ t := by
    intro h
    exact hts (e.injective (het.trans (h.trans hes.symm)))
  exact ⟨g, hg, hgt, hgs, hiorder, hti, hine, hsimple, hnonab', hcentral', hnc',
    hp, hpodd, hf, hq, hmodel', hlocal, hprimes.1,
    (all_original_stationary_cover_predicates_equivalent i t).mpr hprimes.2⟩

theorem escaping_local_odd_sylow_fixed_factors_lie_in_original_layer_preimages
    [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH : (localCentralizingLayer t).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ell (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G))
    (hescape : ¬ coveringOddSylowAmbient H W ≤ C t) :
    ∀ i : G, i = s ∨ i = t * s →
      localFixedGroup (coveringOddSylowAmbient H W) i ≤
        (localLayerPreimage i).map (C i).subtype := by
  let : Fact ell.Prime := ⟨hell⟩
  let Wa := coveringOddSylowAmbient H W
  obtain ⟨-, -, hinv, -, -⟩ :=
    escaping_local_odd_sylow_is_normalized_abelian_and_inverted
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape
  have hellodd : Odd ell :=
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))).of_dvd_nat hdiv
  have hWp : IsPGroup ell Wa := W.isPGroup'.map
    (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
  have hWaodd : Odd (Nat.card Wa) :=
    StationaryOddLocalization.odd_card_of_pgroup hell hellodd Wa hWp
  intro i hi
  obtain ⟨g, -, -, -, hiorder, hti, -, hsimple, hnonab', hcentral', hnc',
      hp', hpodd', hf', hq', hmodel', -, -, -⟩ :=
    original_all_stationary_covers_produce_same_parameter_local_data
      hGnonab n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov i hi
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma i)) := hsimple
  have hWiodd : Odd (Nat.card (localFixedGroup Wa i)) :=
    hWaodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact LocalLayerAbelianQuotients.original_odd_inverted_ambient_subgroup_le_layer_preimage
    n hn S0 f0 (Principal.index_ne_two_of_isSimpleGroup hGnonab)
    i hiorder hnonab' hcentral' hnc' p f hp' hpodd' hf' hq' hmodel'
    (localFixedGroup Wa i) inf_le_right hWiodd t hti (fun w hw => hinv w hw.1)

@[expose] def originalIntrinsicInvertedSubgroup (i : G) (U : Subgroup G) :
    Subgroup (N i) :=
  U.comap ((C i).subtype.comp (N i).subtype)

theorem originalIntrinsicInvertedSubgroup_ambient (i : G) (U : Subgroup G)
    (hUN : U ≤ (N i).map (C i).subtype) :
    LocalProjectiveKernelQuotients.originalAmbientInverted i
      (originalIntrinsicInvertedSubgroup i U) = U := by
  change ((U.comap ((C i).subtype.comp (N i).subtype)).map (N i).subtype).map
    (C i).subtype = U
  rw [Subgroup.map_map, Subgroup.map_comap_eq, MonoidHom.range_comp,
    Subgroup.range_subtype, inf_eq_right.mpr hUN]

theorem originalIntrinsicInvertedSubgroup_mem (i t : G) (U : Subgroup G)
    (hU : ∀ x : G, x ∈ U ↔ x ∈ (N i).map (C i).subtype ∧ t * x * t⁻¹ = x⁻¹)
    (x : N i) :
    x ∈ originalIntrinsicInvertedSubgroup i U ↔
      t * ((x : C i) : G) * t⁻¹ = (((x : C i) : G))⁻¹ := by
  change ((x : C i) : G) ∈ U ↔ _
  rw [hU]
  exact and_iff_right (Subgroup.mem_map_of_mem (C i).subtype x.property)

theorem characteristic_comap_of_original_isomorphism {A : Type u} {B : Type v}
    [Group A] [Group B] (e : A ≃* B) (U : Subgroup B) (hU : U.Characteristic) :
    (U.comap e.toMonoidHom).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro a x hx
  have h := (Subgroup.characteristic_iff_le_comap.mp hU)
    ((e.symm.trans a).trans e) hx
  change e (a (e.symm (e x))) ∈ U at h
  change e (a x) ∈ U
  simpa only [MulEquiv.symm_apply_apply] using h

theorem originalIntrinsicInvertedSubgroup_characteristic (i : G) (U : Subgroup G)
    (hU : (U.subgroupOf ((N i).map (C i).subtype)).Characteristic) :
    (originalIntrinsicInvertedSubgroup i U).Characteristic := by
  let e := (N i).equivMapOfInjective (C i).subtype (C i).subtype_injective
  have h := characteristic_comap_of_original_isomorphism e
    (U.subgroupOf ((N i).map (C i).subtype)) hU
  exact h

@[expose] def originalIntrinsicInvertedSubgroupEquiv (i : G) (U : Subgroup G)
    (hUN : U ≤ (N i).map (C i).subtype) :
    originalIntrinsicInvertedSubgroup i U ≃* U :=
  ((originalIntrinsicInvertedSubgroup i U).equivMapOfInjective
    ((C i).subtype.comp (N i).subtype)
    ((C i).subtype_injective.comp (N i).subtype_injective)).trans
      (MulEquiv.subgroupCongr (by
        simpa only [Subgroup.map_map] using
          originalIntrinsicInvertedSubgroup_ambient i U hUN))

theorem originalIntrinsicInvertedSubgroupEquiv_apply (i : G) (U : Subgroup G)
    (hUN : U ≤ (N i).map (C i).subtype) (x : originalIntrinsicInvertedSubgroup i U) :
    (originalIntrinsicInvertedSubgroupEquiv i U hUN x : G) = ((x : N i) : C i) := rfl

theorem originalIntrinsicInvertedSubgroup_card (i : G) (U : Subgroup G)
    (hUN : U ≤ (N i).map (C i).subtype) :
    Nat.card (originalIntrinsicInvertedSubgroup i U) = Nat.card U :=
  Nat.card_congr (originalIntrinsicInvertedSubgroupEquiv i U hUN).toEquiv

theorem originalIntrinsicInvertedSubgroup_index (i : G) (U : Subgroup G) :
    (originalIntrinsicInvertedSubgroup i U).index = U.relIndex ((N i).map (C i).subtype) := by
  rw [originalIntrinsicInvertedSubgroup, Subgroup.index_comap,
    MonoidHom.range_comp, Subgroup.range_subtype]

theorem originalIntrinsicInvertedSubgroup_hall (i : G) (U : Subgroup G)
    (hUN : U ≤ (N i).map (C i).subtype)
    (hHall : Nat.Coprime (Nat.card U) (U.relIndex ((N i).map (C i).subtype))) :
    Nat.Coprime (Nat.card (originalIntrinsicInvertedSubgroup i U))
      (originalIntrinsicInvertedSubgroup i U).index := by
  rw [originalIntrinsicInvertedSubgroup_card i U hUN, originalIntrinsicInvertedSubgroup_index]
  exact hHall

theorem originalIntrinsicInvertedSubgroup_abelian (i : G) (U : Subgroup G)
    (hU : IsMulCommutative U) : IsMulCommutative (originalIntrinsicInvertedSubgroup i U) := by
  let : IsMulCommutative U := hU
  exact U.comap_injective_isMulCommutative
    ((C i).subtype_injective.comp (N i).subtype_injective)

@[expose] def originalIntrinsicFixedSubgroup (i t : G) : Subgroup (N i) :=
  (Subgroup.centralizer ({t} : Set G)).comap ((C i).subtype.comp (N i).subtype)

theorem originalIntrinsicFixedSubgroup_map (i t : G) :
    (originalIntrinsicFixedSubgroup i t).map ((C i).subtype.comp (N i).subtype) =
      (N i).map (C i).subtype ⊓ Subgroup.centralizer ({t} : Set G) := by
  rw [originalIntrinsicFixedSubgroup, Subgroup.map_comap_eq, MonoidHom.range_comp,
    Subgroup.range_subtype]

theorem originalIntrinsicFixedSubgroup_mem (i t : G) (x : N i) :
    x ∈ originalIntrinsicFixedSubgroup i t ↔
      t * ((x : C i) : G) * t⁻¹ = ((x : C i) : G) := by
  change ((x : C i) : G) ∈ Subgroup.centralizer ({t} : Set G) ↔ _
  exact (StationaryOddLocalization.conj_fixed_iff t _).symm

theorem original_intrinsic_inverted_complement_semidirect (i t : G) (U : Subgroup G)
    (hUN : U ≤ (N i).map (C i).subtype)
    (hchar : (U.subgroupOf ((N i).map (C i).subtype)).Characteristic)
    (hgen : U ⊔ ((N i).map (C i).subtype ⊓ Subgroup.centralizer ({t} : Set G)) =
      (N i).map (C i).subtype)
    (hdisj : U ⊓ ((N i).map (C i).subtype ⊓ Subgroup.centralizer ({t} : Set G)) = ⊥) :
    let Ui := originalIntrinsicInvertedSubgroup i U
    let Ai := originalIntrinsicFixedSubgroup i t
    Ui ⊔ Ai = ⊤ ∧ Ui ⊓ Ai = ⊥ ∧ Ui.Normal ∧
    ∃ phi : Ai →* MulAut Ui,
      (∀ a : Ai, ∀ x : Ui,
        ((phi a x : N i) : C i) = (a : N i) * (x : N i) * (a : N i)⁻¹) ∧
      ∃ e : Ui ⋊[phi] Ai ≃* N i,
        (∀ x : Ui ⋊[phi] Ai, e x = (x.left : N i) * x.right) ∧
        (∀ z : N i, ∃ x : Ui, ∃ a : Ai, e ⟨x, a⟩ = z) := by
  let Ui := originalIntrinsicInvertedSubgroup i U
  let Ai := originalIntrinsicFixedSubgroup i t
  let f := (C i).subtype.comp (N i).subtype
  have hf : Function.Injective f := (C i).subtype_injective.comp (N i).subtype_injective
  have hUi : Ui.map f = U := by
    simpa only [Subgroup.map_map] using originalIntrinsicInvertedSubgroup_ambient i U hUN
  have hAi : Ai.map f =
      (N i).map (C i).subtype ⊓ Subgroup.centralizer ({t} : Set G) :=
    originalIntrinsicFixedSubgroup_map i t
  have htop : (⊤ : Subgroup (N i)).map f = (N i).map (C i).subtype := by
    rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
  have hgen' : Ui ⊔ Ai = ⊤ := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_sup, hUi, hAi, htop, hgen]
  have hdisj' : Ui ⊓ Ai = ⊥ := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_inf _ _ _ hf, hUi, hAi, hdisj, Subgroup.map_bot]
  let : Ui.Characteristic := originalIntrinsicInvertedSubgroup_characteristic i U hchar
  have hnormal : Ui.Normal := inferInstance
  let : Ui.Normal := hnormal
  have hnormal' : (Ui.subgroupOf (⊤ : Subgroup (N i))).Normal := inferInstance
  obtain ⟨phi, hphi, e, he, -⟩ :=
    LocalInvertedHallSubgroups.original_normal_complement_literal_semidirect
      (⊤ : Subgroup (N i)) Ui Ai le_top le_top hnormal' hgen' hdisj'
  let e' := e.trans Subgroup.topEquiv
  refine ⟨hgen', hdisj', hnormal, phi, ?_, e', he, ?_⟩
  · intro a x
    exact congrArg (fun z : N i => (z : C i)) (hphi a x)
  · intro z
    exact ⟨(e'.symm z).left, (e'.symm z).right, e'.apply_symm_apply z⟩

@[expose] def OriginalFixedFactorProjectiveData (t i : G) (Wi : Subgroup G) (p f : ℕ) : Prop :=
  ∃ (_ : orderOf i = 2), ∃ (_ : t ∈ C i),
    IsSimpleGroup (CFSG.generalizedFitting (Gamma i)) ∧
    (∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a) ∧
    Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥ ∧
    (∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic P) ∧
    p.Prime ∧ Odd p ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
    (CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) ∧
    allLocalPrimeStationaryCovers i t ∧
    ∃ U : Subgroup G,
      (∀ x : G, x ∈ U ↔ x ∈ (N i).map (C i).subtype ∧ t * x * t⁻¹ = x⁻¹) ∧
      U ≤ (N i).map (C i).subtype ∧ IsMulCommutative U ∧
      let Ui := originalIntrinsicInvertedSubgroup i U
      let Ai := originalIntrinsicFixedSubgroup i t
      (∀ x : N i, x ∈ Ui ↔
        t * ((x : C i) : G) * t⁻¹ = (((x : C i) : G))⁻¹) ∧
      LocalProjectiveKernelQuotients.originalAmbientInverted i Ui = U ∧
      IsMulCommutative Ui ∧ Ui.Characteristic ∧
      Nat.Coprime (Nat.card Ui) Ui.index ∧ Ui ⊔ Ai = ⊤ ∧ Ui ⊓ Ai = ⊥ ∧ Ui.Normal ∧
      (∃ phi : Ai →* MulAut Ui,
        (∀ a : Ai, ∀ x : Ui,
          ((phi a x : N i) : C i) = (a : N i) * (x : N i) * (a : N i)⁻¹) ∧
        ∃ e : Ui ⋊[phi] Ai ≃* N i,
          (∀ x : Ui ⋊[phi] Ai, e x = (x.left : N i) * x.right) ∧
          (∀ z : N i, ∃ x : Ui, ∃ a : Ai, e ⟨x, a⟩ = z)) ∧
      ∃ (hWC : Wi ≤ C i)
        (hWY : Wi ≤ LocalProjectiveKernelQuotients.originalAmbientLayerPreimage i),
        ∃ hnormal : (LocalProjectiveKernelQuotients.originalInvertedKernel i Wi Ui).Normal,
          letI := hnormal
          (∀ w : Wi, LocalProjectiveKernelQuotients.originalProjectiveRestriction i Wi hWC w =
            barKappa i (nu i (Subgroup.inclusion hWC w))) ∧
          (LocalProjectiveKernelQuotients.originalProjectiveRestriction i Wi hWC).ker =
            (N i).comap (Subgroup.inclusion hWC) ∧
          (LocalProjectiveKernelQuotients.originalProjectiveRestriction i Wi hWC).ker.map
            Wi.subtype = Wi ⊓ LocalProjectiveKernelQuotients.originalAmbientOddCore i ∧
          Wi ⊓ LocalProjectiveKernelQuotients.originalAmbientOddCore i =
            Wi ⊓ LocalProjectiveKernelQuotients.originalAmbientInverted i Ui ∧
          (LocalProjectiveKernelQuotients.originalLayerRestriction i Wi hWC hWY).ker =
            (Wi ⊓ LocalProjectiveKernelQuotients.originalAmbientInverted i Ui).comap Wi.subtype ∧
          (∃ q : Wi ⧸ LocalProjectiveKernelQuotients.originalInvertedKernel i Wi Ui →*
              CFSG.generalizedFitting (Gamma i),
            Function.Injective q ∧ ∀ w : Wi, (q (QuotientGroup.mk w) : Gamma i) =
              barKappa i (nu i (Subgroup.inclusion hWC w))) ∧
          (Wi ⊓ LocalProjectiveKernelQuotients.originalAmbientInverted i Ui = ⊥ →
            Function.Injective (LocalProjectiveKernelQuotients.originalLayerRestriction
              i Wi hWC hWY))

section OriginalExactKernels

variable [Finite G] [IsSimpleGroup G]
variable (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH : (localCentralizingLayer t).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ell (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G))
    (hescape : ¬ coveringOddSylowAmbient H W ≤ C t)

include hGnonab hrecognition hn f0 ht hs hsC hts hnonab hcentral hnc
  hp hpodd hf hq hmodel hcov hVH hJH hR hell hdiv hVW hescape

theorem escaping_local_odd_sylow_fixed_factors_have_exact_original_projective_kernels :
    ∀ i : G, i = s ∨ i = t * s →
      ∃ g : G, OrderedPairLocalTransport.OriginalLocalDataTransport (MulAut.conj g) t i ∧
        OrderedPairLocalTransport.OriginalAllPrimeTransport (MulAut.conj g) t s i t ∧
        OriginalFixedFactorProjectiveData t i
          (localFixedGroup (coveringOddSylowAmbient H W) i) p f := by
  let : Fact ell.Prime := ⟨hell⟩
  let Wa := coveringOddSylowAmbient H W
  obtain ⟨-, -, hinv, -, -⟩ :=
    escaping_local_odd_sylow_is_normalized_abelian_and_inverted
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape
  have hellodd : Odd ell :=
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))).of_dvd_nat hdiv
  have hWp : IsPGroup ell Wa := W.isPGroup'.map
    (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
  have hWaodd : Odd (Nat.card Wa) :=
    StationaryOddLocalization.odd_card_of_pgroup hell hellodd Wa hWp
  intro i hi
  obtain ⟨g, -, -, -, hiorder, hti, hine, hsimple, hnonab', hcentral', hnc',
      hp', hpodd', hf', hq', hmodel', hlocal, hprime, hcov'⟩ :=
    original_all_stationary_covers_produce_same_parameter_local_data
      hGnonab n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov i hi
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma i)) := hsimple
  have hprimes := (all_original_stationary_cover_predicates_equivalent i t).mp hcov'
  obtain ⟨-, -, -, -, U, hU, -, -, hUN, hUab, hUchar, hHall, -, hgen, hdisj,
      -, -, -, -, -, -, -, -, -⟩ :=
    LocalInvertedHallSubgroups.original_all_prime_stationary_local_inverted_hall_subgroup
      hGnonab hrecognition n hn S0 f0 i t hiorder ht hti hine hnonab' hcentral' hnc'
      p f hp' hpodd' hf' hq' hmodel' hprimes
  let Ui := originalIntrinsicInvertedSubgroup i U
  have hUi : ∀ x : N i, x ∈ Ui ↔
      t * ((x : C i) : G) * t⁻¹ = (((x : C i) : G))⁻¹ :=
    originalIntrinsicInvertedSubgroup_mem i t U hU
  have hambient := originalIntrinsicInvertedSubgroup_ambient i U hUN
  obtain ⟨hgen', hdisj', hnormal', hsemidirect⟩ :=
    original_intrinsic_inverted_complement_semidirect i t U hUN hUchar hgen hdisj
  let Wi := localFixedGroup Wa i
  have hWC : Wi ≤ C i := inf_le_right
  have hWY : Wi ≤ LocalProjectiveKernelQuotients.originalAmbientLayerPreimage i :=
    escaping_local_odd_sylow_fixed_factors_lie_in_original_layer_preimages
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape i hi
  have hWiodd : Odd (Nat.card Wi) :=
    hWaodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hWiinv : ∀ w : Wi, t * (w : G) * t⁻¹ = (w : G)⁻¹ :=
    fun w => hinv w w.property.1
  let ti : C i := ⟨t, hti⟩
  have hnormal := LocalProjectiveKernelQuotients.originalInvertedKernel_normal
    i hiorder ti Wi hWC hWiodd Ui hUi hWiinv
  let := hnormal
  have htoolkit := LocalProjectiveKernelQuotients.original_local_projective_kernel_quotient_toolkit
    i hiorder ti Wi hWC hWiodd Ui hUi hWiinv hWY
  refine ⟨g, hlocal, hprime, hiorder, hti, hsimple, hnonab', hcentral', hnc',
    hp', hpodd', hf', hq', hmodel', hcov', U, hU, hUN, hUab, hUi, hambient,
    originalIntrinsicInvertedSubgroup_abelian i U hUab,
    originalIntrinsicInvertedSubgroup_characteristic i U hUchar,
    originalIntrinsicInvertedSubgroup_hall i U hUN hHall,
    hgen', hdisj', hnormal', hsemidirect, hWC, hWY, hnormal, ?_⟩
  exact ⟨htoolkit.1, htoolkit.2.1, htoolkit.2.2.1, htoolkit.2.2.2.1,
    htoolkit.2.2.2.2.1, htoolkit.2.2.2.2.2,
    LocalProjectiveKernelQuotients.originalLayerRestriction_injective_of_inter_eq_bot
      i hiorder ti Wi hWC hWiodd Ui hUi hWiinv hWY⟩

theorem escaping_local_odd_sylow_eigensubgroups_have_exact_projective_kernels :
    let Wa := coveringOddSylowAmbient H W
    ((localCentralizingLayer t).map (C t).subtype ≤ Subgroup.normalizer (Wa : Set G) ∧
      IsMulCommutative Wa ∧ (∀ w ∈ Wa, t * w * t⁻¹ = w⁻¹) ∧
      Wa ⊓ C t = ⊥ ∧ Wa ≠ ⊥ ∧
      ∃ d : G, d ∈ (localCentralizingLayer t).map (C t).subtype ∧
        orderOf d = 4 ∧ d ^ 2 = t ∧ d * s * d⁻¹ = t * s ∧
        d ∈ Subgroup.normalizer (Wa : Set G) ∧
        (localFixedGroup Wa s).map (MulAut.conj d).toMonoidHom = localFixedGroup Wa (t * s) ∧
        localFixedGroup Wa s ≠ ⊥ ∧ localFixedGroup Wa (t * s) ≠ ⊥ ∧
        Nat.card (localFixedGroup Wa s) = Nat.card (localFixedGroup Wa (t * s)) ∧
        Disjoint (localFixedGroup Wa s) (localFixedGroup Wa (t * s)) ∧
        localFixedGroup Wa s ⊔ localFixedGroup Wa (t * s) = Wa ∧
        ∃ e : localFixedGroup Wa s × localFixedGroup Wa (t * s) ≃* Wa,
          ∀ x, (e x : G) = (x.1 : G) * (x.2 : G)) ∧
    ∀ i : G, i = s ∨ i = t * s →
      ∃ g : G, OrderedPairLocalTransport.OriginalLocalDataTransport (MulAut.conj g) t i ∧
        OrderedPairLocalTransport.OriginalAllPrimeTransport (MulAut.conj g) t s i t ∧
        OriginalFixedFactorProjectiveData t i (localFixedGroup Wa i) p f := by
  exact ⟨escaping_local_odd_sylow_has_original_exchanged_fixed_eigensubgroups
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape,
    escaping_local_odd_sylow_fixed_factors_have_exact_original_projective_kernels
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape⟩

end OriginalExactKernels


section OriginalCompatibleCover

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions
open scoped commutatorElement

theorem original_local_compatible_SL2_cover
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F))
      (rho : Gamma t →* coordinateE F),
      Nat.card F = p ^ f ∧ Function.Injective rho ∧
      (CFSG.generalizedFitting (Gamma t)).map rho = specialLayer F ∧
      rho.range = OddFieldLift.Gamma F A ∧
      ∃ eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F,
        (∀ (z : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)),
          (z : H t) = nu t (tInC t) → eta z = OddFieldSL2.minusIdentity F) ∧
        (∀ x : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
          (rho (barKappa t x)).val =
            coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x))) := by
  obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S0' : Sylow 2 G' := S0.mapSurjective (f := e.toMonoidHom) e.surjective
  let f0' : SemidihedralGroup n ≃* S0' :=
    f0.trans ((S0 : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective)
  let d := PerfectLayerNormalization.originalGeneralizedFittingEquiv e t
  let a := PerfectLayerNormalization.originalReducedQuotientEquiv e t
  let b := PerfectLayerNormalization.originalOddQuotientEquiv e t
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma (e t))) := d.symm.isSimpleGroup
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg (Subgroup.map a.toMonoidHom) hcentral
    rw [PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  obtain ⟨F, hfield, hfiniteF, A, rho', data⟩ := actual_simple_layer_matrix_data
    n hn S0' f0' (PerfectLayerNormalization.isomorphism_transports_no_index_two e hG)
    (e t) ((e.orderOf_eq t).trans ht)
    (PerfectLayerNormalization.isomorphism_transports_nonabelian d hnonab) hcentral'
    (PerfectLayerNormalization.isomorphism_transports_noncyclic_sylows d 2 hnc)
    p f hp hpodd hf (PerfectLayerNormalization.original_psl_two_model_transport d p f hmodel)
  let : Field F := hfield
  let : Finite F := hfiniteF
  let rho := rho'.comp a.toMonoidHom
  obtain ⟨eta', hetaz, heta, -⟩ := data.compatible_layer
  have hT : ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).map b.toMonoidHom =
      (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t)) :=
    (PerfectLayerNormalization.original_local_layer_preimages_transport e t).1
  let c : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t)) :=
    (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).equivMapOfInjective
      b.toMonoidHom b.injective).trans (MulEquiv.subgroupCongr hT)
  let eta := c.trans eta'
  refine ⟨F, hfield, hfiniteF, A, rho, data.field_card,
    data.faithful.comp a.injective, ?_, ?_, eta, ?_, ?_⟩
  · change (CFSG.generalizedFitting (Gamma t)).map (rho'.comp a.toMonoidHom) = _
    rw [← Subgroup.map_map,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting]
    exact data.layer_image
  · change (rho'.comp a.toMonoidHom).range = _
    have ha : a.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr a.surjective
    rw [MonoidHom.range_comp, ha, ← MonoidHom.range_eq_map]
    exact data.full_image
  · intro z hz
    have hc : (c z : H (e t)) = nu (e t) (tInC (e t)) := by
      change b (z : H t) = _
      rw [hz]
      rw [PerfectLayerNormalization.originalOddQuotientEquiv_nu,
        PerfectLayerNormalization.originalCentralizerEquiv_tInC]
    have he : c z = ⟨nu (e t) (tInC (e t)),
        QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
          (nu (e t) (tInC (e t))) (barKappa (e t)) (barKappa_kernel (e t))
          (CFSG.generalizedFitting (Gamma (e t)))⟩ := Subtype.ext hc
    change eta' (c z) = _
    rw [he, hetaz]
    rfl
  · intro x
    have hb : a (barKappa t (x : H t)) = barKappa (e t) (c x : H (e t)) := by
      exact PerfectLayerNormalization.original_quotient_maps_commute e t x
    change (rho' (a (barKappa t x))).val = _
    rw [hb]
    exact heta (c x)

theorem original_odd_core_centrality_controls_subgroup_commutators
    {G : Type u} [Group G] [Finite G] (A K0 : Subgroup G) (hKA : K0 ≤ A)
    (i : G) (hiK : i ∈ K0)
    (hcentral : QuotientGroup.mk' (CFSG.pPrimeCore 2 A) (⟨i, hKA hiK⟩ : A) ∈
      Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A)) :
    ⁅K0, Subgroup.zpowers i⁆ ≤ (CFSG.pPrimeCore 2 K0).map K0.subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let incl := Subgroup.inclusion hKA
  let R0 := (CFSG.pPrimeCore 2 A).comap incl
  have hRodd : Odd (Nat.card R0) :=
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := A))).of_dvd_nat
      ((CFSG.pPrimeCore 2 A).card_comap_dvd_of_injective incl
        (Subgroup.inclusion_injective hKA))
  have hRcore : R0 ≤ CFSG.pPrimeCore 2 K0 :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hRodd⟩
  let q := (QuotientGroup.mk' (CFSG.pPrimeCore 2 A)).comp incl
  let ik : K0 := ⟨i, hiK⟩
  have hqi : q ik ∈ Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A) := hcentral
  have hcomm : ⁅(⊤ : Subgroup K0), Subgroup.zpowers ik⁆ ≤ R0 := by
    apply Subgroup.commutator_le.mpr
    intro x _ y hy
    have hqy : q y ∈ Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A) := by
      have hmap : (Subgroup.zpowers ik).map q = Subgroup.zpowers (q ik) :=
        MonoidHom.map_zpowers q ik
      exact Subgroup.zpowers_le.mpr hqi
        (hmap ▸ Subgroup.mem_map_of_mem q hy)
    change incl ⁅x, y⁆ ∈ CFSG.pPrimeCore 2 A
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    exact (show Commute (q x) (q y) from
      Subgroup.mem_center_iff.mp hqy (q x)).commutator_eq
  have hmap := Subgroup.map_mono (f := K0.subtype) (hcomm.trans hRcore)
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
    MonoidHom.map_zpowers] at hmap
  exact hmap

theorem original_all_stationary_covers_produce_actual_central_SL2_projection
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (s : G) (hq : 5 ≤ p ^ f) (hcov : allLocalPrimeStationaryCovers t s) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ∃ eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F,
        ∃ _ : Group.IsPerfect (localCentralizingLayer t),
          ∃ htJ : tInC t ∈ localCentralizingLayer t,
            ∃ beta : localCentralizingLayer t →* Matrix.SpecialLinearGroup (Fin 2) F,
              Function.Surjective beta ∧
              beta.ker = ((localCentralizingLayer t) ⊓ N t).subgroupOf
                (localCentralizingLayer t) ∧
              beta.ker ≤ Subgroup.center (localCentralizingLayer t) ∧
              Odd (Nat.card beta.ker) ∧
              beta ⟨tInC t, htJ⟩ = OddFieldSL2.minusIdentity F ∧
              (⟨tInC t, htJ⟩ : localCentralizingLayer t) ∈
                Subgroup.center (localCentralizingLayer t) ∧
              orderOf (⟨tInC t, htJ⟩ : localCentralizingLayer t) = 2 ∧
              (∀ j : localCentralizingLayer t,
                ∃ x : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
                  (x : H t) = nu t j ∧ beta j = eta x) := by
  obtain ⟨F, hfield, hfinite, A, rho, hcard, -, -, -, eta, hetaz, -⟩ :=
    original_local_compatible_SL2_cover n hn S0 f0 hG t ht
      hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  obtain ⟨hJ, -, htJ, himage, -, -, hker, hcentralE, hoddE⟩ :=
    PerfectLayerNormalization.original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
      (all_stationary_covers_give_original_layer_coverage t s hcov)
  let Jc := localCentralizingLayer t
  change Group.IsPerfect Jc at hJ
  change tInC t ∈ Jc at htJ
  change Jc.map (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) at himage
  let T0 := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  change Jc.map (nu t) = T0 at himage
  let q := (nu t).comp Jc.subtype
  have hqmem (j : Jc) : q j ∈ T0 := by
    change nu t (j : C t) ∈ T0
    rw [← himage]
    exact Subgroup.mem_map_of_mem (nu t) j.property
  let q0 := q.codRestrict T0 hqmem
  have hqsurj : Function.Surjective q0 := by
    intro x
    have hx : (x : H t) ∈ Jc.map (nu t) := by
      rw [himage]
      exact x.property
    obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨j, hj⟩, Subtype.ext ?_⟩
    exact hjx
  let beta := eta.toMonoidHom.comp q0
  have hbetaker : beta.ker = (Jc ⊓ N t).subgroupOf Jc := by
    change (eta.toMonoidHom.comp q0).ker = _
    rw [show (eta.toMonoidHom.comp q0).ker = q0.ker from
      MonoidHom.ker_mulEquiv_comp q0 eta]
    change (q.codRestrict T0 hqmem).ker = _
    rw [MonoidHom.ker_codRestrict]
    exact hker
  have hodd : Odd (Nat.card beta.ker) := by
    rw [hbetaker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Jc ⊓ N t ≤ Jc from inf_le_left)).toEquiv]
    exact hoddE
  have htcenter : (⟨tInC t, htJ⟩ : Jc) ∈ Subgroup.center Jc := by
    apply Subgroup.mem_center_iff.mpr
    intro j
    exact Subtype.ext (Subgroup.mem_center_iff.mp (tInC_central t) j)
  have htorder : orderOf (⟨tInC t, htJ⟩ : Jc) = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact ht
  refine ⟨F, hfield, hfinite, hcard, eta, hJ, htJ, beta,
    eta.surjective.comp hqsurj, hbetaker, hbetaker ▸ hcentralE, hodd,
    hetaz (q0 ⟨tInC t, htJ⟩) rfl, htcenter, htorder, ?_⟩
  intro j
  exact ⟨q0 j, rfl, rfl⟩


theorem original_compatible_cover_induces_scalar_projective_equivalence
    {G : Type u} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    (F : Type v) [Field F]
    (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
    (hetaz : ∀ z : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
      (z : H t) = nu t (tInC t) → eta z = OddFieldSL2.minusIdentity F) :
    ∃ e : CFSG.generalizedFitting (Gamma t) ≃* OddProjectiveCoverKernel.S F,
      ∀ x : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
        e (QuaternionDoubleCoverUniqueness.preimageProjection (barKappa t)
          (CFSG.generalizedFitting (Gamma t)) x) =
        ProjectiveSL2Cover.scalarQuotient F 2 (eta x) := by
  let L := CFSG.generalizedFitting (Gamma t)
  let T0 := L.comap (barKappa t)
  let pi := QuaternionDoubleCoverUniqueness.preimageProjection (barKappa t) L
  have hpi : Function.Surjective pi :=
    QuaternionDoubleCoverUniqueness.preimageProjection_surjective
      (barKappa t) (barKappa_surjective t) L
  let z : T0 := ⟨nu t (tInC t),
    QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
      (nu t (tInC t)) (barKappa t) (barKappa_kernel t) L⟩
  have hz : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (FullRootSylowCentralizers.original_odd_quotient_involution t ht).2.1
  have hker : pi.ker = Subgroup.zpowers z := by
    ext x
    change (pi x = 1) ↔ x ∈ Subgroup.zpowers z
    rw [← Subtype.val_inj]
    change (barKappa t (x : H t) = 1) ↔ x ∈ Subgroup.zpowers z
    rw [← MonoidHom.mem_ker, barKappa_kernel,
      KleinFourOddKernel.mem_zpowers_involution (nu t (tInC t)) (x : H t)
        ((FullRootSylowCentralizers.original_odd_quotient_involution t ht).2.1),
      KleinFourOddKernel.mem_zpowers_involution z x hz]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have hez : eta z = ProjectiveSL2Cover.minusIdentity F :=
    (hetaz z rfl).trans (ProjectiveSL2Cover.minusIdentity_eq_neg_one F).symm
  have hmap : pi.ker.map eta.toMonoidHom = ProjectiveSL2Cover.nativeScalarKernel F 2 := by
    rw [hker, MonoidHom.map_zpowers]
    change Subgroup.zpowers (eta z) = _
    rw [hez, ProjectiveSL2Cover.nativeScalarKernel_two_eq_zpowers]
  let c := QuotientGroup.congr pi.ker (ProjectiveSL2Cover.nativeScalarKernel F 2) eta hmap
  let a := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  let e := a.symm.trans c
  refine ⟨e, ?_⟩
  intro x
  have ha : a (QuotientGroup.mk x) = pi x := rfl
  change c (a.symm (pi x)) = _
  rw [← ha, a.symm_apply_apply]
  exact QuotientGroup.congr_mk _ _ eta hmap x


end OriginalCompatibleCover

open CFSG.Semidihedral.ExchangedEigensubgroups

theorem original_same_field_projective_injection_forces_defining_square_orders
    {G : Type u} [Group G] [Finite G]
    (t i : G) (hi : orderOf i = 2) (W : Subgroup G) [IsMulCommutative W]
    (hW : W ≠ ⊥) (Jc : Subgroup (C t)) [Group.IsPerfect Jc]
    (htJ : tInC t ∈ Jc)
    (hJW : Jc.map (C t).subtype ≤ Subgroup.normalizer (W : Set G))
    (hiW : i ∈ Subgroup.normalizer (W : Set G))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)
    (d : G) (hdJ : d ∈ Jc.map (C t).subtype)
    (hexchange : d * i * d⁻¹ = t * i)
    {F : Type v} [Field F] {p ell f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hell : ell.Prime) (hellodd : Odd ell)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : 5 < p ^ f)
    (beta : Jc →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hbeta : Function.Surjective beta) (hcentral : beta.ker ≤ Subgroup.center Jc)
    (hodd : Odd (Nat.card beta.ker))
    (htbeta : beta ⟨tInC t, htJ⟩ = OddFieldSL2.minusIdentity F)
    (htcenter : (⟨tInC t, htJ⟩ : Jc) ∈ Subgroup.center Jc)
    (htorder : orderOf (⟨tInC t, htJ⟩ : Jc) = 2)
    (hWp : IsPGroup ell W)
    (hWC : localFixedGroup W i ≤ C i)
    (hWY : localFixedGroup W i ≤ LocalProjectiveKernelQuotients.originalAmbientLayerPreimage i)
    (eL : CFSG.generalizedFitting (Gamma i) ≃* OddProjectiveCoverKernel.S F)
    (hinj : Function.Injective (LocalProjectiveKernelQuotients.originalLayerRestriction
      i (localFixedGroup W i) hWC hWY)) :
    ell = p ∧ CFSG.IsElementaryAbelian p W ∧ Nat.card W = (p ^ f) ^ 2 ∧
      CFSG.IsElementaryAbelian p (localFixedGroup W i) ∧
      Nat.card (localFixedGroup W i) = p ^ f := by
  let : Fact p.Prime := ⟨hp⟩
  let : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW
  let norm := Subgroup.normalizer (W : Set G)
  let fJ : Jc →* norm := ((C t).subtype.comp Jc.subtype).codRestrict norm
    (fun j => hJW (Subgroup.mem_map_of_mem (C t).subtype j.property))
  let rho := W.normalizerMonoidHom.comp fJ
  let tj : Jc := ⟨tInC t, htJ⟩
  have htW : t ∈ norm := hJW (Subgroup.mem_map_of_mem (C t).subtype htJ)
  let tn : norm := ⟨t, htW⟩
  let inn : norm := ⟨i, hiW⟩
  let alpha := W.normalizerMonoidHom inn
  have halpha : alpha ^ 2 = 1 := original_involution_normalizer_action_square W i hi hiW
  obtain ⟨dc, hdc, hdval⟩ := Subgroup.mem_map.mp hdJ
  let dj : Jc := ⟨dc, hdc⟩
  have hdW : d ∈ norm := hJW hdJ
  let dn : norm := ⟨d, hdW⟩
  have hdmap : fJ dj = dn := Subtype.ext hdval
  have htmap : fJ tj = tn := rfl
  have hrel : dn * inn * dn⁻¹ = tn * inn := Subtype.ext hexchange
  have hrho : rho dj * alpha * (rho dj)⁻¹ = rho tj * alpha := by
    change W.normalizerMonoidHom (fJ dj) * alpha *
      (W.normalizerMonoidHom (fJ dj))⁻¹ = W.normalizerMonoidHom (fJ tj) * alpha
    rw [hdmap, htmap]
    simpa only [map_mul, map_inv] using congrArg W.normalizerMonoidHom hrel
  have htinversion : ∀ w : W, rho tj w = w⁻¹ := by
    intro w
    apply Subtype.ext
    exact hinv w w.property
  let ep := originalFixedEigenEquiv W i hiW
  let pi := LocalProjectiveKernelQuotients.originalLayerRestriction
    i (localFixedGroup W i) hWC hWY
  let inj := eL.toMonoidHom.comp (pi.comp ep.toMonoidHom)
  have hinjinj : Function.Injective inj := eL.injective.comp (hinj.comp ep.injective)
  obtain ⟨hchar, -, hplus, -, -, hwhole, hpluscard, -, hwholecard, -⟩ :=
    exchanged_eigensubgroups_projective_embedding_forces_defining_square_order
      hp hpodd hell hellodd hf hF hq beta hbeta hcentral hodd
      tj htcenter htorder htbeta rho htinversion hWp alpha halpha dj hrho inj hinjinj
  let : CFSG.IsElementaryAbelian p (ExchangedEigensubgroups.positiveGroup alpha) := hplus
  have hplusimage := CFSG.IsElementaryAbelian.map_subtype
    (p := p) (G := G) (K := W) (H := ExchangedEigensubgroups.positiveGroup alpha)
  have himage : (ExchangedEigensubgroups.positiveGroup alpha).map W.subtype =
      localFixedGroup W i := positive_eigensubgroup_ambient_image W i hiW
  refine ⟨hchar, hwhole, hwholecard, himage ▸ hplusimage, ?_⟩
  exact (Nat.card_congr ep.toEquiv).symm.trans hpluscard

theorem original_local_data_transport_preserves_same_field_scalar_models
    {G : Type u} [Group G] [Finite G] (t i : G) (ht : orderOf t = 2)
    (e : G ≃* G) (hlocal : OrderedPairLocalTransport.OriginalLocalDataTransport e t i)
    {F : Type v} [Field F]
    (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
    (hetaz : ∀ z : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
      (z : ActualSimpleLayerLocalPackage.H t) = nu t (tInC t) →
        eta z = OddFieldSL2.minusIdentity F) :
    ∃ etai : (CFSG.generalizedFitting (Gamma i)).comap (barKappa i) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ ei : CFSG.generalizedFitting (Gamma i) ≃* OddProjectiveCoverKernel.S F,
        (∀ x : (CFSG.generalizedFitting (Gamma i)).comap (barKappa i),
          ei (QuaternionDoubleCoverUniqueness.preimageProjection (barKappa i)
            (CFSG.generalizedFitting (Gamma i)) x) =
            ProjectiveSL2Cover.scalarQuotient F 2 (etai x)) ∧
        (∀ z : (CFSG.generalizedFitting (Gamma i)).comap (barKappa i),
          (z : H i) = nu i (tInC i) → etai z = OddFieldSL2.minusIdentity F) := by
  obtain ⟨-, c, a, b, d, l, hc, hct, ha, hb, hd, hbk, hl,
    hN, hNZ, hL, hT, hY, hJ, hE, hNa, hYa, hJa, hcard⟩ := hlocal
  let Tt := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  let Ti := (CFSG.generalizedFitting (Gamma i)).comap (barKappa i)
  let tr : Tt ≃* Ti := (Tt.equivMapOfInjective b.toMonoidHom b.injective).trans
    (MulEquiv.subgroupCongr hT)
  have htr (x : Tt) : (tr x : H i) = b (x : H t) := by
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  obtain ⟨et, het⟩ := original_compatible_cover_induces_scalar_projective_equivalence
    t ht F eta hetaz
  let etai := tr.symm.trans eta
  let ei := l.symm.trans et
  refine ⟨etai, ei, ?_, ?_⟩
  · intro x
    let y : Tt := tr.symm x
    have hy : b (y : H t) = (x : H i) := by
      rw [← htr y]
      exact congrArg Subtype.val (tr.apply_symm_apply x)
    have hproj : l (QuaternionDoubleCoverUniqueness.preimageProjection (barKappa t)
        (CFSG.generalizedFitting (Gamma t)) y) =
        QuaternionDoubleCoverUniqueness.preimageProjection (barKappa i)
          (CFSG.generalizedFitting (Gamma i)) x := by
      apply Subtype.ext
      rw [hl]
      change d (barKappa t (y : H t)) = barKappa i (x : H i)
      rw [hbk, hy]
    change et (l.symm (QuaternionDoubleCoverUniqueness.preimageProjection (barKappa i)
      (CFSG.generalizedFitting (Gamma i)) x)) = ProjectiveSL2Cover.scalarQuotient F 2 (eta y)
    rw [← hproj, l.symm_apply_apply]
    exact het y
  · intro z hz
    let y : Tt := tr.symm z
    have hy : b (y : H t) = (z : H i) := by
      rw [← htr y]
      exact congrArg Subtype.val (tr.apply_symm_apply z)
    have hzt : (y : H t) = nu t (tInC t) := by
      apply b.injective
      rw [hy, hz, hb, hct]
    exact hetaz y hzt



section OriginalTrivialFactor

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
variable (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH : (localCentralizingLayer t).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ell (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G))
    (hescape : ¬ coveringOddSylowAmbient H W ≤ C t)

include hGnonab hrecognition hn f0 ht hs hsC hts hnonab hcentral hnc
  hp hpodd hf hq hmodel hcov hVH hJH hR hell hdiv hVW hescape

theorem original_escaping_trivial_odd_intersection_forces_defining_square_orders
    (i : G) (hi : i = s ∨ i = t * s)
    (hinter : localFixedGroup (coveringOddSylowAmbient H W) i ⊓
      LocalProjectiveKernelQuotients.originalAmbientOddCore i = ⊥) :
    let Wa := coveringOddSylowAmbient H W
    ell = p ∧ CFSG.IsElementaryAbelian p Wa ∧ Nat.card Wa = (p ^ f) ^ 2 ∧
      CFSG.IsElementaryAbelian p (localFixedGroup Wa i) ∧
      Nat.card (localFixedGroup Wa i) = p ^ f := by
  let Wa := coveringOddSylowAmbient H W
  obtain ⟨hJW, hab, hinv, -, hW, d, hdJ, hdorder, hdsq, hds, -, -⟩ :=
    escaping_local_odd_sylow_has_original_exchanged_fixed_eigensubgroups
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf (Nat.le_of_lt hq) hmodel hcov H hVH hJH hR hell hdiv W hVW hescape
  let : IsMulCommutative Wa := hab
  obtain ⟨g, hgV, hgt, hgs, hiorder, hti, hit, hsimple, hnonabi, hcentrali,
    hnci, -, -, -, -, hmodeli, hlocal, hprimes, hcovi⟩ :=
    original_all_stationary_covers_produce_same_parameter_local_data
      hGnonab n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf (Nat.le_of_lt hq) hmodel hcov i hi
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma i)) := hsimple
  let Wi := localFixedGroup Wa i
  have hWC : Wi ≤ C i := inf_le_right
  have hWY : Wi ≤ LocalProjectiveKernelQuotients.originalAmbientLayerPreimage i :=
    escaping_local_odd_sylow_fixed_factors_lie_in_original_layer_preimages
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf (Nat.le_of_lt hq) hmodel hcov H hVH hJH hR hell hdiv W hVW hescape i hi
  have hWiN : (N i).comap (Subgroup.inclusion hWC) = ⊥ := by
    apply le_antisymm _ bot_le
    intro w hw
    have hwN : (w : G) ∈ LocalProjectiveKernelQuotients.originalAmbientOddCore i :=
      ⟨Subgroup.inclusion hWC w, hw, rfl⟩
    have hwbot : (w : G) ∈ (⊥ : Subgroup G) := hinter ▸ ⟨w.property, hwN⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hwbot)
  have hWiodd : Odd (Nat.card Wi) :=
    (StationaryOddLocalization.odd_card_of_pgroup hell
      ((Nat.coprime_two_left.mp
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))).of_dvd_nat hdiv)
      Wa (W.isPGroup'.map (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype))).of_dvd_nat
        (Subgroup.card_dvd_of_le (show Wi ≤ Wa from inf_le_left))
  have hpiinj : Function.Injective
      (LocalProjectiveKernelQuotients.originalLayerRestriction i Wi hWC hWY) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [LocalProjectiveKernelQuotients.originalLayerRestriction_ker,
      LocalProjectiveKernelQuotients.originalProjectiveRestriction_ker i hiorder Wi hWC hWiodd,
      hWiN]
  obtain ⟨F, hfield, hfinite, hcard, eta, hJperfect, htJ, beta,
    hbetasurj, hbetaker, hbetacentral, hbetaodd, htminus, htcenter, htorder, hrep⟩ :=
    original_all_stationary_covers_produce_actual_central_SL2_projection
      n hn S0 f0 (PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab)
      t ht hnonab hcentral hnc p f hp hpodd hf hmodel s (Nat.le_of_lt hq) hcov
  let : Field F := hfield
  let : Finite F := hfinite
  let : Group.IsPerfect (localCentralizingLayer t) := hJperfect
  have hetaz : ∀ z : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
      (z : ActualSimpleLayerLocalPackage.H t) = nu t (tInC t) →
      eta z = OddFieldSL2.minusIdentity F := by
    intro z hz
    obtain ⟨x, hx, hbeta⟩ := hrep ⟨tInC t, htJ⟩
    have hxz : x = z := Subtype.ext (hx.trans hz.symm)
    rw [← hxz, ← hbeta]
    exact htminus
  obtain ⟨etai, ei, hei, hetazi⟩ := original_local_data_transport_preserves_same_field_scalar_models
    t i ht (MulAut.conj g) hlocal eta hetaz
  have hiW : i ∈ Subgroup.normalizer (Wa : Set G) := by
    rcases hi with rfl | rfl
    · exact hVW (Subgroup.subset_closure (by simp))
    · exact hVW ((Subgroup.closure ({t, s} : Set G)).mul_mem
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  have hdt : Commute d t := Subgroup.mem_centralizer_singleton_iff.mp
    (Subgroup.map_subtype_le _ hdJ)
  have hdti : d * i * d⁻¹ = t * i := by
    rcases hi with rfl | rfl
    · exact hds
    · calc
        d * (t * s) * d⁻¹ = (d * t * d⁻¹) * (d * s * d⁻¹) := by group
        _ = t * (t * s) := by rw [hdt.mul_inv_cancel, hds]
  exact original_same_field_projective_injection_forces_defining_square_orders
    t i hiorder Wa hW (localCentralizingLayer t) htJ hJW hiW hinv d hdJ hdti
    hp hpodd hell
    ((Nat.coprime_two_left.mp
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))).of_dvd_nat hdiv)
    hf hcard hq beta hbetasurj hbetacentral hbetaodd htminus htcenter htorder
    (W.isPGroup'.map (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)) hWC hWY ei hpiinj

end OriginalTrivialFactor



open CFSG.Semidihedral.LocalInvertedLiftContainment
open CFSG.Semidihedral.NontrivialInvertedIntersectionCentrality
open scoped commutatorElement Pointwise

theorem original_eigen_pair_normalizes_fixed_group
    {G : Type u} [Group G] (t i : G) (W : Subgroup G)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hiW : i ∈ Subgroup.normalizer (W : Set G)) (hti : t ∈ C i) :
    Subgroup.closure ({i, t} : Set G) ≤
      Subgroup.normalizer (localFixedGroup W i : Set G) := by
  let V := Subgroup.closure ({i, t} : Set G)
  have hVW : V ≤ Subgroup.normalizer (W : Set G) := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hiW
    · exact (Set.mem_singleton_iff.mp hx) ▸ htW
  have hVC : V ≤ C i := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact (Set.mem_singleton_iff.mp hx) ▸ hti
  exact (le_inf hVW (hVC.trans (C i).le_normalizer)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem original_ambient_inversion_identifies_odd_intersection
    {G : Type u} [Group G] (t i : G) (W U : Subgroup G)
    (hU : ∀ x : G, x ∈ U ↔ x ∈ (N i).map (C i).subtype ∧ t * x * t⁻¹ = x⁻¹)
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) :
    W ⊓ (N i).map (C i).subtype = W ⊓ U := by
  ext w
  constructor
  · intro hw
    exact ⟨hw.1, (hU w).mpr ⟨hw.2, hinv w hw.1⟩⟩
  · intro hw
    exact ⟨hw.1, ((hU w).mp hw.2).1⟩

section OriginalNontrivialFactor


variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
variable (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH : (localCentralizingLayer t).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ell (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G))
    (hescape : ¬ coveringOddSylowAmbient H W ≤ C t)

include hGnonab hrecognition hn f0 ht hs hsC hts hnonab hcentral hnc
  hp hpodd hf hq hmodel hcov hVH hJH hR hell hdiv hVW hescape


theorem original_escaping_fixed_factors_lie_in_actual_lift_and_hall
    (i : G) (hi : i = s ∨ i = t * s) :
    let Wi := localFixedGroup (coveringOddSylowAmbient H W) i
    OriginalCentralizingLiftFacts i ∧
      ∃ U : Subgroup G, OriginalInvertedHallFacts i t U ∧
        ∃ hti : t ∈ C i, OriginalLiftHallQuotientFacts i t hti U ∧
          ∃ hWC : Wi ≤ C i, OriginalInvertedSubgroupConclusion i U Wi hWC ∧
            Wi ⊓ LocalProjectiveKernelQuotients.originalAmbientOddCore i = Wi ⊓ U ∧
            (Wi ⊓ U ≠ ⊥ →
              ⁅Subgroup.centralizer (Wi : Set G), Subgroup.zpowers i⁆ ≤
                (CFSG.pPrimeCore 2 (Subgroup.centralizer (Wi : Set G))).map
                  (Subgroup.centralizer (Wi : Set G)).subtype) := by
  let Wa := coveringOddSylowAmbient H W
  let Wi := localFixedGroup Wa i
  obtain ⟨-, hab, hinv, -, -⟩ :=
    escaping_local_odd_sylow_is_normalized_abelian_and_inverted
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf (Nat.le_of_lt hq) hmodel hcov H hVH hJH hR hell hdiv W hVW hescape
  obtain ⟨g, hgV, hgt, hgs, hiorder, hti, hit, hsimple, hnonabi, hcentrali,
    hnci, -, -, -, -, hmodeli, hlocal, hprimes, hcovi⟩ :=
    original_all_stationary_covers_produce_same_parameter_local_data
      hGnonab n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf (Nat.le_of_lt hq) hmodel hcov i hi
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma i)) := hsimple
  have hWC : Wi ≤ C i := inf_le_right
  have hWY : Wi ≤ LocalProjectiveKernelQuotients.originalAmbientLayerPreimage i :=
    escaping_local_odd_sylow_fixed_factors_lie_in_original_layer_preimages
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf (Nat.le_of_lt hq) hmodel hcov H hVH hJH hR hell hdiv W hVW hescape i hi
  have hWaodd : Odd (Nat.card Wa) :=
    StationaryOddLocalization.odd_card_of_pgroup hell
      ((Nat.coprime_two_left.mp
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))).of_dvd_nat hdiv)
      Wa (W.isPGroup'.map (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype))
  have hWiodd : Odd (Nat.card Wi) := hWaodd.of_dvd_nat
    (Subgroup.card_dvd_of_le (show Wi ≤ Wa from inf_le_left))
  have hWiinv : ∀ w ∈ Wi, t * w * t⁻¹ = w⁻¹ := fun w hw => hinv w hw.1
  have htWa : t ∈ Subgroup.normalizer (Wa : Set G) :=
    hVW (Subgroup.subset_closure (by simp))
  have hiWa : i ∈ Subgroup.normalizer (Wa : Set G) := by
    rcases hi with rfl | rfl
    · exact hVW (Subgroup.subset_closure (by simp))
    · exact hVW ((Subgroup.closure ({t, s} : Set G)).mul_mem
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  have hVWi := original_eigen_pair_normalizes_fixed_group t i Wa htWa hiWa hti
  obtain ⟨hLift, U, hHall, hQuotient, hconfine⟩ :=
    original_all_prime_stationary_nontrivial_inverted_intersection_centrality
      hGnonab hrecognition n hn S0 f0 i t hiorder ht hti hit
      hnonabi hcentrali hnci p f hp hpodd hf (Nat.le_of_lt hq) hmodeli
      ((all_original_stationary_cover_predicates_equivalent i t).mp hcovi)
  obtain ⟨hContain, hNontrivial⟩ := hconfine Wi hWC hWiodd hWiinv hWY hVWi
  have hinter : Wi ⊓ LocalProjectiveKernelQuotients.originalAmbientOddCore i = Wi ⊓ U :=
    original_ambient_inversion_identifies_odd_intersection t i Wi U hHall.2.2.2.2.1 hWiinv
  refine ⟨hLift, U, hHall, hti, hQuotient, hWC, hContain, hinter, ?_⟩
  intro hF
  have h := hNontrivial hF
  obtain ⟨hFU, hFodd, hFnormal, hVU, hVA, hJF, hKF, hKA, hUK,
    hiA, hiK, hKA', hRnontrivial, hAproper, hRodd, hFcore, hJcover, hcover,
    hfactor, hcoreinter, hintrinsic, hcentralA, hPnormal, hPodd, hPcore, hPmap,
    hbracketP, hbracketCore, hmemP, hmemCore, hquot⟩ := h
  exact hbracketCore

end OriginalNontrivialFactor

end CFSG.Semidihedral.EscapingLocalEigensubgroups
