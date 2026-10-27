module

public import CFSG.CharacterTheory.Semidihedral.StationaryLayerCoverSupport
public import CFSG.CharacterTheory.Semidihedral.LocalSylowNormalizerFactorization

public section

namespace CFSG.Semidihedral.StationaryLayerCover

open CFSG.Open CFSG.DihedralBlueprint
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Semidihedral.LocalCoverFactorization
  (nontrivial_odd_core_local_layer_cover_forces_quaternion_factorization)
open CFSG.Semidihedral.LocalSylowNormalizerFactorization
  (localSylowNormalizer local_sylow_normalizer_in_original_centralizer)

theorem centralized_or_inverted_of_layer_cover
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
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
    {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) :
    (∀ x ∈ ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype, s * x * s⁻¹ = x) ∨
      (∀ x ∈ ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype,
        s * x * s⁻¹ = x⁻¹) := by
  have : Fact ell.Prime := ⟨hell⟩
  set Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype with hPa
  set V := Subgroup.closure ({t, s} : Set G) with hV
  have hellodd : Odd ell := (actual_centralizer_core_odd t).of_dvd_nat hellN
  have hVK : IsKleinFour V := actual_involution_pair_isKleinFour t s ht hs hsC hts
  obtain ⟨htV, hV2, hVC⟩ := original_involution_pair_properties t s ht hs hsC
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have ht1 : t ≠ 1 := fun h => by simp [h] at ht
  have hs1 : s ≠ 1 := fun h => by simp [h] at hs
  have : Group.IsPerfect G := isPerfect_of_nonabelian hGnonab
  obtain ⟨S', hVS'⟩ := hV2.exists_le_sylow
  let f' : SemidihedralGroup n ≃* S' := fS.trans (Sylow.equiv S S')
  let D := ambientOddCore (Subgroup.normalizer (V : Set G))
  obtain ⟨-, hZD, hZDbot, hZDcomm, -⟩ :=
    CFSG.Semidihedral.Local.four_and_quaternion_eight_local_normalizer_quotients n hn S' f' V
      hVS' (Or.inl hVK)
  have hVcomm : IsMulCommutative V := IsKleinFour.isMulCommutative
  have hZ : (Subgroup.center V).map V.subtype = V := by
    rw [Subgroup.center_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hZ] at hZD hZDbot hZDcomm
  have hVD : V ⊔ D = Subgroup.centralizer (V : Set G) := hZD
  have hDC : D ≤ Subgroup.centralizer (V : Set G) := hVD ▸ le_sup_right
  have hV2' : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have h := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V)
    rw [IsKleinFour.exponent_two] at h
    exact congrArg Subtype.val h
  have hoddD : ∀ x ∈ Subgroup.centralizer (V : Set G), Odd (orderOf x) → x ∈ D := by
    intro x hx hodd
    have hx' : x ∈ V ⊔ D := by
      rw [hVD]
      exact hx
    exact mem_of_odd_orderOf_of_mem_sup hZDcomm hZDbot hV2' hx' hodd
  have hNVD : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    ambientOddCore_normalized _
  have hDodd : Odd (Nat.card D) := ambientOddCore_odd _
  have hDt : D ≤ C t := hDC.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htV))
  let Na := (N t).map (C t).subtype
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have hNan : (Na.subgroupOf (C t)).Normal := by
    have h : Na.subgroupOf (C t) = N t :=
      Subgroup.comap_map_eq_self_of_injective (C t).subtype_injective _
    rw [h]
    infer_instance
  have hNaodd : Odd (Nat.card Na) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective]
    exact actual_centralizer_core_odd t
  let ND := Na ⊔ D
  have hNDodd : Odd (Nat.card ND) := odd_card_sup_in_parent (C t) Na D hNaC hDt hNan hNaodd hDodd
  have hNDt : ND ≤ C t := sup_le hNaC hDt
  have hVND : V ≤ Subgroup.normalizer (ND : Set G) :=
    (le_inf (actual_centralizer_core_normalized t V hVC)
      (Subgroup.le_normalizer.trans hNVD)).trans (Subgroup.inf_normalizer_le_normalizer_sup Na D)
  let PD0 : Subgroup G := ((default : Sylow ell D) : Subgroup D).map D.subtype
  have hPD0 : IsSylowIn ell PD0 D := isSylowIn_map ell D default
  have hVPD0 : V ≤ Subgroup.normalizer (PD0 : Set G) :=
    ((Subgroup.le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le hPD0.1)).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨Q0, hQ0, hPDQ0, hVQ0⟩ := normalized_sylow_containing 2 ell Nat.prime_two hell V ND
    PD0 hV2 hVND (Nat.coprime_two_left.mpr hNDodd) (hPD0.1.trans le_sup_right) hPD0.2.1 hVPD0
  obtain ⟨Q0s, hQ0s⟩ := (isSylowIn_iff_exists_sylow ell Q0 ND).mp hQ0
  have hPaNa : Pa ≤ Na := Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hPaell : IsPGroup ell Pa := (P.isPGroup'.map _).map _
  obtain ⟨c, hc, hPaQ⟩ := invariant_pgroup_le_fixed_conjugate_sylow hell V ND Pa hV2 hVND
    hNDodd Q0s (by rw [hQ0s]; exact hVQ0) (hPaNa.trans le_sup_left) hPaell hVP
  rw [hQ0s] at hPaQ
  have hcodd : Odd (orderOf c) := hNDodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard ND hc.1)
  have hcD : c ∈ D := hoddD c hc.2 hcodd
  let Q := Q0.map (MulAut.conj c).toMonoidHom
  let PD := PD0.map (MulAut.conj c).toMonoidHom
  have hPD : IsSylowIn ell PD D := isSylowIn_map_conj hPD0 (Subgroup.le_normalizer hcD)
  have hQp : IsPGroup ell Q := hQ0.2.1.map _
  have hPDQ : PD ≤ Q := Subgroup.map_mono hPDQ0
  have hcV : ∀ v ∈ V, (MulAut.conj c) v = v := by
    intro v hv
    change c * v * c⁻¹ = v
    rw [← Subgroup.mem_centralizer_iff.mp hc.2 v hv, mul_inv_cancel_right]
  have hVQ : V ≤ Subgroup.normalizer (Q : Set G) :=
    normalized_map_of_fixed (MulAut.conj c) V Q0 hcV hVQ0
  have hQND : Q ≤ ND := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hc.1) y).mp (hQ0.1 hy)
  have hQt : Q ≤ C t := hQND.trans hNDt
  have hQD : Q ⊓ D = PD := hPD.2.2 _ inf_le_right (hQp.to_le inf_le_left) (le_inf hPDQ hPD.1)
  let F := Pa ⊓ Subgroup.centralizer ({s} : Set G)
  have hPaodd : Odd (Nat.card Pa) := odd_card_of_pgroup hell hellodd Pa hPaell
  have hPat : Pa ≤ C t := Subgroup.map_subtype_le _
  have hCV : ∀ x : G, x ∈ Subgroup.centralizer ({t} : Set G) →
      x ∈ Subgroup.centralizer ({s} : Set G) → x ∈ Subgroup.centralizer (V : Set G) := by
    intro x hxt hxs
    have hle : V ≤ Subgroup.centralizer ({x} : Set G) := by
      apply (Subgroup.closure_le _).mpr
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hxt).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hxs).symm
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
  have hFPD : F ≤ PD := by
    rintro x ⟨hxPa, hxs⟩
    have hxV := hCV x (hPat hxPa) hxs
    have hxodd : Odd (orderOf x) := hPaodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Pa hxPa)
    rw [← hQD]
    exact ⟨hPaQ hxPa, hoddD x hxV hxodd⟩
  by_cases hFP : F = Pa
  · left
    intro x hx
    have hxF : x ∈ F := by
      rw [hFP]
      exact hx
    exact (conj_fixed_iff s x).mpr hxF.2
  by_cases hF1 : F = ⊥
  · right
    exact inverted_of_trivial_fixed_subgroup s hs Pa hPaodd (hVP hsV) hF1
  exfalso
  have hQPD : ¬ Q ≤ PD := by
    intro hle
    apply hFP
    apply le_antisymm inf_le_left
    intro x hx
    refine ⟨hx, ?_⟩
    have hxD : x ∈ D := hPD.1 (hle (hPaQ hx))
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hDC hxD) s hsV).symm
  have hdV : ∀ d ∈ D, ∀ u ∈ V, d * u * d⁻¹ = u := by
    intro d hd u hu
    rw [← Subgroup.mem_centralizer_iff.mp (hDC hd) u hu, mul_inv_cancel_right]
  obtain ⟨g0, hg0V, hg0⟩ := exists_fixedFree_normalizer_element hn S' f' V hVS'
  obtain ⟨h0, hh0V, hh0⟩ := CFSG.Semidihedral.Local.klein_four_normalizer_conj_transitive n hn
    S' f' V hVS' hVK hsV htV hs1 ht1
  obtain ⟨d1, hd1, hgH⟩ := exists_mul_mem_normalizer hell hPD (hNVD hg0V)
  obtain ⟨d2, hd2, hhH⟩ := exists_mul_mem_normalizer hell hPD (hNVD hh0V)
  have hgV : d1 * g0 ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ (hDC hd1)) hg0V
  have hgfix : ∀ v ∈ V, v ≠ 1 → d1 * g0 * v * (d1 * g0)⁻¹ ≠ v := by
    intro v hv hv1
    have hu : g0 * v * g0⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg0V v).mp hv
    rw [show d1 * g0 * v * (d1 * g0)⁻¹ = d1 * (g0 * v * g0⁻¹) * d1⁻¹ by group,
      hdV d1 hd1 _ hu]
    exact hg0 v hv hv1
  have hhs : d2 * h0 * s * (d2 * h0)⁻¹ = t := by
    rw [show d2 * h0 * s * (d2 * h0)⁻¹ = d2 * (h0 * s * h0⁻¹) * d2⁻¹ by group, hh0,
      hdV d2 hd2 t htV]
  have hFNa : F ≤ Na := inf_le_left.trans hPaNa
  have hFt : F ≤ C t := inf_le_left.trans hPat
  have hVs : V ≤ Subgroup.centralizer ({s} : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hVcomm).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsV))
  have hVF : V ≤ Subgroup.normalizer (F : Set G) :=
    (le_inf hVP (hVs.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hFcover := centralizer_cover_descends (C t) (nu t)
    ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) Pa F inf_le_left hcover
  have hKcover : ((Subgroup.normalizer (F : Set G)).subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · calc (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) =
            ((Subgroup.centralizer (F : Set G)).subgroupOf (C t) ⊓
              ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
                (nu t) := hFcover.symm
        _ ≤ ((Subgroup.normalizer (F : Set G)).subgroupOf (C t) ⊓
              ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
                (nu t) :=
          Subgroup.map_mono (inf_le_inf (Subgroup.subgroupOf_mono _
            (Subgroup.centralizer_le_normalizer _)) le_rfl)
  have hFodd : Odd (Nat.card F) := hPaodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hKcore : CFSG.pPrimeCore 2 (Subgroup.normalizer (F : Set G)) ≠ ⊥ := by
    intro hbot
    have h1 := original_odd_subgroup_le_normalizer_core F hFodd
    rw [ambientOddCore, original_oddCore_eq_twoPrimeCore, hbot, Subgroup.map_bot] at h1
    exact hF1 (le_bot_iff.mp h1)
  have hquat := nontrivial_odd_core_local_layer_cover_forces_quaternion_factorization
    G hGnonab hrecognition n hn S fS t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq
    hmodel (Subgroup.normalizer (F : Set G)) hVF hKcore hKcover
  obtain ⟨⟨-, -, -, -, -, -, hfacK, -, -⟩, -⟩ := hquat.2 F hF1 hFNa hVF hFcover
  have hloc := stationary_centralizer_cover_prime_forces_local_invariant_subgroup_centralization
    hGnonab hrecognition n hn S fS t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq
    hmodel hell P hellN hVP hcover hstationary F hF1 inf_le_left hVF
  exact false_of_localized_fixed_subgroup hell hellodd hn S fS ht V htV ht1 hsV hCV hDC hoddD
    hPD hQp hPDQ hVQ hQt hQD hQPD hFPD hFt hgH hgV hgfix hhH hhs hfacK
    (fun W hWK hWp htW => (hloc.1 W hWK hWp htW).1)

theorem stationary_layer_cover_local_prime_is_centralized_or_inverted
    {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
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
    {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) :
    let Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    ((((Subgroup.centralizer (Pa : Set G)).subgroupOf (C t) ⊓ Y).map (nu t) = T₀) ↔
        ((∀ x ∈ Pa, s * x * s⁻¹ = x) ∨ (∀ x ∈ Pa, s * x * s⁻¹ = x⁻¹))) ∧
      ((∀ x ∈ Pa, s * x * s⁻¹ = x⁻¹) → IsMulCommutative Pa) := by
  intro Pa T₀ Y
  have : Fact ell.Prime := ⟨hell⟩
  refine ⟨⟨fun hcover => centralized_or_inverted_of_layer_cover hGnonab hrecognition n hn S fS
    t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hell P hellN hVP hcover
    hstationary, fun hact => ?_⟩, abelian_of_inverted s Pa⟩
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  let sC : C t := ⟨s, hsC⟩
  have hsC2 : orderOf sC = 2 := (Subgroup.orderOf_coe sC).symm.trans hs
  have hst : sC ≠ tInC t := fun h => hts (congrArg Subtype.val h).symm
  have hsP : sC ∈ Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t))) : Set (C t)) := by
    have hsV : s ∈ Subgroup.closure ({t, s} : Set G) := Subgroup.subset_closure (by simp)
    have h : sC ∈ (localSylowNormalizer t P).subgroupOf (C t) := hVP hsV
    rw [local_sylow_normalizer_in_original_centralizer] at h
    exact h
  have hact' : (∀ x : N t, x ∈ P → sC * (x : C t) * sC⁻¹ = x) ∨
      (∀ x : N t, x ∈ P → sC * (x : C t) * sC⁻¹ = (x : C t)⁻¹) := by
    rcases hact with h | h
    · exact Or.inl fun x hx => Subtype.ext (h _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
    · exact Or.inr fun x hx => Subtype.ext (h _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
  have hcov :=
    CFSG.Semidihedral.Local.centralized_or_inverted_local_sylow_prime_has_layer_covering_centralizer
      n hn S fS hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel sC hsC2 hst ell hellN P hsP
      hact'
  have key : (Subgroup.centralizer (Pa : Set G)).subgroupOf (C t) =
      Subgroup.centralizer ((((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t))) :
        Set (C t)) :=
    centralizer_map_subtype_subgroupOf (C t) _
  rw [key]
  exact hcov

end CFSG.Semidihedral.StationaryLayerCover
