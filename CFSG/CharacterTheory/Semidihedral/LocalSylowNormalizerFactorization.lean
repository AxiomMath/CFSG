module

public import CFSG.CharacterTheory.Semidihedral.LocalCoverFactorization

public noncomputable section

namespace CFSG.Semidihedral.LocalSylowNormalizerFactorization

open CFSG.Open
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Semidihedral.LocalCoverFactorization
open CFSG.Wreathed.OriginalSylowNormalizerWitness

universe u

@[expose] def localSylowInCentralizer {G : Type u} [Group G] (t : G) {ell : ℕ}
    (P : Sylow ell (N t)) : Subgroup (C t) :=
  (P : Subgroup (N t)).map (N t).subtype

@[expose] def localSylowAmbient {G : Type u} [Group G] (t : G) {ell : ℕ}
    (P : Sylow ell (N t)) : Subgroup G :=
  (localSylowInCentralizer t P).map (C t).subtype

@[expose] def localSylowNormalizer {G : Type u} [Group G] (t : G) {ell : ℕ}
    (P : Sylow ell (N t)) : Subgroup G :=
  Subgroup.normalizer (localSylowAmbient t P : Set G)

theorem local_sylow_normalizer_in_original_centralizer
    {G : Type u} [Group G] (t : G) {ell : ℕ} (P : Sylow ell (N t)) :
    (localSylowNormalizer t P).subgroupOf (C t) =
      Subgroup.normalizer (localSylowInCentralizer t P : Set (C t)) := by
  change (Subgroup.normalizer
    ((localSylowInCentralizer t P).map (C t).subtype : Set G)).comap (C t).subtype = _
  rw [Subgroup.comap_normalizer_eq_of_le_range
    ((Subgroup.map_subtype_le _).trans_eq (C t).range_subtype.symm),
    Subgroup.comap_map_eq_self_of_injective (C t).subtype_injective]

theorem original_local_sylow_frattini
    {G : Type u} [Group G] [Finite G] (t : G) {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) :
    (localSylowNormalizer t P).subgroupOf (C t) ⊔ N t = ⊤ := by
  let : Fact ell.Prime := ⟨hell⟩
  rw [local_sylow_normalizer_in_original_centralizer]
  exact Sylow.normalizer_sup_eq_top P

theorem original_local_sylow_normalizer_covers_odd_core_quotient
    {G : Type u} [Group G] [Finite G] (t : G) {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) :
    ((localSylowNormalizer t P).subgroupOf (C t)).map (nu t) = ⊤ := by
  have h := congrArg (Subgroup.map (nu t)) (original_local_sylow_frattini t hell P)
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
    Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h
  exact h

theorem original_local_sylow_frattini_element_factorization
    {G : Type u} [Group G] [Finite G] (t : G) {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) :
    ∀ x : C t, ∃ a ∈ N t,
      ∃ b ∈ (localSylowNormalizer t P).subgroupOf (C t), a * b = x := by
  intro x
  have h : N t ⊔ (localSylowNormalizer t P).subgroupOf (C t) = ⊤ := by
    rw [sup_comm]
    exact original_local_sylow_frattini t hell P
  exact Subgroup.mem_sup_of_normal_left.mp (h ▸ Subgroup.mem_top x)

theorem original_local_sylow_normalizer_quotient_representatives
    {G : Type u} [Group G] [Finite G] (t : G) {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) :
    ∀ x : C t, ∃ b : (localSylowNormalizer t P).subgroupOf (C t),
      nu t b = nu t x ∧ kappa t b = kappa t x := by
  intro x
  obtain ⟨b, hb, hrep⟩ := (original_local_sylow_normalizer_covers_odd_core_quotient
    t hell P).ge (show nu t x ∈ (⊤ : Subgroup (H t)) from Subgroup.mem_top _)
  exact ⟨⟨b, hb⟩, hrep, congrArg (barKappa t) hrep⟩

theorem original_local_sylow_normalizer_covers_reduced_quotient
    {G : Type u} [Group G] [Finite G] (t : G) {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) :
    ((localSylowNormalizer t P).subgroupOf (C t)).map (kappa t) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (NZ t) x
  obtain ⟨b, _, hb⟩ := original_local_sylow_normalizer_quotient_representatives t hell P c
  exact ⟨b, b.property, hb⟩

theorem original_involution_mem_local_sylow_normalizer
    {G : Type u} [Group G] (t : G) {ell : ℕ} (P : Sylow ell (N t)) :
    t ∈ localSylowNormalizer t P := by
  have h := Subgroup.center_le_normalizer
    (localSylowInCentralizer t P : Set (C t)) (tInC_central t)
  rw [← local_sylow_normalizer_in_original_centralizer] at h
  exact h

theorem original_local_sylow_normalizer_covers_layer
    {G : Type u} [Group G] [Finite G] (t : G) {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) :
    ((localSylowNormalizer t P).subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  apply le_antisymm
  · rintro x ⟨b, hb, rfl⟩
    exact hb.2
  · intro x hx
    obtain ⟨b, hb, hrep⟩ := (original_local_sylow_normalizer_covers_odd_core_quotient
      t hell P).ge (show x ∈ (⊤ : Subgroup (H t)) from Subgroup.mem_top _)
    have hbT : b ∈ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap
        (nu t) := by
      change nu t b ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
      rwa [hrep]
    exact ⟨b, ⟨hb, hbT⟩, hrep⟩

theorem original_local_sylow_centralizer_normalizer_odd_index
    {G : Type u} [Group G] [Finite G] (t : G) {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) :
    Odd ((localSylowNormalizer t P).subgroupOf (C t)).index := by
  have hker : Odd (Nat.card (nu t).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  apply odd_index_of_odd_kernel_and_image (nu t) (QuotientGroup.mk'_surjective _)
    hker ((localSylowNormalizer t P).subgroupOf (C t))
  rw [original_local_sylow_normalizer_covers_odd_core_quotient t hell P,
    Subgroup.index_top]
  exact odd_one

theorem original_local_sylow_normalizer_nontrivial_odd_core
    {G : Type u} [Group G] [Finite G] (t : G) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (N t)) (P : Sylow ell (N t)) :
    localSylowAmbient t P ≠ ⊥ ∧
      localSylowAmbient t P ≤
        (CFSG.pPrimeCore 2 (localSylowNormalizer t P)).map
          (localSylowNormalizer t P).subtype ∧
      CFSG.pPrimeCore 2 (localSylowNormalizer t P) ≠ ⊥ := by
  let : Fact ell.Prime := ⟨hell⟩
  have hPne : localSylowAmbient t P ≠ ⊥ := by
    intro hbot
    have hPC : localSylowInCentralizer t P = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective).mp hbot
    exact P.ne_bot_of_dvd_card hdiv
      ((Subgroup.map_eq_bot_iff_of_injective _ (N t).subtype_injective).mp hPC)
  have hPodd : Odd (Nat.card (localSylowAmbient t P)) := by
    rw [localSylowAmbient, Subgroup.card_subtype]
    exact (Nat.coprime_two_left.mp
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))).of_dvd_nat
        (Subgroup.card_dvd_of_le (show localSylowInCentralizer t P ≤ N t from
          Subgroup.map_subtype_le _))
  have hPcore : localSylowAmbient t P ≤
      (CFSG.pPrimeCore 2 (localSylowNormalizer t P)).map
        (localSylowNormalizer t P).subtype := by
    have h := normal_odd_le_ambientOddCore (localSylowAmbient t P)
      (localSylowNormalizer t P) (localSylowAmbient t P).le_normalizer
        (by change ((localSylowAmbient t P).subgroupOf
              (Subgroup.normalizer (localSylowAmbient t P : Set G))).Normal
            infer_instance) hPodd
    simpa only [ambientOddCore,
      CFSG.Semidihedral.QuaternionFocalFactorization.oddCore_eq_twoPrimeCore] using h
  refine ⟨hPne, hPcore, ?_⟩
  intro hbot
  rw [hbot, Subgroup.map_bot] at hPcore
  exact hPne (bot_unique hPcore)

theorem original_local_sylow_normalizer_contains_original_involution_pair
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t : G) (ht : orderOf t = 2) {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) :
    ∃ s : G, orderOf s = 2 ∧ s ∈ C t ∧ t ≠ s ∧
      Subgroup.closure ({t, s} : Set G) ≤ localSylowNormalizer t P := by
  let H := localSylowNormalizer t P
  let B := H.subgroupOf (C t)
  let K := H ⊓ C t
  have hBodd : Odd B.index :=
    original_local_sylow_centralizer_normalizer_odd_index t hell P
  have hCodd := original_involution_centralizer_odd_index n hn S0 f0 hG t ht
  have hKmap : B.map (C t).subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype]
  have hKodd : Odd K.index := by
    rw [← hKmap, Subgroup.index_map_subtype]
    exact hBodd.mul hCodd
  let SK : Sylow 2 K := default
  obtain ⟨SG, hSG⟩ := SameParameterSections.subgroup_sylow_of_odd_index K hKodd SK
  let fG := f0.trans (Sylow.equiv S0 SG)
  let eK := ((SK : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hSG.symm)
  let fK := fG.trans eK.symm
  have htK : t ∈ K :=
    ⟨original_involution_mem_local_sylow_normalizer t P,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let tK : K := ⟨t, htK⟩
  have htKorder : orderOf tK = 2 := (Subgroup.orderOf_coe tK).symm.trans ht
  have htKcentral : tK ∈ Subgroup.center K := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.property.2
  have hzK := central_involution_eq_supplied_semidihedral_center n hn SK fK tK
    htKcentral htKorder
  have htKpow : tK = (fK (CFSG.Semidihedral.r n) : K) ^ 2 ^ (n - 2) := by
    rw [← hzK, CFSG.Semidihedral.z, map_pow, Subgroup.coe_pow, CFSG.Semidihedral.half]
  obtain ⟨-, -, -, -, hsKorder, hsKne⟩ :=
    CFSG.Semidihedral.Principal.supplied_t_s_facts hn fK htKpow
  let sG : G := ((fK (CFSG.Semidihedral.s n) : K) : G)
  have hsGorder : orderOf sG = 2 :=
    (Subgroup.orderOf_coe (fK (CFSG.Semidihedral.s n) : K)).trans hsKorder
  have hsGC : sG ∈ C t := (fK (CFSG.Semidihedral.s n) : K).property.2
  have hts : t ≠ sG := by
    intro h
    exact hsKne (Subtype.ext h.symm)
  refine ⟨sG, hsGorder, hsGC, hts, ?_⟩
  apply (Subgroup.closure_le H).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hxt | hxs
  · exact hxt ▸ htK.1
  · have hxs' : x = sG := Set.mem_singleton_iff.mp hxs
    exact hxs' ▸ (fK (CFSG.Semidihedral.s n) : K).property.1

theorem original_local_sylow_normalizer_full_quaternion_data
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (N t))
    (P : Sylow ell (N t)) :
    OriginalCoverQuaternionConclusion n t p f (localSylowNormalizer t P) := by
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨s, hs, hsC, hts, hVH⟩ :=
    original_local_sylow_normalizer_contains_original_involution_pair
      n hn S0 f0 hG t ht hell P
  have hR := (original_local_sylow_normalizer_nontrivial_odd_core t hell hdiv P).2.2
  exact original_layer_cover_complete_quaternion_data
    G hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel (localSylowNormalizer t P) hVH hR
        (original_local_sylow_normalizer_covers_layer t hell P)

theorem local_odd_core_sylow_normalizer_has_quaternion_focal_factorization
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (N t))
    (P : Sylow ell (N t)) :
    let H := localSylowNormalizer t P
    let B := H.subgroupOf (C t)
    let R := CFSG.pPrimeCore 2 B
    let Delta := B ⧸ (R ⊔ (Z t).subgroupOf B)
    Odd ell ∧ localSylowAmbient t P ≠ ⊥ ∧
      localSylowAmbient t P ≤ (CFSG.pPrimeCore 2 H).map H.subtype ∧
      CFSG.pPrimeCore 2 H ≠ ⊥ ∧ B ⊔ N t = ⊤ ∧
      (∀ x : C t, ∃ a ∈ N t, ∃ b ∈ B, a * b = x) ∧
      B = Subgroup.normalizer (localSylowInCentralizer t P : Set (C t)) ∧
      t ∈ H ∧ OriginalCoverFocalConclusion n t H ∧
      OriginalCoverParameterConclusion t p f H ∧
      ∃ e : Delta ≃* Gamma t,
        (∀ b : B, e (QuotientGroup.mk' (R ⊔ (Z t).subgroupOf B) b) = kappa t b) ∧
        (CFSG.generalizedFitting Delta).map e.toMonoidHom =
          CFSG.generalizedFitting (Gamma t) := by
  intro H B R Delta
  obtain ⟨hPne, hPcore, hR⟩ := original_local_sylow_normalizer_nontrivial_odd_core t hell hdiv P
  obtain ⟨hfocal, hparameter⟩ := original_local_sylow_normalizer_full_quaternion_data
    G hGnonab hrecognition n hn S0 f0 t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel hell hdiv P
  have hparameterCopy := hparameter
  obtain ⟨-, iota, hinj, hrep, hrange, hJmap, -⟩ := hparameterCopy
  have hsurj : Function.Surjective iota := by
    apply MonoidHom.range_eq_top.mp
    rw [hrange]
    exact original_local_sylow_normalizer_covers_reduced_quotient t hell P
  let e : Delta ≃* Gamma t := MulEquiv.ofBijective iota ⟨hinj, hsurj⟩
  have hellodd : Odd ell := (Nat.coprime_two_left.mp
    (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))).of_dvd_nat hdiv
  exact ⟨hellodd, hPne, hPcore, hR, original_local_sylow_frattini t hell P,
    original_local_sylow_frattini_element_factorization t hell P,
    local_sylow_normalizer_in_original_centralizer t P,
    original_involution_mem_local_sylow_normalizer t P,
    hfocal, hparameter, e, hrep, hJmap⟩

end CFSG.Semidihedral.LocalSylowNormalizerFactorization
