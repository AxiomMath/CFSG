module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PullBackSpin
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Reduce
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Two

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups commutatorElement

theorem isCoverOf_of_mulEquiv {τ : StatedLieTag} {n p f c : ℕ} {A B : Type} [Group A]
    [Group B] (e : A ≃* B) (h : IsCoverOf τ n p f c A) : IsCoverOf τ n p f c B :=
  CFSG.ComponentClassification.HarrisLit.T1.S74.isCoverOf_congr e h

theorem isSLTwoOver_of_mulEquiv' {q : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsSLTwoOver q A) : IsSLTwoOver q B := by
  obtain ⟨F, i₁, i₂, hF, ⟨eF⟩⟩ := h
  exact ⟨F, i₁, i₂, hF, ⟨e.symm.trans eF⟩⟩

theorem card_comap_mk' {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (H : Subgroup (Y ⧸ N)) :
    Nat.card ↥(H.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card H := by
  have h1 := Subgroup.card_mul_index (H.comap (QuotientGroup.mk' N))
  have h2 := Subgroup.card_mul_index H
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : Nat.card ↥(H.comap (QuotientGroup.mk' N)) * H.index =
      Nat.card N * Nat.card H * H.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) this

theorem card_fusionZStar (Y : Type) [Group Y] [Finite Y] :
    Nat.card ↥(Open.fusionZStar Y) =
      Nat.card ↥(pPrimeCore 2 Y) * Nat.card ↥(center (Y ⧸ pPrimeCore 2 Y)) := by
  have hO : Open.fusionOddCore Y = pPrimeCore 2 Y := GSLit.oddCore_eq_pPrimeCore_two Y
  have h := card_comap_mk' (Open.fusionOddCore Y) (center (Y ⧸ Open.fusionOddCore Y))
  change Nat.card ↥(Open.fusionZStar Y) = _ at h
  rw [h]
  congr 1
  · rw [hO]
  · let e : Y ⧸ Open.fusionOddCore Y ≃* Y ⧸ pPrimeCore 2 Y := QuotientGroup.quotientMulEquivOfEq hO
    rw [← OuterAutomorphisms.center_map_equiv e, Subgroup.card_map_of_injective e.injective]

theorem ordProj_two_mul_of_odd {a b : ℕ} (ha : Odd a) (hb : b ≠ 0) :
    ordProj[2] (a * b) = ordProj[2] b := by
  have ha0 : a ≠ 0 := by rintro rfl; exact absurd ha (by decide)
  rw [Nat.factorization_mul ha0 hb, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr ha)
      (even_iff_two_dvd.mpr h)), zero_add]

theorem isMTypeSchur_of_bar_equiv {p : ℕ} {A B : Type} [Group A] [Group B] [Finite A]
    [Finite B] (hA : IsMTypeSchur p A) (hB : IsTwoQuasisimple B)
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) : IsMTypeSchur p B := by
  obtain ⟨eZ⟩ := FooteLit.nonempty_fusionZStar_equiv_of_quotient_equiv e
  have hcZ : Nat.card ↥(center (B ⧸ pPrimeCore 2 B)) =
      Nat.card ↥(center (A ⧸ pPrimeCore 2 A)) := by
    rw [← OuterAutomorphisms.center_map_equiv e, Subgroup.card_map_of_injective e.injective]
  have hoA := odd_card_pPrimeCore_two A
  have hoB := odd_card_pPrimeCore_two B
  have hcA : Nat.card ↥(center (A ⧸ pPrimeCore 2 A)) ≠ 0 := Nat.card_pos.ne'
  have hev : Even (Nat.card ↥(Open.fusionZStar A)) → Even (Nat.card ↥(Open.fusionZStar B)) := by
    rw [card_fusionZStar, card_fusionZStar, Nat.even_mul, Nat.even_mul, hcZ]
    rintro (h | h)
    · exact absurd h (Nat.not_even_iff_odd.mpr hoA)
    · exact .inr h
  have hord : ordProj[2] (Nat.card ↥(Open.fusionZStar B)) =
      ordProj[2] (Nat.card ↥(Open.fusionZStar A)) := by
    rw [card_fusionZStar, card_fusionZStar, ordProj_two_mul_of_odd hoB (hcZ ▸ hcA),
      ordProj_two_mul_of_odd hoA hcA, hcZ]
  rcases hA with ⟨-, ⟨τ, n, f, hm⟩, hevA, hc⟩ | ⟨hp3, ⟨e'⟩⟩
  · refine .inl ⟨hB, ⟨τ, n, f, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩, hev hevA,
      fun n' r hn hr hm' => ?_⟩
    rw [hord, hc n' r hn hr (hm'.imp (GSThmB.OddQuot.lieModel_of_equiv eZ.symm)
      (GSThmB.OddQuot.lieModel_of_equiv eZ.symm)),
      Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).toEquiv]
  · exact .inr ⟨hp3, ⟨e.symm.trans e'⟩⟩

theorem inductionTypeField_of_bar_equiv {p : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) (h : InductionTypeField p A) :
    InductionTypeField p B := by
  obtain ⟨f, hf, h⟩ := h
  refine ⟨f, hf, ?_⟩
  rcases h with h | h | h | h | ⟨hev, h⟩
  · exact .inl (isCoverOf_of_mulEquiv e h)
  · exact .inr (.inl (isCoverOf_of_mulEquiv e h))
  · exact .inr (.inr (.inl (isCoverOf_of_mulEquiv e h)))
  · exact .inr (.inr (.inr (.inl (isCoverOf_of_mulEquiv e h))))
  · exact .inr (.inr (.inr (.inr ⟨hev, isSLTwoOver_of_mulEquiv' e h⟩)))

theorem inductionType_of_bar_equiv {p : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) (h : InductionType p A) :
    InductionType p B := by
  rcases h with h | ⟨hp3, h⟩
  · exact .inl (inductionTypeField_of_bar_equiv e h)
  · obtain ⟨eZ⟩ := FooteLit.nonempty_fusionZStar_equiv_of_quotient_equiv e
    refine .inr ⟨hp3, ?_⟩
    rcases h with ⟨τ, n, hm⟩ | he'
    · exact .inl ⟨τ, n, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩
    · obtain ⟨e'⟩ := he'
      exact .inr ⟨e.symm.trans e'⟩

variable {G : Type} [Group G] [Finite G]

theorem isTwoComponentIn_subgroupOf_inf {K J : Subgroup G} {z : G} (hzK : z ∈ K)
    (hJ : IsTwoComponentIn J (K ⊓ centralizer {z})) :
    IsTwoComponentIn (J.subgroupOf K) (centralizer {(⟨z, hzK⟩ : ↥K)}) := by
  have hCv : centralizer ({(⟨z, hzK⟩ : ↥K)} : Set ↥K) = (K ⊓ centralizer {z}).subgroupOf K := by
    ext x
    rw [mem_subgroupOf, mem_inf]
    constructor
    · intro h
      exact ⟨x.2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp h))⟩
    · rintro ⟨-, h⟩
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp h))
  rw [hCv]
  have hle : J.subgroupOf K ≤ (K ⊓ centralizer {z}).subgroupOf K := fun x hx => hJ.1 hx
  rw [isTwoComponentIn_iff hle, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
    (inf_le_left : K ⊓ centralizer {z} ≤ K) 2 Nat.prime_two]
  exact (isTwoComponentIn_iff hJ.1).mp hJ

theorem not_le_24_of_isQuasisimple {Y : Type} [Group Y] [Finite Y] (hq : IsQuasisimple Y)
    (h : Nat.card Y ≤ 24) : False := by
  have : IsSimpleGroup (Y ⧸ center Y) := hq.2.1
  have h60 := GroupTheory.nonabelian_simple_order_at_least_sixty (G := Y ⧸ center Y) hq.2.1
    hq.2.2
  have hle : Nat.card (Y ⧸ center Y) ≤ Nat.card Y :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  omega

theorem isSimpleChevalleyOver_of_isChevalleyOver {Y : Type} [Group Y] [Finite Y]
    (hY : IsTwoQuasisimple Y) {p : ℕ} (h : IsChevalleyOver p (Y ⧸ pPrimeCore 2 Y)) :
    IsSimpleChevalleyOver p (Y ⧸ Open.fusionZStar Y) := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv Y
  rcases h with ⟨-, τ, n, f, hm⟩ | ⟨-, hS⟩
  · exact ⟨τ, n, f, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hm⟩
  · exfalso
    refine not_le_24_of_isQuasisimple hY.2 ?_
    rcases hS with hS | hS
    · obtain ⟨e⟩ := hS
      rw [Nat.card_congr e.toEquiv, card_specialLinearGroup_two_zmod_three]
    · obtain ⟨e⟩ := hS
      rw [Nat.card_congr e.toEquiv, ← card_specialLinearGroup_two_zmod_three]
      exact Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective

theorem sixty_le_card_bar {J : Type} [Group J] [Finite J] (hJ : IsTwoQuasisimple J) :
    60 ≤ Nat.card (J ⧸ pPrimeCore 2 J) := by
  have hq := hJ.2
  have : IsSimpleGroup ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) := hq.2.1
  have h60 := GroupTheory.nonabelian_simple_order_at_least_sixty hq.2.1 hq.2.2
  exact h60.trans (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective)

theorem not_m11_of_twoQuasisimple
    {K : Type} [Group K] [Finite K]
    {z : K} (hz : orderOf z = 2) {J : Subgroup K} (hJz : J ≤ centralizer {z})
    (hJ : IsTwoQuasisimple ↥J) :
    ¬ Nonempty (K ⧸ pPrimeCore 2 K ≃* ↥Blueprint.NativeSporadic.M11) := by
  rintro ⟨eM⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 K)
  have hz' : orderOf (π z) = 2 := orderOf_mk_eq_two (odd_card_pPrimeCore_two K) hz
  have hH : J.map π ≤ centralizer {π z} := by
    rintro _ ⟨j, hj, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp
      (hJz hj)]
  let φ : ↥J →* ↥(J.map π) := (π.comp J.subtype).codRestrict _ (fun j => ⟨j, j.2, rfl⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨j, hj, rfl⟩⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  have hker : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map J.subtype ≤ pPrimeCore 2 K := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 K) := by
      rw [← Subgroup.card_map_of_injective J.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two K))
      (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨e⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective φ hφ hker
  have h60 : 60 ≤ Nat.card ↥(J.map π) := by
    have h1 := sixty_le_card_bar hJ
    rw [Nat.card_congr e.toEquiv] at h1
    exact h1.trans (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective)
  have hez : orderOf (eM (π z)) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz'
  obtain ⟨hc, hN⟩ :=
    Semidihedral.ProperSubgroupRegularity.m11_involution_centralizer_card_and_odd_core
      (eM (π z)) hez
  obtain ⟨hc', -⟩ :=
    Semidihedral.ProperSubgroupRegularity.centralizer_card_and_core_of_equiv eM (π z) hc hN
  have h48 : Nat.card ↥(J.map π) ≤ 48 := by
    rw [← hc']
    exact Subgroup.card_le_of_le hH
  omega

theorem isSimpleChevalleyOver_of_knownRow
    (hKR : KnownRow) (hK : Assembly.KProper Blueprint.Catalog G) {K : Subgroup G}
    (hKtop : K ≠ ⊤) (hKq : IsTwoQuasisimple ↥K) {z : G} (hzK : z ∈ K) (hz : orderOf z = 2)
    {J : Subgroup G} (hJ : IsTwoComponentIn J (K ⊓ centralizer {z})) (hzJ : z ∈ J) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hM : IsMTypeSchur p ↥J) (hI : InductionTypeField p ↥J) :
    IsSimpleChevalleyOver p (↥K ⧸ Open.fusionZStar ↥K) := by
  set z' : ↥K := ⟨z, hzK⟩ with hz'
  have hJ' : IsTwoComponentIn (J.subgroupOf K) (centralizer {z'}) :=
    isTwoComponentIn_subgroupOf_inf hzK hJ
  let eJ : ↥(J.subgroupOf K) ≃* ↥J := subgroupOfEquivOfLe (hJ.1.trans inf_le_left)
  have hM' : IsMTypeSchur p ↥(J.subgroupOf K) := T23.isMTypeSchur_of_mulEquiv eJ.symm hM
  have hI' : InductionTypeField p ↥(J.subgroupOf K) := inductionTypeField_of_bar_equiv
    (QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)) hI
  have htop := T23.oPrimeResidual_two_eq_top hKq.1
  let e : ↥(GH74.GLS.oPrimeResidual 2 ↥K) ≃* ↥K :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hN : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 ↥K) :=
    isTwoQuasisimple_of_mulEquiv e.symm hKq
  obtain ⟨eKZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥K
  have hq := hKq.2
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have : IsSimpleGroup (↥K ⧸ Open.fusionZStar ↥K) := eKZ.isSimpleGroup
  have hnab : ∃ a b : ↥K ⧸ Open.fusionZStar ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨eKZ.symm a, eKZ.symm b, fun hc => hab (eKZ.symm.injective ?_)⟩
    rw [map_mul, map_mul, hc]
  have hcatK : Blueprint.Catalog (↥K ⧸ Open.fusionZStar ↥K) :=
    QuasithinUnique.catalog_of_kProper_of_surjective hK K hKtop _ hnab
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv e
  have hcatN := SectionRank.catalog_of_mulEquiv eZ hcatK
  have hz'2 : orderOf z' = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  rcases hKR ↥K hN hcatN z' hz'2 (J.subgroupOf K) hJ' hzJ p hp hp2 hM' hI' with hch | hM11
  · exact isSimpleChevalleyOver_of_isChevalleyOver hKq
      (T23.isChevalleyOver_of_mulEquiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) hch)
  · exact absurd hM11 (not_m11_of_twoQuasisimple hz'2 hJ'.1 hJ'.2.2)

theorem le_coreActionKernel_of_ne {M K L : Subgroup G} (hK : IsTwoComponentIn K M)
    (hL : IsTwoComponentIn L M) (hne : K ≠ L) : K ≤ coreActionKernel L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' := (isTwoComponentIn_iff hK.1).mp hK
  have hL' := (isTwoComponentIn_iff hL.1).mp hL
  have hne' : K.subgroupOf M ≠ L.subgroupOf M := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hK.1, inf_eq_left.mpr hL.1] at h
    exact h
  obtain ⟨-, hKN, hcomm⟩ := CatalogueBPrimeJoin.mutual_normalization_core_commutation 2
    (K.subgroupOf M) (L.subgroupOf M) hK' hL' hne'
  let eL : ↥(L.subgroupOf M) ≃* ↥L := subgroupOfEquivOfLe hL.1
  intro x hx
  have hxM : x ∈ M := hK.1 hx
  have hx' : (⟨x, hxM⟩ : ↥M) ∈ K.subgroupOf M := hx
  refine ⟨?_, fun l hl => ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    have hN := mem_normalizer_iff.mp (hKN hx')
    constructor
    · intro hy
      exact (hN ⟨y, hL.1 hy⟩).mp hy
    · intro hy
      have hyM : y ∈ M := by
        have h1 : x * y * x⁻¹ ∈ M := hL.1 hy
        have h2 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem hxM) h1) hxM
      exact (hN ⟨y, hyM⟩).mpr hy
  · have hl' : (⟨l, hL.1 hl⟩ : ↥M) ∈ L.subgroupOf M := hl
    have hmem : ⁅(⟨l, hL.1 hl⟩ : ↥M)⁻¹, (⟨x, hxM⟩ : ↥M)⁻¹⁆ ∈
        ⁅K.subgroupOf M, L.subgroupOf M⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator (inv_mem hl') (inv_mem hx')
    obtain ⟨o, ho, hoeq⟩ := (hcomm hmem).2
    refine ⟨eL o, ?_, ?_⟩
    · rw [← pPrimeCore_map_iso 2 eL]
      exact ⟨o, ho, rfl⟩
    · have h1 : ((eL o : ↥L) : G) = ((o : ↥M) : G) := rfl
      rw [Subgroup.coe_subtype, h1]
      have h2 : ((o : ↥M) : G) = ((⁅(⟨l, hL.1 hl⟩ : ↥M)⁻¹, (⟨x, hxM⟩ : ↥M)⁻¹⁆ : ↥M) : G) :=
        congrArg Subtype.val hoeq
      rw [h2]
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]

theorem lemma221 {w v : G} (hv2 : orderOf v = 2) (hvM : v ∈ centralizer {w}) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (centralizer {w} ⊓ centralizer {v})) (hvJ : v ∈ J) {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {w})) : J ≤ L ∨ J ≤ coreActionKernel L := by
  obtain ⟨K₀, hK₀, -, -, hJK⟩ := T23.exists_pumpup_of_mem hv2 hvM hJ hvJ
  have hKc := T23.isTwoComponentIn_map_subtype hK₀
  have hJK' : J ≤ K₀.map (centralizer {w}).subtype := by
    intro x hx
    have hx' : (⟨x, (hJ.1 hx).1⟩ : ↥(centralizer ({w} : Set G))) ∈ J.subgroupOf _ := hx
    exact ⟨⟨x, (hJ.1 hx).1⟩, (hJK.1 hx').1, rfl⟩
  by_cases h : K₀.map (centralizer {w}).subtype = L
  · exact .inl (h ▸ hJK')
  · exact .inr (hJK'.trans (le_coreActionKernel_of_ne hKc hL h))

end CFSG.ComponentClassification.HarrisLit.T1
