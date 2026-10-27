module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenFieldInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem torusElt_mem_fixedFieldImage {σ : K ≃+* K} (i : Fin Tag.G2.rank) {t : Kˣ}
    (ht : σ t = t) : torusElt .G2 K i t ∈ fixedFieldImage .G2 σ := by
  have hw : ∀ s : Kˣ, σ s = s → weylElt .G2 K i s ∈ fixedFieldImage .G2 σ := fun s hs => by
    rw [weylElt_eq_xUnit_mul]
    refine mul_mem (mul_mem (xUnit_mem_fixedFieldImage i hs)
      (yUnit_mem_fixedFieldImage i ?_)) (xUnit_mem_fixedFieldImage i hs)
    rw [map_neg, Units.val_inv_eq_inv_val, map_inv₀, hs]
  exact mul_mem (hw t ht) (hw (-1) (by simp))

theorem entrywiseFixedGroup_eq_fixedFieldImage [Finite K] (σ : K ≃+* K) :
    entrywiseFixedGroup .G2 σ = fixedFieldImage .G2 σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup .G2 K σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup .G2 σ : Set (ModGL .G2 K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, ⟨hH, hhΓ⟩, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  refine mul_mem ?_ hj
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hH
  have hfix : Units.map (entrywiseHom σ.toRingHom)
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) =
        torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ := hhΓ.2
  rw [map_mul, entrywise_torusElt, entrywise_torusElt] at hfix
  obtain ⟨e, he⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  have hprod : ∀ s : Fin Tag.G2.rank → Kˣ, (e s : ModGL .G2 K) =
      torusElt .G2 K g2ia (s g2ia) * torusElt .G2 K g2ir (s g2ir) := fun s => by
    rw [he]
    change (List.ofFn (n := 2) fun i => torusElt .G2 K i (s i)).prod = _
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    rfl
  have hinj := e.injective (a₁ := fun i => Units.map σ.toRingHom.toMonoidHom (if i = g2ia then t₁
    else t₂)) (a₂ := fun i => if i = g2ia then t₁ else t₂) (Subtype.ext (by
      rw [hprod, hprod]
      simp only [show g2ir ≠ g2ia by decide, ite_false, ite_true]
      exact hfix))
  have h1 := congrFun hinj g2ia
  have h2 := congrFun hinj g2ir
  simp only [show g2ir ≠ g2ia by decide, ite_false, ite_true] at h1 h2
  exact mul_mem (torusElt_mem_fixedFieldImage g2ia (congrArg Units.val h1))
    (torusElt_mem_fixedFieldImage g2ir (congrArg Units.val h2))

theorem units_map_entrywise_refl_k {k : Type} [Field k] (h : ModGL .G2 k) :
    Units.map (entrywiseHom (RingEquiv.refl k).toRingHom) h = h :=
  Units.ext (entrywise_id (h : Module.End k (RootModule .G2 k)))

theorem entrywise_baseChangeGL_restrict [Finite K] (φ σ : K ≃+* K)
    (j : ModGL .G2 (fixSubfield σ)) :
    Units.map (entrywiseHom φ.toRingHom) (baseChangeGL (fixSubfield σ).subtype j) =
      baseChangeGL (fixSubfield σ).subtype
        (Units.map (entrywiseHom (fixSubfieldRestrict φ σ).toRingHom) j) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL]
  congr 1

theorem ringEquiv_eq_refl_of_card_two {k : Type} [Field k] (hk : Nat.card k = 2) (ψ : k ≃+* k) :
    ψ = RingEquiv.refl k := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  refine RingEquiv.ext fun c => ?_
  by_cases hc : c = 0
  · rw [hc, map_zero]
    rfl
  · have : Fintype k := Fintype.ofFinite k
    have h01 : ∀ x : k, x = 0 ∨ x = 1 := by
      intro x
      have hx : x ^ 2 = x := by
        have := FiniteField.pow_card x
        rwa [← Nat.card_eq_fintype_card, hk] at this
      have h' : x * (x - 1) = 0 := by linear_combination hx
      rcases mul_eq_zero.1 h' with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.1 h)
    rcases h01 c with h | h
    · exact absurd h hc
    · rw [h, map_one]
      rfl

theorem eq_one_of_forall_fixedFieldImage {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e))
    {σ : K ≃+* K} (hk : Nat.card (fixSubfield σ) = 2 ^ e) {g : adjointGroup .G2 K}
    (hgJ : (g : ModGL .G2 K) ∈ fixedFieldImage .G2 σ) (φ : K ≃+* K)
    (hfix : ∀ j : adjointGroup .G2 K, (j : ModGL .G2 K) ∈ fixedFieldImage .G2 σ →
      (g : ModGL .G2 K) * Units.map (entrywiseHom φ.toRingHom) (j : ModGL .G2 K) *
        (g : ModGL .G2 K)⁻¹ = j) :
    g = 1 ∧ ∀ c ∈ fixSubfield σ, φ c = c := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  set k := fixSubfield σ
  have : Finite k := Subtype.finite
  set ι := baseChangeGL (τ := .G2) k.subtype
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  obtain ⟨g', hg', hgg'⟩ := hgJ
  set ψ := fixSubfieldRestrict φ σ
  have hid : ∀ j' ∈ adjointGroup .G2 k,
      g' * Units.map (entrywiseHom ψ.toRingHom) j' * g'⁻¹ = j' := by
    intro j' hj'
    have hj'J : ι j' ∈ fixedFieldImage .G2 σ := ⟨j', hj', rfl⟩
    have hj'C : ι j' ∈ adjointGroup .G2 K := fixedFieldImage_le hj'J |>.1
    have h1 := hfix ⟨ι j', hj'C⟩ hj'J
    change (g : ModGL .G2 K) * Units.map (entrywiseHom φ.toRingHom) (ι j') *
      (g : ModGL .G2 K)⁻¹ = ι j' at h1
    rw [← hgg', entrywise_baseChangeGL_restrict, ← map_inv, ← map_mul, ← map_mul] at h1
    exact hιinj h1
  have hψ : ψ = RingEquiv.refl k ∧ g' = 1 := by
    rcases Nat.lt_or_ge 1 e with he2 | he1'
    ·
      obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form he2 k hk
      obtain ⟨q, -, hq⟩ := hNF 1
      have h1 := hq (1, RingEquiv.refl k) fun h => by
        simp only [MulAut.one_apply, OneMemClass.coe_one, inv_one, one_mul, mul_one]
        exact (units_map_entrywise_refl_k (h : ModGL .G2 k)).symm
      have h2 := hq (⟨g', hg'⟩, ψ) fun h => (hid h h.2).symm
      have h3 := h2.trans h1.symm
      exact ⟨congrArg Prod.snd h3, congrArg (fun x => (x.1 : ModGL .G2 k)) h3⟩
    ·
      have he1 : e = 1 := le_antisymm he1' he
      have hk2 : Nat.card k = 2 := by rw [hk, he1, pow_one]
      have hψ1 := ringEquiv_eq_refl_of_card_two hk2 ψ
      refine ⟨hψ1, ?_⟩
      have hZ : Subgroup.center (adjointGroup .G2 k) = ⊥ := center_adjointGroup_eq_bot
      have hc : (⟨g', hg'⟩ : adjointGroup .G2 k) ∈ Subgroup.center (adjointGroup .G2 k) := by
        refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
        have h1 := hid j j.2
        rw [hψ1, units_map_entrywise_refl_k] at h1
        change (j : ModGL .G2 k) * g' = g' * j
        rw [← mul_inv_eq_iff_eq_mul.1 h1]
      rw [hZ, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
  obtain ⟨hψ1, hg'1⟩ := hψ
  refine ⟨Subtype.ext ?_, fun c hc => ?_⟩
  · rw [← hgg', hg'1, map_one]
    rfl
  · have h1 := congrArg (fun ψ' : k ≃+* k => (ψ' ⟨c, hc⟩ : K)) hψ1
    simp only [ψ] at h1
    exact h1

theorem even_G2_canonical_field_full_centralizer {e : ℕ} (he : 1 ≤ e) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    (∀ c : K, c ∈ fixSubfield σ ↔ c ^ 2 ^ e = c) ∧ Nat.card (fixSubfield σ) = 2 ^ e ∧
      fixedFieldImage .G2 σ ≤ adjointGroup .G2 K ∧
      ((entrywiseAdjointAut .G2 σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (adjointGroup .G2 K).subtype = fixedFieldImage .G2 σ ∧
      (∃ ι : ↥((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)) ≃*
          ↥(((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup .G2 K)) = MulAut.conj (j : adjointGroup .G2 K)) ∧
      (∀ β ∈ Subgroup.centralizer {entrywiseAdjointAut .G2 σ},
        ∃! gφ : adjointGroup .G2 K × (K ≃+* K), (gφ.1 : ModGL .G2 K) ∈ fixedFieldImage .G2 σ ∧
          ∀ h : adjointGroup .G2 K, (β h : ModGL .G2 K) = (gφ.1 : ModGL .G2 K) *
            Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL .G2 K) *
              (gφ.1 : ModGL .G2 K)⁻¹) ∧
      ((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map MulAut.conj ≤
        Subgroup.centralizer {entrywiseAdjointAut .G2 σ} ∧
      ((((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {entrywiseAdjointAut .G2 σ})).Normal ∧
      Subgroup.centralizer {entrywiseAdjointAut .G2 σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage .G2 σ).subgroupOf
            (adjointGroup .G2 K)).map MulAut.conj : Subgroup (MulAut (adjointGroup .G2 K))) :
              Set (MulAut (adjointGroup .G2 K))) =
        Subgroup.zpowers (entrywiseAdjointAut .G2 σ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have h2e : 2 ≤ 2 * e := by omega
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e / 2) := fun c => by
    rw [hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hσσ, hσ1, -⟩ := SpChain.mem_zpowers_of_forall_fixed h2e ⟨e, two_mul e⟩ hK hσ'
  have hk : Nat.card (fixSubfield σ) = 2 ^ e := by
    obtain ⟨-, -, hcard⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two (by omega) hK
      (by rw [sq]; exact hσσ) hσ1
    rw [show 2 * e / 2 = e by omega] at hcard
    exact hcard
  set δ := entrywiseAdjointAut .G2 σ with hδ
  set J := fixedFieldImage .G2 σ with hJ
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage σ
  have hJC : J ≤ adjointGroup .G2 K := fun j hj => (fixedFieldImage_le hj).1
  have hmemJ : ∀ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ J ↔ δ g = g := by
    intro g
    rw [hJ, ← hΓJ, mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form h2e K hK
  have hcommδ : ∀ φ : K ≃+* K, entrywiseAdjointAut .G2 φ * δ = δ * entrywiseAdjointAut .G2 φ :=
    fun φ => by rw [hδ, ← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, ringAut_commute]
  have hform : ∀ (β : MulAut (adjointGroup .G2 K)) (g : adjointGroup .G2 K) (φ : K ≃+* K),
      (∀ h : adjointGroup .G2 K, (β h : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom φ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) →
      β = MulAut.conj g * entrywiseAdjointAut .G2 φ := fun β g φ h =>
    MulEquiv.ext fun x => Subtype.ext (by
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_entrywiseAdjointAut, Subgroup.coe_inv])
  have hcentJ : ∀ β ∈ Subgroup.centralizer {δ}, ∀ (g : adjointGroup .G2 K) (φ : K ≃+* K),
      (∀ h : adjointGroup .G2 K, (β h : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom φ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) →
      (g : ModGL .G2 K) ∈ J := by
    intro β hβ g φ h
    have hβδ : δ * β = β * δ := Subgroup.mem_centralizer_iff.1 hβ δ (Set.mem_singleton δ)
    rw [hform β g φ h] at hβδ
    have e1 : MulAut.conj (δ g) * (δ * entrywiseAdjointAut .G2 φ) =
        MulAut.conj g * (δ * entrywiseAdjointAut .G2 φ) := by
      calc MulAut.conj (δ g) * (δ * entrywiseAdjointAut .G2 φ) =
          δ * (MulAut.conj g * entrywiseAdjointAut .G2 φ) := by
            rw [← mul_assoc, ← mulAut_mul_conj, mul_assoc]
        _ = MulAut.conj g * entrywiseAdjointAut .G2 φ * δ := hβδ
        _ = MulAut.conj g * (δ * entrywiseAdjointAut .G2 φ) := by rw [mul_assoc, hcommδ]
    exact (hmemJ g).2 (hinj (mul_right_cancel e1))
  have hNδ : ((J.subgroupOf (adjointGroup .G2 K)).map MulAut.conj) ≤
      Subgroup.centralizer {δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
  refine ⟨fun c => by rw [mem_fixSubfield, hσ], hk, hJC, ?_,
    ⟨(J.subgroupOf (adjointGroup .G2 K)).equivMapOfInjective _ hinj, fun j => rfl⟩,
    fun β hβ => ?_, hNδ, ⟨fun n hn g => ?_⟩, le_antisymm (fun β hβ => ?_) ?_⟩
  ·
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hmemJ g).2 hg
    · intro hx
      exact ⟨⟨x, hJC hx⟩, (hmemJ _).1 hx, rfl⟩
  ·
    obtain ⟨⟨g, φ⟩, hgφ, huniq⟩ := hNF β
    exact ⟨(g, φ), ⟨hcentJ β hβ g φ hgφ, hgφ⟩, fun q hq => huniq q hq.2⟩
  ·
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_subgroupOf.1 hn
    rw [SetLike.mem_coe] at hj
    have hgδ : δ * (g : MulAut (adjointGroup .G2 K)) = g * δ :=
      Subgroup.mem_centralizer_iff.1 g.2 δ (Set.mem_singleton δ)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut (adjointGroup .G2 K)) j, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc δ ((g : MulAut (adjointGroup .G2 K)) j) =
          (δ * (g : MulAut (adjointGroup .G2 K))) j := rfl
        _ = (g * δ : MulAut (adjointGroup .G2 K)) j := by rw [hgδ]
        _ = (g : MulAut (adjointGroup .G2 K)) (δ j) := rfl
        _ = (g : MulAut (adjointGroup .G2 K)) j := by
            rw [(hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  ·
    obtain ⟨hβδ, hβN⟩ := Subgroup.mem_inf.1 hβ
    obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF β
    have hgJ := hcentJ β hβδ g φ hgφ
    have hfix : ∀ j : adjointGroup .G2 K, (j : ModGL .G2 K) ∈ J →
        (g : ModGL .G2 K) * Units.map (entrywiseHom φ.toRingHom) (j : ModGL .G2 K) *
          (g : ModGL .G2 K)⁻¹ = j := by
      intro j hj
      have hn : MulAut.conj j ∈ (J.subgroupOf (adjointGroup .G2 K)).map MulAut.conj :=
        ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      have h1 : MulAut.conj j * β = β * MulAut.conj j :=
        Subgroup.mem_centralizer_iff.1 hβN _ hn
      have h2 : MulAut.conj (β j) = MulAut.conj j := by
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      rw [← hgφ j, hinj h2]
    obtain ⟨hg1, hφk⟩ := eq_one_of_forall_fixedFieldImage he hK hk hgJ φ hfix
    have hφ : φ ∈ Subgroup.zpowers σ := mem_zpowers_of_fixed fun x hx => hφk x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hform β g (σ ^ n) hgφ, hg1, map_one, one_mul, hδ]
    exact (map_zpow (entrywiseAdjointAutHom (τ := .G2)) σ n).symm
  ·
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)

end CFSG.ComponentClassification.UnbalancedCatalog
