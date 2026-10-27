module

public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute mem_zpowers_of_fixed)

variable {τ : Tag} {K : Type} [Field K]

theorem entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
    [Finite K]
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8) (hK : ringChar K = 2)
    (σ : K ≃+* K) : entrywiseFixedGroup τ σ = fixedFieldImage τ σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hT := (even_power_two_Cartan_root_diagonals_inner τ hτ K hK).2.2.2 σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup τ σ : Set (ModGL τ K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  refine mul_mem ?_ hj
  have hh' : h ∈ torusGroup τ K ⊓
      (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) := ⟨hh.1, hh.2.2⟩
  rw [hT] at hh'
  obtain ⟨t, ht, rfl⟩ := hh'
  have hle : torusGroup τ (fixSubfield σ) ≤ adjointGroup τ (fixSubfield σ) :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact ⟨t, hle ht, rfl⟩

@[expose] def fixedFieldImageEquiv
    (σ : K ≃+* K) :
    adjointGroup τ (fixSubfield σ) ≃* fixedFieldImage τ σ :=
  (adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ (baseChangeGL_injective _)

theorem even_card_fixedFieldImage
    [Finite K] [CharP K 2] (hr : 0 < τ.rank) (σ : K ≃+* K) :
    Even (Nat.card (fixedFieldImage τ σ)) := by
  set i : Fin τ.rank := ⟨0, hr⟩
  have hx : xUnit τ K i 1 ∈ fixedFieldImage τ σ := xUnit_mem_fixedFieldImage i (map_one σ)
  have h2 : (xUnit τ K i 1) ^ 2 = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, coe_xUnit, sq, xOp_mul_xOp (upTransport τ),
      show (1 : K) + 1 = 0 from CharTwo.add_self_eq_zero 1, xOp_zero, Units.val_one]
  have hne : xUnit τ K i 1 ≠ 1 := fun h => by
    have h' := congrArg Units.val h
    rw [coe_xUnit, Units.val_one, ← xOp_zero (τ := τ) (R := K) i] at h'
    exact one_ne_zero (xOp_injective i h')
  have hord : orderOf (⟨_, hx⟩ : fixedFieldImage τ σ) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using h2)
    · exact fun h => hne (congrArg Subtype.val h)
  have := orderOf_dvd_natCard (⟨_, hx⟩ : fixedFieldImage τ σ)
  rw [hord] at this
  exact even_iff_two_dvd.2 this

theorem units_map_entrywiseHom_refl {k : Type} [Field k] (h : ModGL τ k) :
    Units.map (entrywiseHom (RingEquiv.refl k).toRingHom) h = h :=
  Units.ext (entrywise_id (h : Module.End k (RootModule τ k)))

theorem units_map_entrywiseHom_baseChangeGL_restrict
    [Finite K] (φ σ : K ≃+* K)
    (j : ModGL τ (fixSubfield σ)) :
    Units.map (entrywiseHom φ.toRingHom) (baseChangeGL (fixSubfield σ).subtype j) =
      baseChangeGL (fixSubfield σ).subtype
        (Units.map (entrywiseHom (fixSubfieldRestrict φ σ).toRingHom) j) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL]
  congr 1

theorem eq_one_of_forall_fixedFieldImage_of_normalForm
    [Finite K] {σ : K ≃+* K}
    (hNFk : ∀ α : MulAut (adjointGroup τ (fixSubfield σ)),
      ∃! gψ : adjointGroup τ (fixSubfield σ) × (fixSubfield σ ≃+* fixSubfield σ),
        ∀ h : adjointGroup τ (fixSubfield σ), (α h : ModGL τ (fixSubfield σ)) =
          (gψ.1 : ModGL τ (fixSubfield σ)) *
            Units.map (entrywiseHom gψ.2.toRingHom) (h : ModGL τ (fixSubfield σ)) *
              (gψ.1 : ModGL τ (fixSubfield σ))⁻¹)
    {g : adjointGroup τ K} (hgJ : (g : ModGL τ K) ∈ fixedFieldImage τ σ) (φ : K ≃+* K)
    (hfix : ∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ →
      (g : ModGL τ K) * Units.map (entrywiseHom φ.toRingHom) (j : ModGL τ K) *
        (g : ModGL τ K)⁻¹ = j) :
    g = 1 ∧ ∀ c ∈ fixSubfield σ, φ c = c := by
  set k := fixSubfield σ
  set ι := baseChangeGL (τ := τ) k.subtype
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  obtain ⟨g', hg', hgg'⟩ := hgJ
  set ψ := fixSubfieldRestrict φ σ
  have hid : ∀ j' ∈ adjointGroup τ k,
      g' * Units.map (entrywiseHom ψ.toRingHom) j' * g'⁻¹ = j' := by
    intro j' hj'
    have hj'J : ι j' ∈ fixedFieldImage τ σ := ⟨j', hj', rfl⟩
    have hj'C : ι j' ∈ adjointGroup τ K := (fixedFieldImage_le hj'J).1
    have h1 := hfix ⟨ι j', hj'C⟩ hj'J
    change (g : ModGL τ K) * Units.map (entrywiseHom φ.toRingHom) (ι j') *
      (g : ModGL τ K)⁻¹ = ι j' at h1
    rw [← hgg', units_map_entrywiseHom_baseChangeGL_restrict, ← map_inv, ← map_mul,
      ← map_mul] at h1
    exact hιinj h1
  obtain ⟨q, -, hq⟩ := hNFk 1
  have h1 := hq (1, RingEquiv.refl k) fun h => by
    simp only [MulAut.one_apply, OneMemClass.coe_one, inv_one, one_mul, mul_one]
    exact (units_map_entrywiseHom_refl (h : ModGL τ k)).symm
  have h2 := hq (⟨g', hg'⟩, ψ) fun h => (hid h h.2).symm
  have h3 := h2.trans h1.symm
  have hψ1 : ψ = RingEquiv.refl k := congrArg Prod.snd h3
  have hg'1 : g' = 1 := congrArg (fun x => (x.1 : ModGL τ k)) h3
  refine ⟨Subtype.ext ?_, fun c hc => ?_⟩
  · rw [← hgg', hg'1, map_one]
    rfl
  · have h1 := congrArg (fun ψ' : k ≃+* k => (ψ' ⟨c, hc⟩ : K)) hψ1
    simp only [ψ] at h1
    exact h1

theorem canonical_field_full_centralizer_of_normalForm
    {e : ℕ} (he : 1 ≤ e) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (hNF : ∀ α : MulAut (adjointGroup τ K), ∃! gφ : adjointGroup τ K × (K ≃+* K),
      ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (gφ.1 : ModGL τ K) *
        Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL τ K) * (gφ.1 : ModGL τ K)⁻¹)
    (hNFk : ∀ α : MulAut (adjointGroup τ (fixSubfield σ)),
      ∃! gψ : adjointGroup τ (fixSubfield σ) × (fixSubfield σ ≃+* fixSubfield σ),
        ∀ h : adjointGroup τ (fixSubfield σ), (α h : ModGL τ (fixSubfield σ)) =
          (gψ.1 : ModGL τ (fixSubfield σ)) *
            Units.map (entrywiseHom gψ.2.toRingHom) (h : ModGL τ (fixSubfield σ)) *
              (gψ.1 : ModGL τ (fixSubfield σ))⁻¹)
    (hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ) :
    Nat.card (fixSubfield σ) = 2 ^ e ∧
      fixedFieldImage τ σ ≤ adjointGroup τ K ∧
      ((entrywiseAdjointAut τ σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (adjointGroup τ K).subtype = fixedFieldImage τ σ ∧
      (∃ ι : ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ≃*
          ↥(((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup τ K)) = MulAut.conj (j : adjointGroup τ K)) ∧
      (∀ β ∈ Subgroup.centralizer {entrywiseAdjointAut τ σ},
        ∃! gφ : adjointGroup τ K × (K ≃+* K), (gφ.1 : ModGL τ K) ∈ fixedFieldImage τ σ ∧
          ∀ h : adjointGroup τ K, (β h : ModGL τ K) = (gφ.1 : ModGL τ K) *
            Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL τ K) *
              (gφ.1 : ModGL τ K)⁻¹) ∧
      (∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ fixedFieldImage τ σ → ∀ φ : K ≃+* K,
        MulAut.conj g * entrywiseAdjointAut τ φ ∈
          Subgroup.centralizer {entrywiseAdjointAut τ σ}) ∧
      ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj ≤
        Subgroup.centralizer {entrywiseAdjointAut τ σ} ∧
      ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {entrywiseAdjointAut τ σ})).Normal ∧
      Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage τ σ).subgroupOf
            (adjointGroup τ K)).map MulAut.conj : Subgroup (MulAut (adjointGroup τ K))) :
              Set (MulAut (adjointGroup τ K))) =
        Subgroup.zpowers (entrywiseAdjointAut τ σ) := by
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have h2e : 2 ≤ 2 * e := by omega
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e / 2) := fun c => by
    rw [hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hσσ, hσ1, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.mem_zpowers_of_forall_fixed h2e
      ⟨e, two_mul e⟩ hK hσ'
  have hk : Nat.card (fixSubfield σ) = 2 ^ e := by
    obtain ⟨-, -, hcard⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two (by omega) hK
      (by rw [sq]; exact hσσ) hσ1
    rw [show 2 * e / 2 = e by omega] at hcard
    exact hcard
  set δ := entrywiseAdjointAut τ σ with hδ
  set J := fixedFieldImage τ σ with hJ
  have hJC : J ≤ adjointGroup τ K := fun j hj => (fixedFieldImage_le hj).1
  have hmemJ : ∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ J ↔ δ g = g := by
    intro g
    refine (Subgroup.ext_iff.1 hΓJ (g : ModGL τ K)).symm.trans ?_
    rw [mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  have hcommδ : ∀ φ : K ≃+* K, entrywiseAdjointAut τ φ * δ = δ * entrywiseAdjointAut τ φ :=
    fun φ => by rw [hδ, ← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, ringAut_commute]
  have hform : ∀ (β : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (φ : K ≃+* K),
      (∀ h : adjointGroup τ K, (β h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
      β = MulAut.conj g * entrywiseAdjointAut τ φ := fun β g φ h =>
    MulEquiv.ext fun x => Subtype.ext (by
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_entrywiseAdjointAut, Subgroup.coe_inv])
  have hconjδ : ∀ (g : adjointGroup τ K) (φ : K ≃+* K),
      δ * (MulAut.conj g * entrywiseAdjointAut τ φ) =
        MulAut.conj (δ g) * (δ * entrywiseAdjointAut τ φ) := fun g φ => by
    rw [← mul_assoc, mulAut_mul_conj, mul_assoc]
  have hcentJ : ∀ β ∈ Subgroup.centralizer {δ}, ∀ (g : adjointGroup τ K) (φ : K ≃+* K),
      (∀ h : adjointGroup τ K, (β h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
      (g : ModGL τ K) ∈ J := by
    intro β hβ g φ h
    have hβδ : δ * β = β * δ := Subgroup.mem_centralizer_iff.1 hβ δ (Set.mem_singleton δ)
    rw [hform β g φ h] at hβδ
    have e1 : MulAut.conj (δ g) * (δ * entrywiseAdjointAut τ φ) =
        MulAut.conj g * (δ * entrywiseAdjointAut τ φ) := by
      rw [← hconjδ, hβδ, mul_assoc, hcommδ]
    exact (hmemJ g).2 (hinj (mul_right_cancel e1))
  have hactor : ∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ J → ∀ φ : K ≃+* K,
      MulAut.conj g * entrywiseAdjointAut τ φ ∈ Subgroup.centralizer {δ} := by
    intro g hg φ
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    rw [Set.mem_singleton_iff.1 hx, hconjδ, (hmemJ g).1 hg, mul_assoc, ← hcommδ, ← mul_assoc]
  have hNδ : ((J.subgroupOf (adjointGroup τ K)).map MulAut.conj) ≤
      Subgroup.centralizer {δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
  refine ⟨hk, hJC, ?_,
    ⟨(J.subgroupOf (adjointGroup τ K)).equivMapOfInjective _ hinj, fun j => rfl⟩,
    fun β hβ => ?_, hactor, hNδ, ⟨fun n hn g => ?_⟩, le_antisymm (fun β hβ => ?_) ?_⟩
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
    have hgδ : δ * (g : MulAut (adjointGroup τ K)) = g * δ :=
      Subgroup.mem_centralizer_iff.1 g.2 δ (Set.mem_singleton δ)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut (adjointGroup τ K)) j, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc δ ((g : MulAut (adjointGroup τ K)) j) =
          (δ * (g : MulAut (adjointGroup τ K))) j := rfl
        _ = (g * δ : MulAut (adjointGroup τ K)) j := by rw [hgδ]
        _ = (g : MulAut (adjointGroup τ K)) (δ j) := rfl
        _ = (g : MulAut (adjointGroup τ K)) j := by
            rw [(hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  ·
    obtain ⟨hβδ, hβN⟩ := Subgroup.mem_inf.1 hβ
    obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF β
    have hgJ := hcentJ β hβδ g φ hgφ
    have hfix : ∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ J →
        (g : ModGL τ K) * Units.map (entrywiseHom φ.toRingHom) (j : ModGL τ K) *
          (g : ModGL τ K)⁻¹ = j := by
      intro j hj
      have hn : MulAut.conj j ∈ (J.subgroupOf (adjointGroup τ K)).map MulAut.conj :=
        ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      have h1 : MulAut.conj j * β = β * MulAut.conj j :=
        Subgroup.mem_centralizer_iff.1 hβN _ hn
      have h2 : MulAut.conj (β j) = MulAut.conj j := by
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      rw [← hgφ j, hinj h2]
    obtain ⟨hg1, hφk⟩ := eq_one_of_forall_fixedFieldImage_of_normalForm hNFk hgJ φ hfix
    have hφ : φ ∈ Subgroup.zpowers σ := mem_zpowers_of_fixed fun x hx => hφk x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hform β g (σ ^ n) hgφ, hg1, map_one, one_mul, hδ]
    exact (map_zpow (entrywiseAdjointAutHom (τ := τ)) σ n).symm
  ·
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)

theorem even_E7_E8_canonical_field_full_centralizer
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {e : ℕ}
    (he : 1 ≤ e) (K : Type) [Field K] (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    (∀ c : K, c ∈ fixSubfield σ ↔ c ^ 2 ^ e = c) ∧ Nat.card (fixSubfield σ) = 2 ^ e ∧
      fixedFieldImage τ σ ≤ adjointGroup τ K ∧
      ((entrywiseAdjointAut τ σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (adjointGroup τ K).subtype = fixedFieldImage τ σ ∧
      (Finite (fixedFieldImage τ σ) ∧ IsSimpleGroup (fixedFieldImage τ σ) ∧
        Even (Nat.card (fixedFieldImage τ σ)) ∧
        (τ = .E7 → ChevalleyExceptionalModel (fixedFieldImage τ σ) .E7 2 e) ∧
        (τ = .E8 → ChevalleyExceptionalModel (fixedFieldImage τ σ) .E8 2 e)) ∧
      (∃ ι : ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ≃*
          ↥(((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup τ K)) = MulAut.conj (j : adjointGroup τ K)) ∧
      (∀ β ∈ Subgroup.centralizer {entrywiseAdjointAut τ σ},
        ∃! gφ : adjointGroup τ K × (K ≃+* K), (gφ.1 : ModGL τ K) ∈ fixedFieldImage τ σ ∧
          ∀ h : adjointGroup τ K, (β h : ModGL τ K) = (gφ.1 : ModGL τ K) *
            Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL τ K) *
              (gφ.1 : ModGL τ K)⁻¹) ∧
      (∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ fixedFieldImage τ σ → ∀ φ : K ≃+* K,
        MulAut.conj g * entrywiseAdjointAut τ φ ∈
          Subgroup.centralizer {entrywiseAdjointAut τ σ}) ∧
      ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj ≤
        Subgroup.centralizer {entrywiseAdjointAut τ σ} ∧
      ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {entrywiseAdjointAut τ σ})).Normal ∧
      Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage τ σ).subgroupOf
            (adjointGroup τ K)).map MulAut.conj : Subgroup (MulAut (adjointGroup τ K))) :
              Set (MulAut (adjointGroup τ K))) =
        Subgroup.zpowers (entrywiseAdjointAut τ σ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
    (Or.inr (Or.inr (Or.inr hτ))) hchar σ
  obtain ⟨hNF, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form (f := 2 * e)
    (by omega) K hK τ hτ
  have h2e : 2 ≤ 2 * e := by omega
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e / 2) := fun c => by
    rw [hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hσσ, hσ1, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.mem_zpowers_of_forall_fixed h2e
      ⟨e, two_mul e⟩ hK hσ'
  have hk : Nat.card (fixSubfield σ) = 2 ^ e := by
    obtain ⟨-, -, hcard⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two (by omega) hK
      (by rw [sq]; exact hσσ) hσ1
    rw [show 2 * e / 2 = e by omega] at hcard
    exact hcard
  obtain ⟨hNFk, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form he
    (fixSubfield σ) hk τ hτ
  obtain ⟨-, hJC, hfixJ, hι, huniq, hactor, hNδ, hnormal, hcent⟩ :=
    canonical_field_full_centralizer_of_normalForm he hK σ hσ hNF hNFk hΓJ
  have hZk : Subgroup.center (adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  set eJ : fixedFieldImage τ σ ≃* AdjointQuotient τ (fixSubfield σ) :=
    (fixedFieldImageEquiv σ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm
  have hmodel7 : τ = .E7 → ChevalleyExceptionalModel (fixedFieldImage τ σ) .E7 2 e := by
    rintro rfl
    exact ⟨⟨Nat.prime_two, he, rfl⟩, fixSubfield σ, inferInstance, inferInstance, hk, ⟨eJ⟩⟩
  have hmodel8 : τ = .E8 → ChevalleyExceptionalModel (fixedFieldImage τ σ) .E8 2 e := by
    rintro rfl
    exact ⟨⟨Nat.prime_two, he, rfl⟩, fixSubfield σ, inferInstance, inferInstance, hk, ⟨eJ⟩⟩
  have hsimple : IsSimpleGroup (fixedFieldImage τ σ) := by
    rcases hτ with h | h
    · exact (CFSG.LieType.Simplicity.fam_e7_simplicity _ 2 e (hmodel7 h)).2
    · exact (CFSG.LieType.Simplicity.fam_e8_simplicity _ 2 e (hmodel8 h)).2
  have hrank : 0 < τ.rank := by
    rcases hτ with rfl | rfl <;> decide
  exact ⟨fun c => by rw [mem_fixSubfield, hσ], hk, hJC, hfixJ,
    ⟨inferInstance, hsimple, even_card_fixedFieldImage hrank σ, hmodel7, hmodel8⟩, hι, huniq,
    hactor,
    hNδ, hnormal, hcent⟩

end CFSG.LieType.Chevalley
