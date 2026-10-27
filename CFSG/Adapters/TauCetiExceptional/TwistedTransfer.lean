module

public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open scoped commutatorElement

theorem commutatorElement_mul_mul_of_mem_center {G : Type*} [Group G] (a b : G) {z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : ∀ g, z * g * z⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
  have h2 : ∀ g, w * g * w⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hw g, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [h1]; group
    _ = ⁅a, b⁆ := by rw [h2, commutatorElement_def]

theorem map_subtype_commutator {G : Type*} [Group G] (H : Subgroup G) :
    (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable {t : TwistTag} {L : Type} [Field L] {Fr : L →+* L} {G : Type} [Group G]

structure IsTwistedIsogeny (t : TwistTag) (L : Type) [Field L] (Fr : L →+* L) (F : G →* G)
    (π : G →* ModGL t.tag L) : Prop where
  mem : ∀ g, π g ∈ adjointGroup t.tag L
  surj : ∀ x ∈ adjointGroup t.tag L, ∃ g, π g = x
  ker : ∀ g, π g = 1 → g ∈ Subgroup.center G
  comm : ∀ g, π (F g) = twistHom t L Fr (π g)

namespace IsTwistedIsogeny

variable {F : G →* G} {π : G →* ModGL t.tag L} (h : IsTwistedIsogeny t L Fr F π)
include h

theorem map_fixedSubgroup_le :
    (fixedSubgroup F).map π ≤ twistedFixedGroup t L Fr := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨h.mem g, ?_⟩
  change twistHom t L Fr (π g) = π g
  rw [← h.comm, mem_fixedSubgroup.1 hg]

theorem inv_mul_mem_center {g : G} (hg : π g ∈ twistedFixedGroup t L Fr) :
    g⁻¹ * F g ∈ Subgroup.center G := by
  apply h.ker
  have hg2 : twistHom t L Fr (π g) = π g := hg.2
  rw [map_mul, map_inv, h.comm, hg2, inv_mul_cancel]

theorem commutator_le_map :
    ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ ≤ (fixedSubgroup F).map π := by
  rw [Subgroup.commutator_le]
  intro r₁ hr₁ r₂ hr₂
  obtain ⟨g₁, rfl⟩ := h.surj r₁ hr₁.1
  obtain ⟨g₂, rfl⟩ := h.surj r₂ hr₂.1
  refine ⟨⁅g₁, g₂⁆, ?_, map_commutatorElement π g₁ g₂⟩
  change F ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆
  rw [map_commutatorElement]
  have e₁ : F g₁ = g₁ * (g₁⁻¹ * F g₁) := by group
  have e₂ : F g₂ = g₂ * (g₂⁻¹ * F g₂) := by group
  rw [e₁, e₂, commutatorElement_mul_mul_of_mem_center _ _ (h.inv_mul_mem_center hr₁)
    (h.inv_mul_mem_center hr₂)]

theorem map_commutator_fixedSubgroup
    (hperf : ⁅⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆,
      ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆⁆ =
        ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆) :
    ⁅fixedSubgroup F, fixedSubgroup F⁆.map π =
      ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ := by
  rw [Subgroup.map_commutator]
  refine le_antisymm (Subgroup.commutator_mono h.map_fixedSubgroup_le h.map_fixedSubgroup_le) ?_
  calc ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ = _ := hperf.symm
    _ ≤ _ := Subgroup.commutator_mono h.commutator_le_map h.commutator_le_map

@[expose] def derivedMap
    (hperf : ⁅⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆,
      ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆⁆ =
        ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆) :
    ↥(commutator ↥(fixedSubgroup F)) →*
      ↥⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ :=
  ((π.comp (fixedSubgroup F).subtype).comp (commutator ↥(fixedSubgroup F)).subtype).codRestrict _
    fun x => by
      rw [← h.map_commutator_fixedSubgroup hperf, ← map_subtype_commutator]
      exact ⟨((x : ↥(fixedSubgroup F)) : G), ⟨x, x.2, rfl⟩, rfl⟩

theorem coe_derivedMap
    (hperf : ⁅⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆,
      ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆⁆ =
        ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆)
    (x : ↥(commutator ↥(fixedSubgroup F))) :
    (h.derivedMap hperf x : ModGL t.tag L) = π ((x : ↥(fixedSubgroup F)) : G) :=
  rfl

theorem derivedMap_surjective
    (hperf : ⁅⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆,
      ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆⁆ =
        ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆) :
    Function.Surjective (h.derivedMap hperf) := by
  rintro ⟨y, hy⟩
  rw [← h.map_commutator_fixedSubgroup hperf, ← map_subtype_commutator, Subgroup.map_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

@[expose] def derivedCentralQuotientEquiv
    (hperf : ⁅⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆,
      ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆⁆ =
        ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆)
    (hZ : Subgroup.center ↥⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ = ⊥) :
    TauCeti.DerivedCentralQuotient ↥(fixedSubgroup F) ≃*
      ↥⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ :=
  MulEquiv.ofBijective
    (DerivedCentralQuotient.lift (h.derivedMap hperf) (h.derivedMap_surjective hperf) hZ)
    ⟨(injective_iff_map_eq_one _).2 fun q hq => by
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [DerivedCentralQuotient.lift_mk] at hq
        have hc := h.ker _ (congrArg Subtype.val hq)
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
        rw [Subgroup.mem_center_iff] at hc
        intro y
        exact Subtype.ext (Subtype.ext (hc ((y : ↥(fixedSubgroup F)) : G))),
      DerivedCentralQuotient.lift_surjective _ _ _⟩

end IsTwistedIsogeny

section Native

variable {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}

@[expose] def sigmaEquiv [Finite K] (σ : K →+* K) : K ≃+* K :=
  RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩

theorem sigmaEquiv_toRingHom [Finite K] (σ : K →+* K) : (sigmaEquiv σ).toRingHom = σ :=
  RingHom.ext fun _ => rfl

theorem center_graphFixedRootGroup_eq_bot
    [Finite K] (σ : K →+* K) :
    Subgroup.center ↥(graphFixedRootGroup t K σ) = ⊥ := by
  have h := exceptional_fixed_center_trivial t K (sigmaEquiv σ)
  rwa [sigmaEquiv_toRingHom] at h

omit [Field K] in
theorem finite_of_card (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ t.order) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')

@[expose] def nativeEquiv
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ t.order)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup t K σ) ≃*
      ↥(graphFixedRootGroup t K σ) :=
  have := finite_of_card hp hK
  (QuotientGroup.congr _ _
      (MulEquiv.subgroupCongr (finite_fixed_root_group_perfect t hp hf K hK σ hσ).2.2.1)
      (Subgroup.map_center_eq _)).trans
    ((QuotientGroup.quotientMulEquivOfEq (center_graphFixedRootGroup_eq_bot σ)).trans
      QuotientGroup.quotientBot)

variable (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)

@[expose] def rootGroupEquivDerived
    (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ t.order) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    ↥(graphFixedRootGroup t K σ) ≃* ↥⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ :=
  ((graphFixedRootGroup t K σ).equivMapOfInjective _
    (baseChangeGL_injective (algebraMap K L))).trans
    (MulEquiv.subgroupCongr
      (exceptional_ambient_twisted_Frobenius_fixed_normalizer t hp hf K hK σ hσ L Fr
        hFr).2.2.2.2.1.symm)

theorem commutator_derived_eq
    (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ t.order) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    ⁅⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆,
      ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆⁆ =
        ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ := by
  rw [(exceptional_ambient_twisted_Frobenius_fixed_normalizer t hp hf K hK σ hσ L Fr
    hFr).2.2.2.2.1, ← Subgroup.map_commutator,
    (finite_fixed_root_group_perfect t hp hf K hK σ hσ).1]

theorem center_derived_eq_bot
    (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ t.order) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    Subgroup.center ↥⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ = ⊥ := by
  have := finite_of_card hp hK
  rw [← Subgroup.map_center_eq (rootGroupEquivDerived L Fr hp hf hK hσ hFr),
    center_graphFixedRootGroup_eq_bot σ, Subgroup.map_bot]

theorem nonempty_derivedCentralQuotient_equiv
    (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ t.order) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) {F : G →* G} {π : G →* ModGL t.tag L}
    (h : IsTwistedIsogeny t L Fr F π) :
    Nonempty (TauCeti.DerivedCentralQuotient ↥(fixedSubgroup F) ≃*
      CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup t K σ)) :=
  ⟨((h.derivedCentralQuotientEquiv (commutator_derived_eq L Fr hp hf hK hσ hFr)
    (center_derived_eq_bot L Fr hp hf hK hσ hFr)).trans
      (rootGroupEquivDerived L Fr hp hf hK hσ hFr).symm).trans
        (nativeEquiv hp hf hK hσ).symm⟩

end Native

end CFSG.TauCetiBridge.Twisted
