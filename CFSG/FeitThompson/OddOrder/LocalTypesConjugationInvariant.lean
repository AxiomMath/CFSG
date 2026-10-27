module

public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
public import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
public import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G G' : Type*} [Group G] [Group G']

theorem image_conj_image (e : G ≃* G') (z : G) (D : Set G) :
    MulAut.conj (e z) '' (e '' D) = e '' (MulAut.conj z '' D) := by
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr' fun x => ?_
  simp [MulAut.conj_apply]

theorem map_normalizer_image (e : G ≃* G') (D : Set G) :
    (Subgroup.normalizer D).map (e : G →* G') = Subgroup.normalizer (e '' D) := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.coe_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_normalizer_iff_conj_image_eq] at hz ⊢
    rw [image_conj_image, hz]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    rw [Subgroup.mem_normalizer_iff_conj_image_eq] at hy
    refine e.injective.image_injective ?_
    rw [← image_conj_image e (e.symm y) D]
    simpa using hy

theorem map_normalizer_coe (e : G ≃* G') (A : Subgroup G) :
    (Subgroup.normalizer (A : Set G)).map (e : G →* G')
      = Subgroup.normalizer ((A.map (e : G →* G') : Subgroup G') : Set G') := by
  rw [map_normalizer_image, Subgroup.coe_map]
  rfl

theorem map_centralizer_coe (e : G ≃* G') (A : Subgroup G) :
    (Subgroup.centralizer (A : Set G)).map (e : G →* G')
      = Subgroup.centralizer ((A.map (e : G →* G') : Subgroup G') : Set G') := by
  rw [Subgroup.coe_map, show ((e : G →* G')) = e.toMonoidHom from rfl, map_centralizer]
  rfl

theorem map_centralizer_singleton (e : G ≃* G') (x : G) :
    (Subgroup.centralizer {x}).map (e : G →* G') = Subgroup.centralizer {e x} := by
  have h := map_centralizer e ({x} : Set G)
  rw [Set.image_singleton] at h
  exact h

theorem map_map_subtype_comm' (e : G ≃* G') (M : Subgroup G) (K : Subgroup M) :
    (K.map M.subtype).map (e : G →* G')
      = (K.map (e.subgroupMap M : M →* ↥(M.map (e : G →* G')))).map
          (M.map (e : G →* G')).subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_subgroupOf_subgroupMap (e : G ≃* G') (A K : Subgroup G) :
    (A.subgroupOf K).map (e.subgroupMap K : K →* ↥(K.map (e : G →* G'))) =
      (A.map (e : G →* G')).subgroupOf (K.map (e : G →* G')) := by
  refine Subgroup.map_injective (K.map (e : G →* G')).subtype_injective ?_
  rw [Subgroup.subgroupOf_map_subtype, ← map_map_subtype_comm', Subgroup.subgroupOf_map_subtype,
    Subgroup.map_inf _ _ _ e.injective]

theorem isComplement'_map (e : G ≃* G') {H K : Subgroup G} (h : H.IsComplement' K) :
    (H.map (e : G →* G')).IsComplement' (K.map (e : G →* G')) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, ← Subgroup.map_inf _ _ _ e.injective, disjoint_iff.1 h.disjoint,
      Subgroup.map_bot]
  · rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, h.mul_eq]
    simp [Set.image_univ, e.surjective.range_eq]

theorem isMulCommutative_of_map_isMulCommutative (e : G ≃* G') {E : Subgroup G}
    (h : IsMulCommutative ↥(E.map (e : G →* G'))) : IsMulCommutative ↥E := by
  have hE : E = (E.map (e : G →* G')).map (e.symm : G' →* G) := by
    rw [Subgroup.map_map]; ext x; simp
  have := h
  rw [hE]
  exact Subgroup.map_isMulCommutative _ _

theorem IsTIWithNormalizer.map {D : Set G} {L : Subgroup G} (h : IsTIWithNormalizer D L)
    (e : G ≃* G') : IsTIWithNormalizer (e '' D) (L.map (e : G →* G')) where
  nonempty := h.nonempty.image _
  one_notMem := by
    rintro ⟨x, hx, hx1⟩
    rw [show (1 : G') = e 1 by simp] at hx1
    exact h.one_notMem (e.injective hx1 ▸ hx)
  normalizer_eq := by rw [← map_normalizer_image, h.normalizer_eq]
  disjoint_conj_image y hy := by
    have hy' : e.symm y ∉ L := fun hc => hy ⟨e.symm y, hc, by simp⟩
    have hd := (Set.disjoint_image_iff (f := (e : G → G')) e.injective).2
      (h.disjoint_conj_image _ hy')
    rwa [← image_conj_image, MulEquiv.apply_symm_apply] at hd

theorem image_cyclicTIset (e : G ≃* G') (W₁ W₂ : Subgroup G) :
    e '' cyclicTIset W₁ W₂ = cyclicTIset (W₁.map (e : G →* G')) (W₂.map (e : G →* G')) := by
  ext y
  simp only [Set.mem_image, mem_cyclicTIset, ← Subgroup.map_sup, Subgroup.mem_map,
    MonoidHom.coe_coe]
  constructor
  · rintro ⟨x, ⟨hx, hx1, hx2⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun ⟨z, hz, hzx⟩ => hx1 (e.injective hzx ▸ hz),
      fun ⟨z, hz, hzx⟩ => hx2 (e.injective hzx ▸ hz)⟩
  · rintro ⟨⟨x, hx, rfl⟩, h1, h2⟩
    exact ⟨x, ⟨hx, fun hc => h1 ⟨x, hc, rfl⟩, fun hc => h2 ⟨x, hc, rfl⟩⟩, rfl⟩

theorem IsInternalDirectProduct.map {X U V : Subgroup G} (h : IsInternalDirectProduct X U V)
    (e : G ≃* G') : IsInternalDirectProduct (X.map (e : G →* G')) (U.map (e : G →* G'))
      (V.map (e : G →* G')) where
  left_le := Subgroup.map_mono h.left_le
  right_le := Subgroup.map_mono h.right_le
  coe_eq_mul := by
    rw [Subgroup.coe_map, Subgroup.coe_map, Subgroup.coe_map, h.coe_eq_mul, Set.image_mul]
  inf_eq_bot := by
    rw [← Subgroup.map_inf _ _ _ e.injective, h.inf_eq_bot, Subgroup.map_bot]
  commutator_eq_bot := by
    rw [← Subgroup.map_commutator, h.commutator_eq_bot, Subgroup.map_bot]

theorem map_map_subtype_hallCore_comm (e : G ≃* G') (M : Subgroup G) :
    ((hallCore ↥M).map M.subtype).map (e : G →* G')
      = (hallCore ↥(M.map (e : G →* G'))).map (M.map (e : G →* G')).subtype := by
  rw [map_map_subtype_comm', map_hallCore]

theorem map_map_subtype_fittingRaw_comm [Finite G] [Finite G'] (e : G ≃* G') (M : Subgroup G) :
    ((fittingRaw ↥M).map M.subtype).map (e : G →* G')
      = (fittingRaw ↥(M.map (e : G →* G'))).map (M.map (e : G →* G')).subtype := by
  rw [map_map_subtype_comm', map_fittingRaw_of_mulEquiv]

noncomputable def hallCoreMulEquivMap (e : G ≃* G') (M : Subgroup G) :
    ↥(hallCore ↥M) ≃* ↥(hallCore ↥(M.map (e : G →* G'))) :=
  ((hallCore ↥M).equivMapOfInjective _ (e.subgroupMap M).injective).trans
    (MulEquiv.subgroupCongr (map_hallCore (e.subgroupMap M)))

theorem natCard_hallCore_map (e : G ≃* G') (M : Subgroup G) :
    Nat.card (hallCore ↥(M.map (e : G →* G'))) = Nat.card (hallCore ↥M) :=
  (Nat.card_congr (hallCoreMulEquivMap e M).toEquiv).symm

theorem map_subtype_hallCore_of_eq (e : G ≃* G') {K : Subgroup G} {K' : Subgroup G'}
    (hK : K.map (e : G →* G') = K') :
    (hallCore ↥K').map K'.subtype = ((hallCore ↥K).map K.subtype).map (e : G →* G') := by
  subst hK; exact (map_map_subtype_hallCore_comm e K).symm

theorem image_hallCoreSharp (e : G ≃* G') (M : Subgroup G) :
    e '' hallCoreSharp M = hallCoreSharp (M.map (e : G →* G')) := by
  rw [hallCoreSharp_eq, hallCoreSharp_eq, ← map_map_subtype_hallCore_comm, Subgroup.coe_map,
    Set.image_sdiff e.injective]
  simp

theorem image_fittingRawSharp [Finite G] [Finite G'] (e : G ≃* G') (M : Subgroup G) :
    e '' fittingRawSharp M = fittingRawSharp (M.map (e : G →* G')) := by
  rw [fittingRawSharp_eq, fittingRawSharp_eq, ← map_map_subtype_fittingRaw_comm,
    Subgroup.coe_map, Set.image_sdiff e.injective]
  simp

theorem isCyclic_pComplCore_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (r : ℕ) (h : IsCyclic (pComplCore r X)) : IsCyclic (pComplCore r Y) := by
  have hmap : (pComplCore r X).map (e : X →* Y) = pComplCore r Y := by
    rw [pComplCore_eq_piCore, pComplCore_eq_piCore, map_piCore_of_mulEquiv]
  exact (MulEquiv.isCyclic ((e.subgroupMap (pComplCore r X)).trans
    (MulEquiv.subgroupCongr hmap))).1 h

theorem natCard_pCore_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (r : ℕ) : Nat.card (pCore r Y) = Nat.card (pCore r X) := by
  rw [← map_pCore_of_mulEquiv r e, Subgroup.card_map_of_injective e.injective]

theorem IsFrobeniusType.map [Finite G] [Finite G'] {E : Subgroup G} (h : IsFrobeniusType G E)
    (e : G ≃* G') : IsFrobeniusType G' (E.map (e : G →* G')) := by
  have hH : (hallCore G).map (e : G →* G') = hallCore G' := map_hallCore e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hH, ← Subgroup.map_bot (f := (e : G →* G'))]
    exact (Subgroup.map_lt_map_iff_of_injective e.injective).2 h.bot_lt_hallCore
  · rw [← hH, show (⊤ : Subgroup G') = (⊤ : Subgroup G).map (e : G →* G') from
      (Subgroup.map_top_of_surjective _ e.surjective).symm]
    exact (Subgroup.map_lt_map_iff_of_injective e.injective).2 h.hallCore_lt_top
  · rw [← hH]; exact isComplement'_map e h.isComplement'
  · obtain ⟨E₁, hle, hnorm, hcomm, hcent⟩ := h.exists_abelian_normal
    refine ⟨E₁.map (e : G →* G'), Subgroup.map_mono hle, ?_, ?_, ?_⟩
    · rw [← map_subgroupOf_subgroupMap]
      exact hnorm.map _ (e.subgroupMap E).surjective
    · have := hcomm; exact Subgroup.map_isMulCommutative E₁ _
    · intro y hy hy1
      rw [← hH] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx1 : x ≠ 1 := fun hcx => hy1 (by simp [hcx])
      rw [MonoidHom.coe_coe] at *
      rw [← map_centralizer_singleton, ← Subgroup.map_inf _ _ _ e.injective]
      exact Subgroup.map_mono (hcent x hx hx1)
  · obtain ⟨E₀, hle, hexp, hcent⟩ := h.exists_exponent_eq
    refine ⟨E₀.map (e : G →* G'), Subgroup.map_mono hle, ?_, ?_⟩
    · rw [← Monoid.exponent_eq_of_mulEquiv (e.subgroupMap E₀),
        ← Monoid.exponent_eq_of_mulEquiv (e.subgroupMap E)]
      exact hexp
    · intro y hy hy1
      obtain ⟨x, hx, rfl⟩ := hy
      have hx1 : x ≠ 1 := fun hcx => hy1 (by simp [hcx])
      rw [MonoidHom.coe_coe] at *
      rw [← hH, ← map_centralizer_singleton, ← Subgroup.map_inf _ _ _ e.injective,
        hcent x hx hx1, Subgroup.map_bot]

theorem isFrobeniusType_map_subgroupOf_of_eq [Finite G] [Finite G'] {K : Subgroup G}
    {K' : Subgroup G'} (e : G ≃* G') (hK : K.map (e : G →* G') = K') {E : Subgroup G}
    (h : IsFrobeniusType ↥K (E.subgroupOf K)) :
    IsFrobeniusType ↥K' ((E.map (e : G →* G')).subgroupOf K') := by
  subst hK
  have h2 := h.map (e.subgroupMap K)
  rwa [map_subgroupOf_subgroupMap] at h2

theorem IsFrobeniusType.conj [Finite G] {M : Subgroup G} {E : Subgroup M}
    (h : IsFrobeniusType ↥M E) (g : G) :
    IsFrobeniusType ↥(M.map (MulAut.conj g⁻¹ : G →* G))
      (E.map ((MulAut.conj g⁻¹ : G ≃* G).subgroupMap M :
        M →* ↥(M.map (MulAut.conj g⁻¹ : G →* G)))) :=
  h.map ((MulAut.conj g⁻¹ : G ≃* G).subgroupMap M)

theorem IsWitnessedPConfiguration.map [Finite G] [Finite G'] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) (e : G ≃* G') :
    IsWitnessedPConfiguration (M.map (e : G →* G')) (E.map (e : G →* G'))
      (W₁.map (e : G →* G')) (W₂.map (e : G →* G')) := by
  have hcomm : ∀ A B : Subgroup G, (⁅A, B⁆ : Subgroup G).map (e : G →* G')
      = ⁅A.map (e : G →* G'), B.map (e : G →* G')⁆ := fun A B => Subgroup.map_commutator A B _
  have hHall := map_map_subtype_hallCore_comm e M
  have hFit := map_map_subtype_fittingRaw_comm e M
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (⊤ : Subgroup G') = (⊤ : Subgroup G).map (e : G →* G') from
      (Subgroup.map_top_of_surjective _ e.surjective).symm]
    exact (Subgroup.map_lt_map_iff_of_injective e.injective).2 hc.lt_top
  · rw [← Subgroup.map_bot (f := (e : G →* G'))]
    exact fun h => hc.ne_bot_W₁ (Subgroup.map_injective e.injective h)
  · exact (MulEquiv.isCyclic (e.subgroupMap W₁)).1 hc.isCyclic_W₁
  · rw [Subgroup.card_map_of_injective e.injective,
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hc.hall_W₁
  · rw [← hcomm, ← Subgroup.map_sup, hc.sup_commutator_W₁]
  · rw [disjoint_iff, ← hcomm, ← Subgroup.map_inf _ _ _ e.injective,
      disjoint_iff.1 hc.disjoint_commutator_W₁, Subgroup.map_bot]
  · exact (Group.isNilpotent_congr (e.subgroupMap E)).1 hc.isNilpotent_E
  · rw [← hcomm]; exact Subgroup.map_mono hc.le_commutator_E
  · have h := Subgroup.map_mono (f := (e : G →* G')) hc.le_normalizer_E
    rwa [map_normalizer_coe] at h
  · rw [← hHall, ← Subgroup.map_sup, hc.sup_hallCore_E, hcomm]
  · rw [disjoint_iff, ← hHall, ← Subgroup.map_inf _ _ _ e.injective,
      disjoint_iff.1 hc.disjoint_hallCore_E, Subgroup.map_bot]
  · rw [← hHall]
    exact fun h => hc.not_isCyclic_hallCore
      ((MulEquiv.isCyclic (e.subgroupMap ((hallCore ↥M).map M.subtype))).2 h)
  · have h := Subgroup.map_mono (f := (e : G →* G')) hc.commutator_commutator_le_fittingRaw
    rwa [hFit, hcomm, hcomm] at h
  · rw [← hHall, ← hFit]
    have key : (M.map (e : G →* G') ⊓ Subgroup.centralizer
        ((((hallCore ↥M).map M.subtype).map (e : G →* G') : Subgroup G') : Set G'))
        = (M ⊓ Subgroup.centralizer (((hallCore ↥M).map M.subtype : Subgroup G) : Set G)).map
            (e : G →* G') := by
      rw [Subgroup.map_inf _ _ _ e.injective, map_centralizer_coe]
    rw [key, Subgroup.coe_map (f := (e : G →* G')) ((fittingRaw ↥M).map M.subtype),
      Subgroup.coe_map (f := (e : G →* G')) ((hallCore ↥M).map M.subtype),
      Subgroup.coe_map (f := (e : G →* G'))
        (M ⊓ Subgroup.centralizer (((hallCore ↥M).map M.subtype : Subgroup G) : Set G)),
      ← Set.image_mul, hc.coe_fittingRaw_eq]
  · have h := Subgroup.map_mono (f := (e : G →* G')) hc.fittingRaw_le_commutator
    rwa [hFit, hcomm] at h
  · rw [← Subgroup.map_bot (f := (e : G →* G'))]
    exact fun h => hc.ne_bot_W₂ (Subgroup.map_injective e.injective h)
  · exact (MulEquiv.isCyclic (e.subgroupMap W₂)).1 hc.isCyclic_W₂
  · have h := Subgroup.map_mono (f := (e : G →* G')) hc.le_W₂
    rwa [Subgroup.map_inf _ _ _ e.injective, hHall, hcomm, hcomm] at h
  · intro y hy hy1
    obtain ⟨x, hx, rfl⟩ := hy
    have hx1 : x ≠ 1 := fun hcx => hy1 (by simp [hcx])
    rw [MonoidHom.coe_coe] at *
    rw [← hcomm, ← map_centralizer_singleton, ← Subgroup.map_inf _ _ _ e.injective,
      hc.inf_centralizer_eq_W₂ x hx hx1]
  · rw [← Subgroup.map_sup]; exact hc.isInternalDirectProduct_sup.map e
  · rw [← Subgroup.map_sup, ← image_cyclicTIset]
    exact hc.isTIWithNormalizer_cyclicTIset.map e

theorem IsWitnessedPConfiguration.conj [Finite G] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) (g : G) :
    IsWitnessedPConfiguration (M.map (MulAut.conj g⁻¹ : G →* G))
      (E.map (MulAut.conj g⁻¹ : G →* G)) (W₁.map (MulAut.conj g⁻¹ : G →* G))
      (W₂.map (MulAut.conj g⁻¹ : G →* G)) :=
  hc.map (MulAut.conj g⁻¹)

theorem IsTypeI.map [Finite G] [Finite G'] {M : Subgroup G} (h : IsTypeI M) (e : G ≃* G') :
    IsTypeI (M.map (e : G →* G')) := by
  set eM : ↥M ≃* ↥(M.map (e : G →* G')) := e.subgroupMap M with heM
  have hH : (hallCore ↥M).map (eM : ↥M →* ↥(M.map (e : G →* G')))
      = hallCore ↥(M.map (e : G →* G')) := map_hallCore eM
  set eH : ↥(hallCore ↥M) ≃* ↥(hallCore ↥(M.map (e : G →* G'))) := hallCoreMulEquivMap e M
  have hcard := natCard_hallCore_map e M
  obtain ⟨E, hE, halt⟩ := h.exists_isFrobeniusType
  refine ⟨?_, E.map (eM : ↥M →* ↥(M.map (e : G →* G'))), hE.map eM, ?_⟩
  · rw [show (⊤ : Subgroup G') = (⊤ : Subgroup G).map (e : G →* G') from
      (Subgroup.map_top_of_surjective _ e.surjective).symm]
    exact (Subgroup.map_lt_map_iff_of_injective e.injective).2 h.lt_top
  · rcases halt with hi | ⟨habel, hrank⟩ | ⟨hexp, hcyc⟩
    · refine Or.inl ?_
      have := hi.map e
      rwa [image_hallCoreSharp] at this
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · have := habel; rw [← hH]; exact Subgroup.map_isMulCommutative _ _
      · rw [← maxElementaryAbelianPRank_eq_of_mulEquiv eH]; exact hrank
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · intro r hr
        rw [hcard] at hr
        rw [← Monoid.exponent_eq_of_mulEquiv (eM.subgroupMap E)]
        exact hexp r hr
      · obtain ⟨r, hr, hrcyc⟩ := hcyc
        exact ⟨r, by rwa [hcard], isCyclic_pComplCore_of_mulEquiv eH r hrcyc⟩

theorem IsTypeI.conj [Finite G] {M : Subgroup G} (h : IsTypeI M) (g : G) :
    IsTypeI (M.map (MulAut.conj g⁻¹ : G →* G)) :=
  h.map (MulAut.conj g⁻¹)

theorem IsPConfigurationIIToIV.map [Finite G] [Finite G'] {M E W₁ W₂ : Subgroup G}
    (hc : IsPConfigurationIIToIV M E W₁ W₂) (e : G ≃* G') :
    IsPConfigurationIIToIV (M.map (e : G →* G')) (E.map (e : G →* G'))
      (W₁.map (e : G →* G')) (W₂.map (e : G →* G')) where
  isWitnessedPConfiguration := hc.isWitnessedPConfiguration.map e
  prime_natCard_W₁ := by
    rw [Subgroup.card_map_of_injective e.injective]; exact hc.prime_natCard_W₁
  isTIWithNormalizer_fittingRawSharp := by
    have h := hc.isTIWithNormalizer_fittingRawSharp.map e
    rwa [image_fittingRawSharp] at h

theorem IsTypeII.map [Finite G] [Finite G'] {M : Subgroup G} (h : IsTypeII M) (e : G ≃* G') :
    IsTypeII (M.map (e : G →* G')) := by
  obtain ⟨E, W₁, W₂, hc, hE, habel, hnorm, hfrob, hhall⟩ := h.exists_isPConfigurationIIToIV
  have hcomm : (⁅M, M⁆ : Subgroup G).map (e : G →* G')
      = ⁅M.map (e : G →* G'), M.map (e : G →* G')⁆ := Subgroup.map_commutator M M _
  refine ⟨E.map (e : G →* G'), W₁.map (e : G →* G'), W₂.map (e : G →* G'), hc.map e, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]; exact hE
  · have := habel; exact Subgroup.map_isMulCommutative _ _
  · intro hle
    refine hnorm ?_
    have h2 : (Subgroup.normalizer (E : Set G)).map (e : G →* G') ≤ M.map (e : G →* G') := by
      rw [map_normalizer_coe]; exact hle
    exact (Subgroup.map_le_map_iff_of_injective e.injective).1 h2
  · exact isFrobeniusType_map_subgroupOf_of_eq e hcomm hfrob
  · rw [map_subtype_hallCore_of_eq e hcomm, ← map_map_subtype_hallCore_comm e M, hhall]

theorem IsTypeII.conj [Finite G] {M : Subgroup G} (h : IsTypeII M) (g : G) :
    IsTypeII (M.map (MulAut.conj g⁻¹ : G →* G)) :=
  h.map (MulAut.conj g⁻¹)

theorem IsTypeIII.map [Finite G] [Finite G'] {M : Subgroup G} (h : IsTypeIII M) (e : G ≃* G') :
    IsTypeIII (M.map (e : G →* G')) := by
  obtain ⟨E, W₁, W₂, hc, hE, habel, hnorm⟩ := h.exists_isPConfigurationIIToIV
  refine ⟨E.map (e : G →* G'), W₁.map (e : G →* G'), W₂.map (e : G →* G'), hc.map e, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]; exact hE
  · have := habel; exact Subgroup.map_isMulCommutative _ _
  · rw [← map_normalizer_coe]; exact Subgroup.map_mono hnorm

theorem IsTypeIII.conj [Finite G] {M : Subgroup G} (h : IsTypeIII M) (g : G) :
    IsTypeIII (M.map (MulAut.conj g⁻¹ : G →* G)) :=
  h.map (MulAut.conj g⁻¹)

theorem IsTypeIV.map [Finite G] [Finite G'] {M : Subgroup G} (h : IsTypeIV M) (e : G ≃* G') :
    IsTypeIV (M.map (e : G →* G')) := by
  obtain ⟨E, W₁, W₂, hc, habel, hnorm⟩ := h.exists_isPConfigurationIIToIV
  refine ⟨E.map (e : G →* G'), W₁.map (e : G →* G'), W₂.map (e : G →* G'), hc.map e, ?_, ?_⟩
  · exact fun hcm => habel (isMulCommutative_of_map_isMulCommutative e hcm)
  · rw [← map_normalizer_coe]; exact Subgroup.map_mono hnorm

theorem IsTypeIV.conj [Finite G] {M : Subgroup G} (h : IsTypeIV M) (g : G) :
    IsTypeIV (M.map (MulAut.conj g⁻¹ : G →* G)) :=
  h.map (MulAut.conj g⁻¹)

theorem IsTypeV.map [Finite G] [Finite G'] {M : Subgroup G} (h : IsTypeV M) (e : G ≃* G') :
    IsTypeV (M.map (e : G →* G')) := by
  set eH : ↥(hallCore ↥M) ≃* ↥(hallCore ↥(M.map (e : G →* G'))) := hallCoreMulEquivMap e M
  have hcard := natCard_hallCore_map e M
  obtain ⟨W₁, W₂, hc, halt⟩ := h.exists_isWitnessedPConfiguration
  have hc' : IsWitnessedPConfiguration (M.map (e : G →* G')) ⊥ (W₁.map (e : G →* G'))
      (W₂.map (e : G →* G')) := by
    have := hc.map e
    rwa [Subgroup.map_bot] at this
  have hW₁ : Nat.card (W₁.map (e : G →* G')) = Nat.card W₁ :=
    Subgroup.card_map_of_injective e.injective
  refine ⟨W₁.map (e : G →* G'), W₂.map (e : G →* G'), hc', ?_⟩
  rcases halt with hi | ⟨r, hr, hrcyc, hdvd⟩ | ⟨r, hr, hrcyc, hcard3, hdvd⟩
  · refine Or.inl ?_
    have := hi.map e
    rwa [image_hallCoreSharp] at this
  · exact Or.inr (Or.inl ⟨r, by rwa [hcard], isCyclic_pComplCore_of_mulEquiv eH r hrcyc,
      by rwa [hW₁]⟩)
  · exact Or.inr (Or.inr ⟨r, by rwa [hcard], isCyclic_pComplCore_of_mulEquiv eH r hrcyc,
      by rw [natCard_pCore_of_mulEquiv eH]; exact hcard3, by rwa [hW₁]⟩)

theorem IsTypeV.conj [Finite G] {M : Subgroup G} (h : IsTypeV M) (g : G) :
    IsTypeV (M.map (MulAut.conj g⁻¹ : G →* G)) :=
  h.map (MulAut.conj g⁻¹)

end

end CFSG.FeitThompson
