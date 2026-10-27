module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperOver
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace OddQuot

section Surjective

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

omit [Finite X] [Finite Y] in
theorem mem_fusionZStar_iff {L : Type*} [Group L] {l : L} :
    l ∈ Open.fusionZStar L ↔ ∀ m : L, ⁅l, m⁆ ∈ pPrimeCore 2 L := by
  rw [← UnbalancingLocal.fusionOddCore_eq_pPrimeCore]
  change QuotientGroup.mk' (Open.fusionOddCore L) l ∈ center (L ⧸ Open.fusionOddCore L) ↔ _
  rw [mem_center_iff]
  constructor
  · intro h m
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (h _).symm
  · intro h q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hm := (QuotientGroup.eq_one_iff _).mpr (h m)
    rw [← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm.symm

theorem comap_pPrimeCore_of_surjective (f : X →* Y) (hf : Function.Surjective f)
    (hker : ¬ 2 ∣ Nat.card f.ker) : (pPrimeCore 2 Y).comap f = pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (prime_complement_kernel_core_preimage f hf hker).1

theorem comap_fusionZStar_of_surjective (f : X →* Y) (hf : Function.Surjective f)
    (hker : ¬ 2 ∣ Nat.card f.ker) : (Open.fusionZStar Y).comap f = Open.fusionZStar X := by
  ext x
  rw [mem_comap, mem_fusionZStar_iff, mem_fusionZStar_iff,
    ← comap_pPrimeCore_of_surjective f hf hker]
  constructor
  · intro h m
    rw [mem_comap, map_commutatorElement]
    exact h (f m)
  · intro h y
    obtain ⟨m, rfl⟩ := hf y
    have h1 := h m
    rwa [mem_comap, map_commutatorElement] at h1

theorem comap_oddTwoCore_of_surjective (f : X →* Y) (hf : Function.Surjective f)
    (hker : ¬ 2 ∣ Nat.card f.ker) : (oddTwoCore Y).comap f = oddTwoCore X := by
  have hO := comap_pPrimeCore_of_surjective f hf hker
  set φ := (QuotientGroup.mk' (pPrimeCore 2 Y)).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφk : pPrimeCore 2 X = φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hO]
  set e := QuotientGroup.liftEquiv (pPrimeCore 2 X) hφs hφk
  have hcomp : φ = e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 X)) := by
    ext x
    rfl
  unfold oddTwoCore
  rw [comap_comap, ← hφ, hcomp, ← comap_comap]
  congr 1
  rw [show (pCore 2 (Y ⧸ pPrimeCore 2 Y)).comap e.toMonoidHom =
      (pCore 2 (Y ⧸ pPrimeCore 2 Y)).map e.symm.toMonoidHom from
    (map_equiv_eq_comap_symm e.symm _).symm, pCore_map_iso]

theorem nonempty_fusionZStar_equiv_of_surjective (f : X →* Y) (hf : Function.Surjective f)
    (hker : ¬ 2 ∣ Nat.card f.ker) :
    Nonempty (X ⧸ Open.fusionZStar X ≃* Y ⧸ Open.fusionZStar Y) := by
  set φ := (QuotientGroup.mk' (Open.fusionZStar Y)).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφk : Open.fusionZStar X = φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_fusionZStar_of_surjective f hf hker]
  exact ⟨QuotientGroup.liftEquiv _ hφs hφk⟩

theorem nonempty_pPrimeCore_equiv_of_surjective (f : X →* Y) (hf : Function.Surjective f)
    (hker : ¬ 2 ∣ Nat.card f.ker) :
    Nonempty (X ⧸ pPrimeCore 2 X ≃* Y ⧸ pPrimeCore 2 Y) := by
  set φ := (QuotientGroup.mk' (pPrimeCore 2 Y)).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφk : pPrimeCore 2 X = φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_pPrimeCore_of_surjective f hf hker]
  exact ⟨QuotientGroup.liftEquiv _ hφs hφk⟩

end Surjective

section Subgroups

variable {H H' : Type*} [Group H] [Group H'] [Finite H] [Finite H']

theorem nonempty_quotient_fusionZStar_equiv (φ : H →* H') (hφ : ¬ 2 ∣ Nat.card φ.ker)
    (X : Subgroup H) :
    Nonempty (X ⧸ Open.fusionZStar X ≃* X.map φ ⧸ Open.fusionZStar (X.map φ)) :=
  nonempty_fusionZStar_equiv_of_surjective (φ.subgroupMap X) (φ.subgroupMap_surjective X)
    (not_two_dvd_card_ker_subgroupMap φ hφ X)

end Subgroups

section Invariance

variable {G G' : Type*} [Group G] [Group G']

theorem map_centralizer_singleton_equiv (e : G ≃* G') (g : G) :
    (centralizer ({g} : Set G)).map e.toMonoidHom = centralizer ({e g} : Set G') := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h1
  · intro h
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h

theorem map_centralizer_equiv (e : G ≃* G') (L : Subgroup G) :
    (centralizer (L : Set G)).map e.toMonoidHom =
      centralizer ((L.map e.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h z hz
    obtain ⟨l, hl, rfl⟩ := mem_map.mp hz
    have h1 := congrArg e (h l hl)
    simpa only [map_mul, MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom] using h1
  · intro h l hl
    apply e.injective
    have h1 := h (e l) (mem_map_of_mem e.toMonoidHom hl)
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h1

theorem isStandardSubgroup_map_equiv (e : G ≃* G') {L : Subgroup G}
    (hL : IsStandardSubgroup L) : IsStandardSubgroup (L.map e.toMonoidHom) :=
  CFSG.IsStandardSubgroup.map_mulEquiv e hL

theorem isComponent_subgroupOf_map_equiv (e : G ≃* G') {A C : Subgroup G} (hAC : A ≤ C)
    (h : IsComponent (A.subgroupOf C)) :
    IsComponent ((A.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom)) := by
  have h1 := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent
    (C.equivMapOfInjective e.toMonoidHom e.injective) h
  have h2 : (A.subgroupOf C).map (C.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom) := by
    rw [show (C.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      e.toMonoidHom.subgroupMap C from rfl]
    exact map_subgroupOf_subgroupMap e.toMonoidHom hAC
  rwa [h2] at h1

theorem lieModel_of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (h : Blueprint.LieModel G t n p f) :
    Blueprint.LieModel G' t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem isSporadic_of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {s : TauCeti.SporadicName} (h : Blueprint.NativeSporadic.IsSporadic G s) :
    Blueprint.NativeSporadic.IsSporadic G' s :=
  let ⟨e'⟩ := h
  ⟨e.symm.trans e'⟩

theorem gsRestricted_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : GSRestricted Y) : GSRestricted Y' := by
  have hL : ∀ {t n p f}, Blueprint.LieModel Y t n p f → Blueprint.LieModel Y' t n p f :=
    fun h => lieModel_of_equiv e h
  have hS : ∀ {s}, Blueprint.NativeSporadic.IsSporadic Y s →
      Blueprint.NativeSporadic.IsSporadic Y' s := fun h => isSporadic_of_equiv e h
  unfold GSRestricted at h ⊢
  rcases h with ⟨p, f, hp, hp2, hf, hq, hm⟩ | ⟨p, f, hp, hp2, hf, hm⟩ | ⟨m, hm1, hm⟩ | h
  · exact Or.inl ⟨p, f, hp, hp2, hf, hq, hL hm⟩
  · refine Or.inr (Or.inl ⟨p, f, hp, hp2, hf, ?_⟩)
    rcases hm with h | h | h | h | h | h | h
    · exact Or.inl (hL h)
    · exact Or.inr (Or.inl (hL h))
    · exact Or.inr (Or.inr (Or.inl (hL h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hL h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hL h))))))
  · exact Or.inr (Or.inr (Or.inl ⟨m, hm1, hL hm⟩))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rcases h with h | h | h | h | h | h | h | ⟨n, hn, ⟨e'⟩⟩ | h | h | h | h | h | h | h | h
    · exact Or.inl (hL h)
    · exact Or.inr (Or.inl (hL h))
    · exact Or.inr (Or.inr (Or.inl (hL h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hL h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (hS h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (hS h))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl (hS h)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl (hS h))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hS h)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hS h))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hS h)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hS h)))))))))))))))

theorem smallType_of_equiv {G G' : Type} [Group G] [Group G'] {J : Subgroup G}
    {J' : Subgroup G'} (e₁ : J ⧸ pPrimeCore 2 J ≃* J' ⧸ pPrimeCore 2 J')
    (e₂ : J ⧸ Open.fusionZStar J ≃* J' ⧸ Open.fusionZStar J') (h : SmallType J) :
    SmallType J' := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, hq, hm⟩ | hm
  · exact Or.inl ⟨e₁.symm.trans e⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hq, lieModel_of_equiv e₁ hm⟩)
  · exact Or.inr (Or.inr (lieModel_of_equiv e₂ hm))

theorem isKGroupCat_of_surjective {X Y : Type} [Group X] [Group Y] (hX : SectionRank.IsKGroupCat X)
    (f : X →* Y) (hf : Function.Surjective f) : SectionRank.IsKGroupCat Y :=
  (hX.quotient f.ker).of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm

theorem kProper_quotient {X : Type} [Group X] (hX : Assembly.KProper Blueprint.Catalog X)
    (N : Subgroup X) [N.Normal] : Assembly.KProper Blueprint.Catalog (X ⧸ N) :=
  CatalogueKProperOver.kProper_quotient (fun e h => SectionRank.catalog_of_mulEquiv e h) hX N

end Invariance

section Wbar

variable {H : Type*} [Group H] [Finite H]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

@[expose] def normalizerMap (B : Subgroup H) : ↥(normalizer (B : Set H)) →*
    ↥(normalizer ((B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H))) :=
  ((π).comp (normalizer (B : Set H)).subtype).codRestrict _ fun w =>
    le_normalizer_map π (mem_map_of_mem π w.2)

omit [Finite H] in
theorem normalizerMap_coe (B : Subgroup H) (w : ↥(normalizer (B : Set H))) :
    (normalizerMap B w : H ⧸ pPrimeCore 2 H) = π w := rfl

theorem normalizerMap_surjective {B : Subgroup H} (hB : IsPGroup 2 B) :
    Function.Surjective (normalizerMap B) := by
  rintro ⟨z, hz⟩
  rw [normalizer_map_eq hB] at hz
  obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
  exact ⟨⟨w, hw⟩, rfl⟩

theorem not_two_dvd_card_ker_normalizerMap (B : Subgroup H) :
    ¬ 2 ∣ Nat.card (normalizerMap B).ker := by
  rw [normalizerMap, MonoidHom.ker_codRestrict]
  exact not_two_dvd_card_ker_domRestrict π not_two_dvd_card_ker _

omit [Finite H] in
theorem map_subgroupOf_normalizerMap {B Y : Subgroup H} (hY : Y ≤ normalizer (B : Set H)) :
    (Y.subgroupOf (normalizer (B : Set H))).map (normalizerMap B) =
      (Y.map π).subgroupOf (normalizer ((B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H))) := by
  ext ⟨z, hz⟩
  rw [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨w, hw, hwz⟩
    exact mem_map.mpr ⟨w, hw, congrArg Subtype.val hwz⟩
  · intro hzY
    obtain ⟨y, hy, hyz⟩ := mem_map.mp hzY
    exact ⟨⟨y, hY hy⟩, hy, Subtype.ext hyz⟩

theorem exists_wbar_equiv {B : Subgroup H} (hB : IsPGroup 2 B) :
    ∃ e : Wbar B ≃* Wbar (B.map π), ∀ w : ↥(normalizer (B : Set H)),
      e (wbarMk B w) = wbarMk (B.map π) (normalizerMap B w) := by
  set φ := (wbarMk (B.map π)).comp (normalizerMap B) with hφ
  have hφs : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (normalizerMap_surjective hB)
  have hφk : oddTwoCore ↥(normalizer (B : Set H)) = φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      comap_oddTwoCore_of_surjective _ (normalizerMap_surjective hB)
        (not_two_dvd_card_ker_normalizerMap B)]
  exact ⟨QuotientGroup.liftEquiv _ hφs hφk, fun w => rfl⟩

omit [Finite H] in
theorem map_wbarImage {B Y : Subgroup H} (e : Wbar B ≃* Wbar (B.map π))
    (he : ∀ w : ↥(normalizer (B : Set H)),
      e (wbarMk B w) = wbarMk (B.map π) (normalizerMap B w))
    (hY : Y ≤ normalizer (B : Set H)) :
    (wbarImage B Y).map e.toMonoidHom = wbarImage (B.map π) (Y.map π) := by
  unfold wbarImage
  rw [← map_subgroupOf_normalizerMap hY, map_map, map_map]
  congr 1
  ext w
  exact he w

end Wbar

end OddQuot

end CFSG.ComponentClassification.GSThmB
