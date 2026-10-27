module

public import CFSG.CharacterTheory.Wreathed.CentralizerFusion
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v

variable {G : Type u} [Group G]

@[expose] def centralizerOddCore (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Subgroup (involutionCentralizer n S e) :=
  CFSG.oddCore (involutionCentralizer n S e)

instance centralizerOddCore_normal (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : (centralizerOddCore n S e).Normal := by
  unfold centralizerOddCore
  infer_instance

@[expose] def centralizerOddCoreQuotient (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Type u :=
  involutionCentralizer n S e ⧸ centralizerOddCore n S e

instance centralizerOddCoreQuotient_group (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Group (centralizerOddCoreQuotient n S e) :=
  inferInstanceAs (Group (involutionCentralizer n S e ⧸ centralizerOddCore n S e))

instance centralizerOddCoreQuotient_finite [Finite G] (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Finite (centralizerOddCoreQuotient n S e) :=
  inferInstanceAs (Finite (involutionCentralizer n S e ⧸ centralizerOddCore n S e))

@[expose] def centralizerOddCoreMap (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    involutionCentralizer n S e →* centralizerOddCoreQuotient n S e :=
  QuotientGroup.mk' (centralizerOddCore n S e)

theorem centralizerOddCoreMap_surjective (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Function.Surjective (centralizerOddCoreMap n S e) :=
  QuotientGroup.mk'_surjective _

@[expose] def centralizerFullCenter (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (involutionCentralizer n S e) :=
  modelCenter (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)

@[expose] def centralizerFullCenterImage (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (centralizerOddCoreQuotient n S e) :=
  (centralizerFullCenter n hn S e).map (centralizerOddCoreMap n S e)

@[expose] def centralizerOddCoreSylow [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Sylow 2 (centralizerOddCoreQuotient n S e) :=
  (centralizerSylow n hn S e).mapSurjective (centralizerOddCoreMap_surjective n S e)

theorem centralizerFullCenter_eq_zpowers (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenter n hn S e = Subgroup.zpowers
      (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
        (Original.a (2 ^ n))) := by
  exact MonoidHom.map_zpowers _ _

instance centralizerFullCenter_isCyclic (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsCyclic (centralizerFullCenter n hn S e) := by
  rw [centralizerFullCenter_eq_zpowers]
  infer_instance

theorem centralizerFullCenter_le_sylow (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenter n hn S e ≤ (centralizerSylow n hn S e :
      Subgroup (involutionCentralizer n S e)) := by
  rw [centralizerFullCenter_eq_zpowers]
  exact Subgroup.zpowers_le.mpr ((centralizerCoordinates n hn S e).symm _).property

theorem centralizerFullCenter_le_sylow_centralizer (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenter n hn S e ≤ Subgroup.centralizer
      (centralizerSylow n hn S e : Set (involutionCentralizer n S e)) := by
  rintro a ⟨w, hw, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hwcenter : w ∈ Subgroup.center (Wreath (2 ^ n)) :=
    (wreath_center_involution_and_quaternion_coordinates n hn).center ▸ hw
  have h := congrArg
    (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e))
    (Subgroup.mem_center_iff.mp hwcenter
      (centralizerCoordinates n hn S e ⟨s, hs⟩))
  rw [map_mul, map_mul] at h
  simpa only [wreathModelHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, Subgroup.coe_subtype] using h

theorem centralizerFullCenter_weakly_closed [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∀ a ∈ centralizerFullCenter n hn S e, ∀ g : involutionCentralizer n S e,
      g⁻¹ * a * g ∈ (centralizerSylow n hn S e :
        Subgroup (involutionCentralizer n S e)) → g⁻¹ * a * g = a := by
  rintro a ⟨w, hw, rfl⟩ g hg
  exact centralizer_original_center_weakly_closed n hn S e w hw g hg

theorem centralizerFullCenterImage_le_center_and_factorization [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenterImage n hn S e ≤
      Subgroup.center (centralizerOddCoreQuotient n S e) ∧
    (∀ g : involutionCentralizer n S e, ∃ r ∈ centralizerOddCore n S e,
      ∃ c ∈ Subgroup.centralizer (centralizerFullCenter n hn S e :
        Set (involutionCentralizer n S e)), g = r * c) := by
  exact cyclic_weakly_closed_central_sylow_subgroup_central_mod_odd_core
    (centralizerSylow n hn S e) (centralizerFullCenter n hn S e)
    (centralizerFullCenter_le_sylow n hn S e)
    (centralizerFullCenter_le_sylow_centralizer n hn S e)
    (centralizerFullCenter_weakly_closed n hn S e)


theorem centralizerFullCenter_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (centralizerFullCenter n hn S e) = 2 ^ n := by
  rw [centralizerFullCenter_eq_zpowers, Nat.card_zpowers,
    orderOf_injective _ (wreathModelHom_injective _ _), Original.orderOf_a]

theorem centralizerOddCore_card_odd [Finite G] (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Odd (Nat.card (centralizerOddCore n S e)) :=
  weakClosure_oddCore_card (involutionCentralizer n S e)

theorem centralizerOddCore_inf_sylow_eq_bot [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerOddCore n S e ⊓ (centralizerSylow n hn S e :
      Subgroup (involutionCentralizer n S e)) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (centralizerSylow n hn S e).isPGroup'.exists_card_eq
  apply disjoint_iff.mp
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hk]
  exact (Nat.coprime_two_right.mpr (centralizerOddCore_card_odd n S e)).pow_right k

theorem centralizerOddCore_inf_fullCenter_eq_bot [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerOddCore n S e ⊓ centralizerFullCenter n hn S e = ⊥ := by
  apply le_antisymm _ bot_le
  exact (inf_le_inf_left _ (centralizerFullCenter_le_sylow n hn S e)).trans
    (centralizerOddCore_inf_sylow_eq_bot n hn S e).le

theorem centralizerOddCoreMap_sylow_injective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective ((centralizerOddCoreMap n S e).domRestrict
      (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e))) := by
  apply (((centralizerOddCoreMap n S e).domRestrict
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e))).ker_eq_bot_iff).mp
  have hk : (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e :=
    QuotientGroup.ker_mk' _
  rw [MonoidHom.ker_domRestrict, hk]
  change (centralizerOddCore n S e).subgroupOf
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) = ⊥
  exact Subgroup.subgroupOf_eq_bot.mpr
    (disjoint_iff.mpr (centralizerOddCore_inf_sylow_eq_bot n hn S e))

theorem centralizerOddCoreMap_sylow_subgroupMap_injective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective ((centralizerOddCoreMap n S e).subgroupMap
      (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e))) := by
  intro a b hab
  apply centralizerOddCoreMap_sylow_injective n hn S e
  exact congrArg Subtype.val hab

@[expose] def centralizerOddCoreSylowEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerSylow n hn S e ≃* centralizerOddCoreSylow n hn S e :=
  MulEquiv.ofBijective ((centralizerOddCoreMap n S e).subgroupMap
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)))
    ⟨centralizerOddCoreMap_sylow_subgroupMap_injective n hn S e,
      (centralizerOddCoreMap n S e).subgroupMap_surjective _⟩

theorem centralizerOddCoreSylowEquiv_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (s : centralizerSylow n hn S e) :
    (centralizerOddCoreSylowEquiv n hn S e s : centralizerOddCoreQuotient n S e) =
      centralizerOddCoreMap n S e s := rfl

@[expose] def centralizerOddCoreCoordinates [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerOddCoreSylow n hn S e ≃* Wreath (2 ^ n) :=
  (centralizerOddCoreSylowEquiv n hn S e).symm.trans (centralizerCoordinates n hn S e)

theorem centralizerOddCoreModelHom_comp [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) =
      (centralizerOddCoreMap n S e).comp
        (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)) := by
  ext w
  exact centralizerOddCoreSylowEquiv_coe n hn S e
    ((centralizerCoordinates n hn S e).symm w)

instance centralizerFullCenterImage_isCyclic [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsCyclic (centralizerFullCenterImage n hn S e) :=
  isCyclic_of_surjective ((centralizerOddCoreMap n S e).subgroupMap
    (centralizerFullCenter n hn S e)) ((centralizerOddCoreMap n S e).subgroupMap_surjective _)

theorem centralizerFullCenterImage_eq_modelCenter [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenterImage n hn S e =
      modelCenter (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) := by
  rw [centralizerFullCenterImage, centralizerFullCenter, modelCenter, Subgroup.map_map,
    ← centralizerOddCoreModelHom_comp]
  rfl

theorem centralizerFullCenterImage_card [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (centralizerFullCenterImage n hn S e) = 2 ^ n := by
  rw [centralizerFullCenterImage_eq_modelCenter, modelCenter,
    Subgroup.card_map_of_injective (wreathModelHom_injective _ _),
    Original.Z, Nat.card_zpowers, Original.orderOf_a]

theorem centralizerOddCoreQuotient_oddCore_eq_bot [Finite G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    CFSG.oddCore (centralizerOddCoreQuotient n S e) = ⊥ :=
  weakClosure_oddCore_quotient_eq_bot (involutionCentralizer n S e)

theorem center_isTwoGroup_of_oddCore_eq_bot
    (E : Type v) [Group E] [Finite E] (hcore : CFSG.oddCore E = ⊥) :
    IsPGroup 2 (Subgroup.center E) := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpp, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p = 2 := by
    by_contra hpne
    let : Fact p.Prime := ⟨hpp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center E) p hpdvd
    let X : Subgroup E := Subgroup.zpowers (x : E)
    have hXnormal : X.Normal := Subgroup.normal_of_le_center
      (Subgroup.zpowers_le.mpr x.property)
    have hXcard : Nat.card X = p := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    have hXodd : Odd (Nat.card X) := hXcard.symm ▸ hpp.odd_of_ne_two hpne
    have hXcore : X ≤ CFSG.oddCore E := le_sSup ⟨hXnormal, hXodd⟩
    have hxone : (x : E) = 1 := by
      exact Subgroup.mem_bot.mp ((hcore ▸ hXcore) (Subgroup.mem_zpowers (x : E)))
    have hxone' : x = 1 := Subtype.ext hxone
    rw [hxone', orderOf_one] at hx
    exact hpp.ne_one hx.symm
  simpa only [hp2] using Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, dvd_rfl, by decide⟩


theorem centralizerOddCoreSylow_center_map [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.center (centralizerOddCoreSylow n hn S e)).map
      (centralizerOddCoreSylow n hn S e :
        Subgroup (centralizerOddCoreQuotient n S e)).subtype =
      centralizerFullCenterImage n hn S e := by
  rw [← Subgroup.map_center_eq (centralizerOddCoreCoordinates n hn S e).symm,
    Subgroup.map_map]
  change (Subgroup.center (Wreath (2 ^ n))).map
    (wreathModelHom (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e)) = _
  rw [(wreath_center_involution_and_quaternion_coordinates n hn).center]
  exact (centralizerFullCenterImage_eq_modelCenter n hn S e).symm

theorem centralizerOddCoreQuotient_center_eq_fullCenterImage [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.center (centralizerOddCoreQuotient n S e) =
      centralizerFullCenterImage n hn S e := by
  apply le_antisymm
  · have htwo : IsPGroup 2 (Subgroup.center (centralizerOddCoreQuotient n S e)) :=
      center_isTwoGroup_of_oddCore_eq_bot _ (centralizerOddCoreQuotient_oddCore_eq_bot n S e)
    have hle : Subgroup.center (centralizerOddCoreQuotient n S e) ≤
        (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)) :=
      htwo.le_sylow_of_normal _
    intro a ha
    rw [← centralizerOddCoreSylow_center_map n hn S e]
    refine Subgroup.mem_map.mpr ⟨⟨a, hle ha⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp ha s.val
  · exact (centralizerFullCenterImage_le_center_and_factorization n hn S e).1

instance centralizerFullCenterImage_normal [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerFullCenterImage n hn S e).Normal :=
  Subgroup.normal_of_le_center
    (centralizerFullCenterImage_le_center_and_factorization n hn S e).1

theorem centralizerFullCenterImage_isTwoGroup [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsPGroup 2 (centralizerFullCenterImage n hn S e) :=
  IsPGroup.of_card (centralizerFullCenterImage_card n hn S e)

theorem centralizerFullCenterQuotient_oddCore_eq_bot [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    CFSG.oddCore (centralizerOddCoreQuotient n S e ⧸
      centralizerFullCenterImage n hn S e) = ⊥ := by
  exact oddCore_quotient_eq_bot_of_central_two (centralizerFullCenterImage n hn S e)
    (centralizerFullCenterImage_le_center_and_factorization n hn S e).1
    (centralizerFullCenterImage_isTwoGroup n hn S e)
    (centralizerOddCoreQuotient_oddCore_eq_bot n S e)


theorem centralizerFullCenter_map (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerFullCenter n hn S e).map (involutionCentralizer n S e).subtype =
      modelCenter S e := by
  rw [centralizerFullCenter, modelCenter, Subgroup.map_map, centralizerModelHom_comp]
  rfl

theorem centralizerFullCenterImage_eq_zpowers [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenterImage n hn S e = Subgroup.zpowers
      (centralizerOddCoreMap n S e
        (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
          (Original.a (2 ^ n)))) := by
  rw [centralizerFullCenterImage, centralizerFullCenter_eq_zpowers,
    MonoidHom.map_zpowers]

theorem centralizerOddCoreModelHom_apply [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (w : Wreath (2 ^ n)) :
    wreathModelHom (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) w =
      centralizerOddCoreMap n S e
        (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) w) := by
  exact congrArg (fun f => f w) (centralizerOddCoreModelHom_comp n hn S e)

structure WreathedCentralizerFullCenterData [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Prop where
  original_center :
    (centralizerFullCenter n hn S e).map (involutionCentralizer n S e).subtype = modelCenter S e
  cyclic_center : IsCyclic (centralizerFullCenter n hn S e)
  center_card : Nat.card (centralizerFullCenter n hn S e) = 2 ^ n
  weak_closure :
    ∀ a ∈ centralizerFullCenter n hn S e, ∀ g : involutionCentralizer n S e,
      g⁻¹ * a * g ∈ (centralizerSylow n hn S e :
        Subgroup (involutionCentralizer n S e)) → g⁻¹ * a * g = a
  factorization :
    ∀ g : involutionCentralizer n S e, ∃ r ∈ centralizerOddCore n S e,
      ∃ c ∈ Subgroup.centralizer (centralizerFullCenter n hn S e :
        Set (involutionCentralizer n S e)), g = r * c
  odd_core_card : Odd (Nat.card (centralizerOddCore n S e))
  odd_core_sylow_intersection :
    centralizerOddCore n S e ⊓ (centralizerSylow n hn S e :
      Subgroup (involutionCentralizer n S e)) = ⊥
  odd_core_center_intersection :
    centralizerOddCore n S e ⊓ centralizerFullCenter n hn S e = ⊥
  sylow_map_injective :
    Function.Injective ((centralizerOddCoreMap n S e).domRestrict
      (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)))
  coordinate_map :
    ∀ w : Wreath (2 ^ n),
      wreathModelHom (centralizerOddCoreSylow n hn S e)
        (centralizerOddCoreCoordinates n hn S e) w =
        centralizerOddCoreMap n S e
          (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) w)
  image_cyclic : IsCyclic (centralizerFullCenterImage n hn S e)
  image_card : Nat.card (centralizerFullCenterImage n hn S e) = 2 ^ n
  full_center : Subgroup.center (centralizerOddCoreQuotient n S e) =
    centralizerFullCenterImage n hn S e
  quotient_odd_core : CFSG.oddCore (centralizerOddCoreQuotient n S e) = ⊥
  full_center_quotient_odd_core : CFSG.oddCore (centralizerOddCoreQuotient n S e ⧸
    centralizerFullCenterImage n hn S e) = ⊥

theorem wreathed_centralizer_full_center_odd_core [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    WreathedCentralizerFullCenterData n hn S e where
  original_center := centralizerFullCenter_map n hn S e
  cyclic_center := inferInstance
  center_card := centralizerFullCenter_card n hn S e
  weak_closure := centralizerFullCenter_weakly_closed n hn S e
  factorization := (centralizerFullCenterImage_le_center_and_factorization n hn S e).2
  odd_core_card := centralizerOddCore_card_odd n S e
  odd_core_sylow_intersection := centralizerOddCore_inf_sylow_eq_bot n hn S e
  odd_core_center_intersection := centralizerOddCore_inf_fullCenter_eq_bot n hn S e
  sylow_map_injective := centralizerOddCoreMap_sylow_injective n hn S e
  coordinate_map := centralizerOddCoreModelHom_apply n hn S e
  image_cyclic := inferInstance
  image_card := centralizerFullCenterImage_card n hn S e
  full_center := centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e
  quotient_odd_core := centralizerOddCoreQuotient_oddCore_eq_bot n S e
  full_center_quotient_odd_core := centralizerFullCenterQuotient_oddCore_eq_bot n hn S e

end CFSG.Wreathed
