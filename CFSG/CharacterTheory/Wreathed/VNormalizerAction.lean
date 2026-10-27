module

public import CFSG.CharacterTheory.Wreathed.VNormalizerAmbient
public import CFSG.CharacterTheory.Wreathed.VQuotientKernel
public import CFSG.GroupTheory.KleinFourAutomorphism

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

theorem original_v_center_quotient_isKleinFour (n : ℕ) (hn : 2 ≤ n) :
    IsKleinFour (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) := by
  obtain ⟨e⟩ := nonabelian_odd_automorphism_center_quotient_dihedral_two n hn
    (Original.V (2 ^ n)) (original_v_is_nonabelian n hn) (by
      have h := wreath_center_involution_and_quaternion_coordinates n hn
      rw [h.center, h.central_product]
      exact le_sup_left) (original_v_automorphism_not_isPGroup n hn)
  constructor
  · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  · rw [Monoid.exponent_eq_of_mulEquiv e]
    exact IsKleinFour.exponent_two

variable {G : Type u} [Group G]

@[expose] def modelVQuotientAction {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Subgroup.normalizer (modelV S e : Set G) →*
      MulAut (Original.V m ⧸ Subgroup.center (Original.V m)) :=
  (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
    (Subgroup.center (Original.V m))).comp (modelVAction S e)

theorem modelVQuotientAction_mk {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (g : Subgroup.normalizer (modelV S e : Set G)) (v : Original.V m) :
    modelVQuotientAction S e g ((QuotientGroup.mk' (Subgroup.center (Original.V m))) v) =
      (QuotientGroup.mk' (Subgroup.center (Original.V m))) (modelVAction S e g v) :=
  CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk _ _ _

theorem original_quarter_power_normalizes_v (n : ℕ) (hn : 2 ≤ n) :
    Original.s (2 ^ n) ^ (2 ^ (n - 2)) ∈
      Subgroup.normalizer (Original.V (2 ^ n) : Set (Wreath (2 ^ n))) := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  rw [hm, Original.V_atQuarter]
  simp only [Original.s, element_base_pow, nsmul_eq_mul, mul_one, mul_zero]
  rw [element_mem_v_normalizer_iff]
  right
  rw [sub_zero, nsmul_eq_mul, Nat.cast_mul]

@[expose] def modelVQuarterActor (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) :=
  ⟨wreathModelHom S e (Original.s (2 ^ n) ^ (2 ^ (n - 2))),
    Subgroup.le_normalizer_map (wreathModelHom S e)
      (Subgroup.mem_map.mpr ⟨_, original_quarter_power_normalizes_v n hn, rfl⟩)⟩

theorem modelVAction_sylow_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (g : Subgroup.normalizer (modelV S e : Set G)) (hg : g.val ∈ (S : Subgroup G))
    (v : Original.V m) :
    (modelVAction S e g v).val =
      e ⟨g.val, hg⟩ * v.val * (e ⟨g.val, hg⟩)⁻¹ := by
  apply wreathModelHom_injective S e
  rw [map_mul, map_mul, map_inv, modelVAction_coe]
  have h : wreathModelHom S e (e ⟨g.val, hg⟩) = g.val :=
    congrArg Subtype.val (e.symm_apply_apply ⟨g.val, hg⟩)
  rw [h]

theorem modelVAction_inner {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (v w : Original.V m) :
    modelVAction S e
      ⟨wreathModelHom S e v.val, (modelV S e).le_normalizer
        (Subgroup.mem_map.mpr ⟨v.val, v.property, rfl⟩)⟩ w = v * w * v⁻¹ := by
  apply Subtype.ext
  apply wreathModelHom_injective S e
  rw [modelVAction_coe]
  change wreathModelHom S e v.val * wreathModelHom S e w.val *
    (wreathModelHom S e v.val)⁻¹ = wreathModelHom S e (v.val * w.val * v.val⁻¹)
  rw [map_mul, map_mul, map_inv]

theorem modelVQuotientAction_eq_one_of_mem (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) (hg : g.val ∈ modelV S e) :
    modelVQuotientAction S e g = 1 := by
  let : IsKleinFour (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) :=
    original_v_center_quotient_isKleinFour n hn
  obtain ⟨v, hv, hvg⟩ := Subgroup.mem_map.mp hg
  have hvimage : wreathModelHom S e v ∈ modelV S e :=
    Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
  have hgeq : g = ⟨wreathModelHom S e v, (modelV S e).le_normalizer hvimage⟩ :=
    Subtype.ext hvg.symm
  apply MulEquiv.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H w =>
    change modelVQuotientAction S e g
      ((QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) w) = _
    rw [modelVQuotientAction_mk, hgeq, modelVAction_inner S e (⟨v, hv⟩ : Original.V (2 ^ n))]
    simp only [map_mul, map_inv, MulAut.one_apply]
    rw [(IsKleinFour.isMulCommutative).1.1]
    group
    rfl

theorem modelVQuarterActor_square_mem (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelVQuarterActor n hn S e).val ^ 2 ∈ modelV S e := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  change (wreathModelHom S e (Original.s (2 ^ n) ^ (2 ^ (n - 2)))) ^ 2 ∈ _
  rw [← map_pow]
  apply Subgroup.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  rw [hm, Original.V_atQuarter]
  simp only [Original.s, element_base_pow, nsmul_eq_mul, mul_one, mul_zero]
  rw [element_mem_v, sub_zero]
  right
  rw [Nat.cast_mul]

theorem modelVQuarterQuotientAction_square (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelVQuotientAction S e (modelVQuarterActor n hn S e)) ^ 2 = 1 := by
  rw [← map_pow]
  exact modelVQuotientAction_eq_one_of_mem n hn S e _
    (modelVQuarterActor_square_mem n hn S e)

theorem original_quarter_conjugate_z_not_center (n : ℕ) (hn : 2 ≤ n) :
    (Original.s (2 ^ n) ^ (2 ^ (n - 2)) * Original.z (2 ^ n) *
        (Original.s (2 ^ n) ^ (2 ^ (n - 2)))⁻¹) / Original.z (2 ^ n) ∉
      Subgroup.center (Wreath (2 ^ n)) := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  rw [hm]
  simp only [Original.s, Original.z, element_base_pow, nsmul_eq_mul, mul_one, mul_zero,
    conjugate_swap_by_base, zero_add, zero_sub, sub_zero, div_eq_mul_inv,
    element_swap_inv, neg_zero, element_swap_mul, add_zero,
    show (1 + 1 : ZMod 2) = 0 by decide]
  rw [element_mem_center_iff _ (by
    have hpos := pow_pos (by decide : 0 < (2 : ℕ)) (n - 2)
    omega)]
  intro h
  have htwo : ((2 ^ (n - 2) : ℕ) : ZMod (4 * 2 ^ (n - 2))) +
      ((2 ^ (n - 2) : ℕ) : ZMod (4 * 2 ^ (n - 2))) = 0 := by
    linear_combination h.2
  apply half_quarter_ne_zero (2 ^ (n - 2)) (pow_pos (by decide) _)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using htwo

theorem modelVQuarterQuotientAction_ne_one (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelVQuotientAction S e (modelVQuarterActor n hn S e) ≠ 1 := by
  intro h
  let z : Original.V (2 ^ n) :=
    ⟨Original.z (2 ^ n), Subgroup.subset_closure (by simp)⟩
  have hfixed := DFunLike.congr_fun h
    ((QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) z)
  rw [modelVQuotientAction_mk, MulAut.one_apply] at hfixed
  have hcentral := QuotientGroup.eq_iff_div_mem.mp hfixed
  have hambient : ((modelVAction S e (modelVQuarterActor n hn S e)) z).val / z.val ∈
      Subgroup.center (Wreath (2 ^ n)) := by
    have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
    rw [hstructure.center, ← hstructure.central_product_center]
    exact Subgroup.mem_map.mpr ⟨_, hcentral, rfl⟩
  have hactor : (modelVQuarterActor n hn S e).val ∈ (S : Subgroup G) :=
    (e.symm (Original.s (2 ^ n) ^ (2 ^ (n - 2)))).property
  rw [modelVAction_sylow_coe S e _ hactor] at hambient
  have he : e ⟨(modelVQuarterActor n hn S e).val, hactor⟩ =
      Original.s (2 ^ n) ^ (2 ^ (n - 2)) := e.apply_symm_apply _
  rw [he] at hambient
  exact original_quarter_conjugate_z_not_center n hn hambient

theorem modelVQuarterQuotientAction_order (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (modelVQuotientAction S e (modelVQuarterActor n hn S e)) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (modelVQuarterQuotientAction_square n hn S e)
    (modelVQuarterQuotientAction_ne_one n hn S e)

theorem modelVAction_ker {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelVAction S e).ker =
      (Subgroup.centralizer (modelV S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelV S e : Set G)) := by
  unfold modelVAction
  rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr (modelVEquiv S e).symm).injective,
    Subgroup.normalizerMonoidHom_ker]

@[expose] def modelVInnerCentralizer {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Subgroup (Subgroup.normalizer (modelV S e : Set G)) :=
  (modelV S e).subgroupOf (Subgroup.normalizer (modelV S e : Set G)) ⊔
    (Subgroup.centralizer (modelV S e : Set G)).subgroupOf
      (Subgroup.normalizer (modelV S e : Set G))

instance modelVInnerCentralizer_normal {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelVInnerCentralizer S e).Normal := by
  unfold modelVInnerCentralizer
  infer_instance

theorem modelVInnerCentralizer_eq {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelVInnerCentralizer S e =
      (modelV S e ⊔ Subgroup.centralizer (modelV S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelV S e : Set G)) := by
  rw [Subgroup.subgroupOf_sup (modelV S e).le_normalizer
    (Subgroup.centralizer_le_normalizer _)]
  rfl

theorem modelVQuotientAction_ker [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelVQuotientAction S e).ker = modelVInnerCentralizer S e := by
  apply le_antisymm
  · intro g hg
    have hquotient : ∀ w : Original.V (2 ^ n),
        (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n))))
          (modelVAction S e g w) =
        (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) w := by
      intro w
      have h := DFunLike.congr_fun hg
        ((QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) w)
      simpa only [modelVQuotientAction_mk, MulAut.one_apply] using h
    obtain ⟨v, hv⟩ := original_v_center_quotient_kernel_inner n hn
      (modelVAction S e g) (modelVAction_fixes_center n hn S e g) hquotient
    let vN : Subgroup.normalizer (modelV S e : Set G) :=
      ⟨wreathModelHom S e v.val, (modelV S e).le_normalizer
        (Subgroup.mem_map.mpr ⟨v.val, v.property, rfl⟩)⟩
    have hvN : modelVAction S e vN = MulAut.conj v := by
      apply MulEquiv.ext
      intro w
      exact modelVAction_inner S e v w
    have hc : vN⁻¹ * g ∈
        (Subgroup.centralizer (modelV S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelV S e : Set G)) := by
      rw [← modelVAction_ker]
      change modelVAction S e (vN⁻¹ * g) = 1
      rw [map_mul, map_inv, hvN, hv, inv_mul_cancel]
    have hvMem : vN ∈
        (modelV S e).subgroupOf (Subgroup.normalizer (modelV S e : Set G)) :=
      Subgroup.mem_map.mpr ⟨v.val, v.property, rfl⟩
    have hprod : vN * (vN⁻¹ * g) ∈ modelVInnerCentralizer S e :=
      (modelVInnerCentralizer S e).mul_mem
        (Subgroup.mem_sup_left hvMem) (Subgroup.mem_sup_right hc)
    simpa only [mul_inv_cancel_left] using hprod
  · apply sup_le
    · intro g hg
      exact modelVQuotientAction_eq_one_of_mem n hn S e g hg
    · intro g hg
      have hf : modelVAction S e g = 1 := by
        have h := (modelVAction_ker S e).symm ▸ hg
        exact h
      change CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
        (Subgroup.center (Original.V (2 ^ n))) (modelVAction S e g) = 1
      rw [hf, map_one]

@[expose] def modelVNormalizerQuotientEquiv [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      (modelVQuotientAction S e).range :=
  (QuotientGroup.quotientMulEquivOfEq (modelVQuotientAction_ker n hn S e).symm).trans
    (QuotientGroup.quotientKerEquivRange (modelVQuotientAction S e))

@[expose] def modelVNormalizerQuotientAction [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e →*
      MulAut (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) :=
  (modelVQuotientAction S e).range.subtype.comp
    (modelVNormalizerQuotientEquiv n hn S e).toMonoidHom

theorem modelVNormalizerQuotientAction_injective [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective (modelVNormalizerQuotientAction n hn S e) :=
  (modelVQuotientAction S e).range.subtype_injective.comp
    (modelVNormalizerQuotientEquiv n hn S e).injective

theorem modelVNormalizerQuotientAction_mk [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    modelVNormalizerQuotientAction n hn S e
      ((QuotientGroup.mk' (modelVInnerCentralizer S e)) g) = modelVQuotientAction S e g := rfl

theorem modelVQuotientAction_image_alternatives (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (modelVQuotientAction S e).range = 2 ∨
      Nonempty ((modelVQuotientAction S e).range ≃* Equiv.Perm (Fin 3)) := by
  let : IsKleinFour (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) :=
    original_v_center_quotient_isKleinFour n hn
  exact CFSG.kleinFour_automorphism_subgroup_alternatives _ (modelVQuotientAction S e).range
    (modelVQuotientAction S e (modelVQuarterActor n hn S e)) ⟨_, rfl⟩
    (modelVQuarterQuotientAction_order n hn S e)

theorem modelVNormalizerQuotient_alternatives [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e) = 2 ∨
      Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
        Equiv.Perm (Fin 3)) := by
  rcases modelVQuotientAction_image_alternatives n hn S e with htwo | hsix
  · exact Or.inl ((Nat.card_congr (modelVNormalizerQuotientEquiv n hn S e).toEquiv).trans htwo)
  · obtain ⟨esix⟩ := hsix
    exact Or.inr ⟨(modelVNormalizerQuotientEquiv n hn S e).trans esix⟩

@[expose] def modelVCenterFixingAction [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) →* centerFixingAutomorphisms (Original.V (2 ^ n)) :=
  (modelVAction S e).codRestrict (centerFixingAutomorphisms (Original.V (2 ^ n)))
    (fun g => (mem_centerFixingAutomorphisms_iff _).mpr
      (modelVAction_fixes_center n hn S e g))

theorem modelVCenterFixingAction_quotient [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centerFixingQuotientAction (Original.V (2 ^ n))).comp
      (modelVCenterFixingAction n hn S e) = modelVQuotientAction S e := rfl

theorem modelVAction_image_isPGroup_of_quotient_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2) : IsPGroup 2 (modelVAction S e).range := by
  let q := centerFixingQuotientAction (Original.V (2 ^ n))
  let f := modelVCenterFixingAction n hn S e
  have hker : IsPGroup 2 q.ker := by
    rw [original_v_centerFixingQuotientAction_ker n hn]
    have hV := (wreath_isPGroup n).to_subgroup (Original.V (2 ^ n))
    have h := (hV.to_subgroup ⊤).map (innerToCenterFixing (Original.V (2 ^ n)))
    rwa [Subgroup.map_top] at h
  have hquotient : IsPGroup 2 (modelVQuotientAction S e).range := by
    apply IsPGroup.of_card (n := 1)
    rw [← Nat.card_congr (modelVNormalizerQuotientEquiv n hn S e).toEquiv, hcard]
    rfl
  have hpreimage : IsPGroup 2 ((modelVQuotientAction S e).range.comap q) :=
    hquotient.comap_of_ker_isPGroup q hker
  have hle : f.range ≤ (modelVQuotientAction S e).range.comap q := by
    rintro a ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hf : IsPGroup 2 f.range := hpreimage.to_le hle
  have hmap : f.range.map (centerFixingAutomorphisms (Original.V (2 ^ n))).subtype =
      (modelVAction S e).range := by
    rw [← MonoidHom.range_comp]
    rfl
  rw [← hmap]
  exact hf.map _

theorem modelVAction_symm_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (g : Subgroup.normalizer (modelV S e : Set G)) (v : Original.V m) :
    wreathModelHom S e ((modelVAction S e g).symm v).val =
      g.val⁻¹ * wreathModelHom S e v.val * g.val := by
  have h := modelVAction_coe S e g ((modelVAction S e g).symm v)
  rw [MulEquiv.apply_symm_apply] at h
  calc
    wreathModelHom S e ((modelVAction S e g).symm v).val =
      g.val⁻¹ * (g.val * wreathModelHom S e
        ((modelVAction S e g).symm v).val * g.val⁻¹) * g.val := by group
    _ = g.val⁻¹ * wreathModelHom S e v.val * g.val := by rw [← h]

theorem modelVNormalizer_order_two_step_replacement [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2)
    (g : G) (hg : g ∈ Subgroup.normalizer (modelV S e : Set G)) :
    ∃ s : G, s ∈ (S : Subgroup G) ∧
      s ∈ Subgroup.normalizer (modelV S e : Set G) ∧
        ∀ v ∈ modelV S e, s⁻¹ * v * s = g⁻¹ * v * g := by
  let f := modelVAction S e
  obtain ⟨s, hs, hsg⟩ := CFSG.GorensteinWalter.hom_to_pGroup_image_on_sylow
    (modelVAction_image_isPGroup_of_quotient_order_two n hn S e hcard)
    f.rangeRestrict (modelVNormalizerSylow n hn S e) ⟨g, hg⟩
  have hsS : s.val ∈ (S : Subgroup G) := by
    change s ∈ (modelVNormalizerSylow n hn S e :
      Subgroup (Subgroup.normalizer (modelV S e : Set G))) at hs
    rw [modelVNormalizerSylow_coe] at hs
    exact hs
  have heq : f s = f ⟨g, hg⟩ := congrArg Subtype.val hsg
  refine ⟨s.val, hsS, s.property, ?_⟩
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  have hpoint := DFunLike.congr_fun (congrArg MulEquiv.symm heq) (⟨w, hw⟩ : Original.V (2 ^ n))
  have hambient := congrArg (fun v : Original.V (2 ^ n) => wreathModelHom S e v.val) hpoint
  rw [modelVAction_symm_coe, modelVAction_symm_coe] at hambient
  exact hambient

end CFSG.Wreathed
