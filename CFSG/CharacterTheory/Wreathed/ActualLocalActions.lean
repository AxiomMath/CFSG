module

public import CFSG.CharacterTheory.Wreathed.LocalNormalizerActions
public import CFSG.CharacterTheory.Wreathed.BaseSquares
public import CFSG.CharacterTheory.Wreathed.VCyclicFusion

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

variable {G : Type u} [Group G]

@[expose] def modelCenter {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup G :=
  (Original.Z m).map (wreathModelHom S e)

@[expose] def modelQ {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup G :=
  (Original.Q m).map (wreathModelHom S e)

@[expose] def modelQEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Original.Q m ≃* modelQ S e :=
  (Original.Q m).equivMapOfInjective (wreathModelHom S e)
    (wreathModelHom_injective S e)

theorem modelQ_le_modelV (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : modelQ S e ≤ modelV S e :=
  Subgroup.map_mono (original_quaternion_le_v n hn)

theorem modelV_center_eq_modelCenter (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.center (modelV S e)).map (modelV S e).subtype = modelCenter S e := by
  rw [← Subgroup.map_center_eq (modelVEquiv S e), Subgroup.map_map]
  change (Subgroup.center (Original.V (2 ^ n))).map
    ((wreathModelHom S e).comp (Original.V (2 ^ n)).subtype) = _
  rw [← Subgroup.map_map,
    (wreath_center_involution_and_quaternion_coordinates n hn).central_product_center]
  rfl

theorem modelV_center_eq_modelCenter_subgroup (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.center (modelV S e) = (modelCenter S e).subgroupOf (modelV S e) := by
  ext v
  change v ∈ Subgroup.center (modelV S e) ↔ v.val ∈ modelCenter S e
  rw [← modelV_center_eq_modelCenter n hn S e]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hval⟩
    have heq : w = v := Subtype.ext hval
    exact heq ▸ hw

@[expose] def modelVCenterQuotientEquiv {m : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Original.V m ⧸ Subgroup.center (Original.V m) ≃*
      modelV S e ⧸ Subgroup.center (modelV S e) :=
  QuotientGroup.congr _ _ (modelVEquiv S e) (Subgroup.map_center_eq (modelVEquiv S e))

theorem modelVCenterQuotientEquiv_mk {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (v : Original.V m) :
    modelVCenterQuotientEquiv S e ((QuotientGroup.mk' (Subgroup.center (Original.V m))) v) =
      (QuotientGroup.mk' (Subgroup.center (modelV S e))) (modelVEquiv S e v) := rfl

@[expose] def modelVActualQuotientAction {m : ℕ} (S : Sylow 2 G)
    (e : S ≃* Wreath m) :
    Subgroup.normalizer (modelV S e : Set G) →*
      MulAut (modelV S e ⧸ Subgroup.center (modelV S e)) :=
  (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
    (Subgroup.center (modelV S e))).comp (modelV S e).normalizerMonoidHom

theorem modelVActualQuotientAction_mk {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (g : Subgroup.normalizer (modelV S e : Set G)) (v : modelV S e) :
    modelVActualQuotientAction S e g
      ((QuotientGroup.mk' (Subgroup.center (modelV S e))) v) =
        (QuotientGroup.mk' (Subgroup.center (modelV S e)))
          ((modelV S e).normalizerMonoidHom g v) :=
  CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk _ _ _

theorem modelVActualQuotientAction_intertwines {m : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath m)
    (g : Subgroup.normalizer (modelV S e : Set G))
    (q : Original.V m ⧸ Subgroup.center (Original.V m)) :
    modelVActualQuotientAction S e g (modelVCenterQuotientEquiv S e q) =
      modelVCenterQuotientEquiv S e (modelVQuotientAction S e g q) := by
  induction q using QuotientGroup.induction_on with
  | H v =>
    change modelVActualQuotientAction S e g
      (modelVCenterQuotientEquiv S e ((QuotientGroup.mk' (Subgroup.center (Original.V m))) v)) = _
    rw [modelVCenterQuotientEquiv_mk, modelVActualQuotientAction_mk]
    change (QuotientGroup.mk' (Subgroup.center (modelV S e)))
      ((modelV S e).normalizerMonoidHom g (modelVEquiv S e v)) =
        modelVCenterQuotientEquiv S e
          ((QuotientGroup.mk' (Subgroup.center (Original.V m))) (modelVAction S e g v))
    rw [modelVCenterQuotientEquiv_mk]
    congr 1
    exact ((modelVEquiv S e).apply_symm_apply
      ((modelV S e).normalizerMonoidHom g (modelVEquiv S e v))).symm

theorem modelVActualQuotientAction_eq_congr {m : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelVActualQuotientAction S e =
      (MulAut.congr (modelVCenterQuotientEquiv S e)).toMonoidHom.comp
        (modelVQuotientAction S e) := by
  ext g q
  obtain ⟨v, rfl⟩ := (modelVCenterQuotientEquiv S e).surjective q
  change modelVActualQuotientAction S e g (modelVCenterQuotientEquiv S e v) =
    modelVCenterQuotientEquiv S e (modelVQuotientAction S e g
      ((modelVCenterQuotientEquiv S e).symm (modelVCenterQuotientEquiv S e v)))
  rw [MulEquiv.symm_apply_apply]
  exact modelVActualQuotientAction_intertwines S e g v

theorem modelVActualQuotientAction_ker [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelVActualQuotientAction S e).ker = modelVInnerCentralizer S e := by
  rw [modelVActualQuotientAction_eq_congr,
    MonoidHom.ker_comp_of_injective _ _ (MulAut.congr (modelVCenterQuotientEquiv S e)).injective]
  exact modelVQuotientAction_ker n hn S e

@[expose] def modelVNormalizerActualQuotientAction [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e →*
      MulAut (modelV S e ⧸ Subgroup.center (modelV S e)) :=
  (MulAut.congr (modelVCenterQuotientEquiv S e)).toMonoidHom.comp
    (modelVNormalizerQuotientAction n hn S e)

theorem modelVNormalizerActualQuotientAction_injective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective (modelVNormalizerActualQuotientAction n hn S e) :=
  (MulAut.congr (modelVCenterQuotientEquiv S e)).injective.comp
    (modelVNormalizerQuotientAction_injective n hn S e)

theorem modelVNormalizerActualQuotientAction_mk [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    modelVNormalizerActualQuotientAction n hn S e
      ((QuotientGroup.mk' (modelVInnerCentralizer S e)) g) =
        modelVActualQuotientAction S e g := by
  rw [modelVActualQuotientAction_eq_congr]
  rfl

theorem modelVNormalizer_swap_fusion [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    ∃ g : G, g ∈ Subgroup.normalizer (modelV S e : Set G) ∧
      (g * wreathModelHom S e (Original.z (2 ^ n)) * g⁻¹ =
        wreathModelHom S e (Original.x2 (2 ^ n)) ∨
      g * wreathModelHom S e (Original.z (2 ^ n)) * g⁻¹ =
        wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2))) := by
  obtain ⟨h, _, _, horder⟩ := modelVNormalizer_exists_odd_three_power_actor n hn S e hsix
  have hquot : orderOf (originalVQuotientAutomorphism n (modelVAction S e h)) = 3 := horder
  obtain ⟨i, _, hi⟩ := originalVAutomorphism_order_three_swap_endpoint n hn
    (modelVAction S e h) hquot
  have hpoint : wreathModelHom S e (((modelVAction S e h) ^ i)
      (originalVSwap (2 ^ n))).val =
      (h ^ i).val * wreathModelHom S e (Original.z (2 ^ n)) * (h ^ i).val⁻¹ := by
    rw [← map_pow]
    exact modelVAction_coe S e (h ^ i) (originalVSwap (2 ^ n))
  refine ⟨(h ^ i).val, (h ^ i).property, ?_⟩
  rcases hi with hi | hi
  · exact Or.inl (hpoint.symm.trans (congrArg (wreathModelHom S e) hi))
  · exact Or.inr (hpoint.symm.trans (congrArg (wreathModelHom S e) hi))

@[expose] def cyclicFourSubgroupEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : CyclicFourSubgroups A ≃ CyclicFourSubgroups B :=
  e.mapSubgroup.toEquiv.subtypeEquiv (by
    intro H
    change (IsCyclic H ∧ Nat.card H = 4) ↔
      (IsCyclic (H.map e.toMonoidHom) ∧ Nat.card (H.map e.toMonoidHom) = 4)
    constructor
    · rintro ⟨hcyclic, hcard⟩
      exact ⟨(e.subgroupMap H).isCyclic.mp hcyclic,
        (Subgroup.card_map_of_injective e.injective).trans hcard⟩
    · rintro ⟨hcyclic, hcard⟩
      exact ⟨(e.subgroupMap H).isCyclic.mpr hcyclic,
        (Subgroup.card_map_of_injective e.injective).symm.trans hcard⟩)

theorem cyclicFourSubgroupEquiv_coe {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (H : CyclicFourSubgroups A) :
    (cyclicFourSubgroupEquiv e H).val = H.val.map e.toMonoidHom := rfl

@[expose] def modelQAutomorphism (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) : MulAut (modelQ S e) :=
  MulAut.congr (modelQEquiv S e)
    (originalQuaternionAutomorphism n hn (modelVAction S e g))

theorem modelQAutomorphism_coe (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) (q : modelQ S e) :
    (modelQAutomorphism n hn S e g q).val = g.val * q.val * g.val⁻¹ := by
  obtain ⟨w, rfl⟩ := (modelQEquiv S e).surjective q
  have happ : modelQAutomorphism n hn S e g (modelQEquiv S e w) =
      modelQEquiv S e (originalQuaternionAutomorphism n hn (modelVAction S e g) w) := by
    change modelQEquiv S e (originalQuaternionAutomorphism n hn (modelVAction S e g)
      ((modelQEquiv S e).symm (modelQEquiv S e w))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [happ]
  change wreathModelHom S e
    (originalQuaternionAutomorphism n hn (modelVAction S e g) w).val =
      g.val * wreathModelHom S e w.val * g.val⁻¹
  rw [originalQuaternionAutomorphism_coe]
  exact modelVAction_coe S e g (Subgroup.inclusion (original_quaternion_le_v n hn) w)

theorem modelVNormalizer_normalizes_modelQ (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ≤
      Subgroup.normalizer (modelQ S e : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact (modelQAutomorphism_coe n hn S e ⟨g, hg⟩ ⟨x, hx⟩) ▸
      (modelQAutomorphism n hn S e ⟨g, hg⟩ ⟨x, hx⟩).property
  · intro hx
    have h := (modelQAutomorphism n hn S e ⟨g⁻¹,
      (Subgroup.normalizer (modelV S e : Set G)).inv_mem hg⟩ ⟨g * x * g⁻¹, hx⟩).property
    rw [modelQAutomorphism_coe] at h
    convert h using 1
    group

theorem modelQAutomorphism_eq_actual_action (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    modelQAutomorphism n hn S e g =
      (modelQ S e).normalizerMonoidHom
        ⟨g.val, modelVNormalizer_normalizes_modelQ n hn S e g.property⟩ := by
  ext q
  rw [modelQAutomorphism_coe]
  exact (Subgroup.normalizerMonoidHom_apply_apply_coe (modelQ S e)
    ⟨g.val, modelVNormalizer_normalizes_modelQ n hn S e g.property⟩ q).symm

theorem modelQCyclicAction_intertwines (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (H : CyclicFourSubgroups (Original.Q (2 ^ n))) :
    cyclicFourAutomorphismAction (modelQAutomorphism n hn S e g)
      (cyclicFourSubgroupEquiv (modelQEquiv S e) H) =
        cyclicFourSubgroupEquiv (modelQEquiv S e)
          (cyclicFourAutomorphismAction
            (originalQuaternionAutomorphism n hn (modelVAction S e g)) H) := by
  apply Subtype.ext
  rw [cyclicFourAutomorphismAction_coe, cyclicFourSubgroupEquiv_coe,
    cyclicFourSubgroupEquiv_coe, cyclicFourAutomorphismAction_coe,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext q
  change (modelQEquiv S e
    (originalQuaternionAutomorphism n hn (modelVAction S e g)
      ((modelQEquiv S e).symm (modelQEquiv S e q)))).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem modelQAutomorphism_cycles_cyclic_four (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3)
    (H : CyclicFourSubgroups (modelQ S e)) :
    let σ := cyclicFourAutomorphismAction (modelQAutomorphism n hn S e g)
    σ H ≠ H ∧ σ (σ H) ≠ H ∧ σ (σ H) ≠ σ H ∧
      ∀ J : CyclicFourSubgroups (modelQ S e), J = H ∨ J = σ H ∨ J = σ (σ H) := by
  let E := cyclicFourSubgroupEquiv (modelQEquiv S e)
  let σ := cyclicFourAutomorphismAction (modelQAutomorphism n hn S e g)
  let τ := cyclicFourAutomorphismAction
    (originalQuaternionAutomorphism n hn (modelVAction S e g))
  obtain ⟨H0, rfl⟩ := E.surjective H
  obtain ⟨hne, hne2, hne3, hcover⟩ :=
    originalQuaternionAutomorphism_cycles_cyclic_four n hn (modelVAction S e g) horder H0
  have hmap (K : CyclicFourSubgroups (Original.Q (2 ^ n))) : σ (E K) = E (τ K) :=
    modelQCyclicAction_intertwines n hn S e g K
  change σ (E H0) ≠ E H0 ∧ σ (σ (E H0)) ≠ E H0 ∧
    σ (σ (E H0)) ≠ σ (E H0) ∧ ∀ J, J = E H0 ∨ J = σ (E H0) ∨ J = σ (σ (E H0))
  rw [hmap, hmap]
  refine ⟨fun h => hne (E.injective h), fun h => hne2 (E.injective h),
    fun h => hne3 (E.injective h), ?_⟩
  intro J
  obtain ⟨J0, rfl⟩ := E.surjective J
  rcases hcover J0 with h | h | h
  · exact Or.inl (congrArg E h)
  · exact Or.inr (Or.inl (congrArg E h))
  · exact Or.inr (Or.inr (congrArg E h))

theorem modelQ_cyclic_four_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (CyclicFourSubgroups (modelQ S e)) = 3 := by
  rw [← Nat.card_congr (cyclicFourSubgroupEquiv (modelQEquiv S e))]
  exact original_quaternion_cyclic_four_card n hn

theorem modelVActualQuotientAction_order (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    orderOf (modelVActualQuotientAction S e g) = orderOf (modelVQuotientAction S e g) := by
  rw [modelVActualQuotientAction_eq_congr]
  exact (MulAut.congr (modelVCenterQuotientEquiv S e)).orderOf_eq _

theorem modelVActualQuotientAction_cycles_nonzero (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3)
    (x : modelV S e ⧸ Subgroup.center (modelV S e)) (hx : x ≠ 1) :
    modelVActualQuotientAction S e g x ≠ x ∧
      modelVActualQuotientAction S e g (modelVActualQuotientAction S e g x) ≠ x ∧
      modelVActualQuotientAction S e g (modelVActualQuotientAction S e g x) ≠
        modelVActualQuotientAction S e g x ∧
      ∀ y : modelV S e ⧸ Subgroup.center (modelV S e), y ≠ 1 →
        y = x ∨ y = modelVActualQuotientAction S e g x ∨
          y = modelVActualQuotientAction S e g (modelVActualQuotientAction S e g x) := by
  let E := modelVCenterQuotientEquiv S e
  let a := modelVQuotientAction S e g
  let b := modelVActualQuotientAction S e g
  obtain ⟨x0, rfl⟩ := E.surjective x
  have hx0 : x0 ≠ 1 := by
    intro h
    apply hx
    rw [h, map_one]
  obtain ⟨hne, hne2, hne3, hcover⟩ :=
    modelVNormalizer_order_three_cycles_all_nonzero n hn S e g horder x0 hx0
  have hmap (q) : b (E q) = E (a q) := modelVActualQuotientAction_intertwines S e g q
  change b (E x0) ≠ E x0 ∧ b (b (E x0)) ≠ E x0 ∧
    b (b (E x0)) ≠ b (E x0) ∧ ∀ y, y ≠ 1 →
      y = E x0 ∨ y = b (E x0) ∨ y = b (b (E x0))
  rw [hmap, hmap]
  refine ⟨fun h => hne (E.injective h), fun h => hne2 (E.injective h),
    fun h => hne3 (E.injective h), ?_⟩
  intro y hy
  obtain ⟨y0, rfl⟩ := E.surjective y
  have hy0 : y0 ≠ 1 := by
    intro h
    apply hy
    rw [h, map_one]
  rcases hcover y0 hy0 with h | h | h
  · exact Or.inl (congrArg E h)
  · exact Or.inr (Or.inl (congrArg E h))
  · exact Or.inr (Or.inr (congrArg E h))

theorem modelVNormalizer_exists_actual_odd_three_cycle [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    ∃ g : Subgroup.normalizer (modelV S e : Set G),
      (∃ k : ℕ, 0 < k ∧ orderOf g = 3 ^ k) ∧ Odd (orderOf g) ∧
      orderOf (modelVActualQuotientAction S e g) = 3 ∧
      (∀ x : modelV S e ⧸ Subgroup.center (modelV S e), x ≠ 1 →
        modelVActualQuotientAction S e g x ≠ x ∧
        modelVActualQuotientAction S e g (modelVActualQuotientAction S e g x) ≠ x ∧
        modelVActualQuotientAction S e g (modelVActualQuotientAction S e g x) ≠
          modelVActualQuotientAction S e g x ∧
        ∀ y : modelV S e ⧸ Subgroup.center (modelV S e), y ≠ 1 →
          y = x ∨ y = modelVActualQuotientAction S e g x ∨
            y = modelVActualQuotientAction S e g (modelVActualQuotientAction S e g x)) ∧
      (∀ H : CyclicFourSubgroups (modelQ S e),
        let σ := cyclicFourAutomorphismAction (modelQAutomorphism n hn S e g)
        σ H ≠ H ∧ σ (σ H) ≠ H ∧ σ (σ H) ≠ σ H ∧
          ∀ J : CyclicFourSubgroups (modelQ S e), J = H ∨ J = σ H ∨ J = σ (σ H)) := by
  obtain ⟨g, hpower, hodd, horder⟩ :=
    modelVNormalizer_exists_odd_three_power_actor n hn S e hsix
  exact ⟨g, hpower, hodd, (modelVActualQuotientAction_order n S e g).trans horder,
    modelVActualQuotientAction_cycles_nonzero n hn S e g horder,
    modelQAutomorphism_cycles_cyclic_four n hn S e g horder⟩

@[expose] def baseInvolutionsEquivOmega (n : ℕ) :
    {b : baseSubgroup (2 ^ n) // orderOf b = 2} ≃
      {b : baseOmega (2 ^ n) // b ≠ 1} where
  toFun b := ⟨⟨b.val, (by
    have h := pow_orderOf_eq_one b.val
    rwa [b.property] at h)⟩, by
      intro h
      have hb : b.val = 1 := congrArg Subtype.val h
      have ho := b.property
      rw [hb, orderOf_one] at ho
      omega⟩
  invFun b := ⟨b.val.val, by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime
    · exact b.val.property
    · intro h
      apply b.property
      exact Subtype.ext h⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem base_involutions_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {b : baseSubgroup (2 ^ n) // orderOf b = 2} = 3 := by
  rw [Nat.card_congr (baseInvolutionsEquivOmega n)]
  exact baseOmega_nonidentity_card n hn

@[expose] def modelBaseInvolutionsEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    {b : baseSubgroup m // orderOf b = 2} ≃
      {x : G // x ∈ modelBase S e ∧ orderOf x = 2} where
  toFun b := ⟨(modelBaseEquiv S e b.val).val,
    (modelBaseEquiv S e b.val).property,
    ((Subgroup.orderOf_coe (modelBaseEquiv S e b.val)).trans
      ((modelBaseEquiv S e).orderOf_eq b.val)).trans b.property⟩
  invFun x := ⟨(modelBaseEquiv S e).symm ⟨x.val, x.property.1⟩,
    ((modelBaseEquiv S e).symm.orderOf_eq ⟨x.val, x.property.1⟩).trans
      ((Subgroup.orderOf_coe ⟨x.val, x.property.1⟩).symm.trans x.property.2)⟩
  left_inv b := Subtype.ext ((modelBaseEquiv S e).symm_apply_apply b.val)
  right_inv x := by
    apply Subtype.ext
    change ((modelBaseEquiv S e) ((modelBaseEquiv S e).symm
      ⟨x.val, x.property.1⟩)).val = x.val
    exact congrArg (fun z : modelBase S e => z.val)
      ((modelBaseEquiv S e).apply_symm_apply ⟨x.val, x.property.1⟩)

theorem modelBase_involutions_card (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card {x : G // x ∈ modelBase S e ∧ orderOf x = 2} = 3 := by
  rw [← Nat.card_congr (modelBaseInvolutionsEquiv S e)]
  exact base_involutions_card n hn

theorem original_Z_le_center (m : ℕ) : Original.Z m ≤ Subgroup.center (Wreath m) := by
  apply Subgroup.zpowers_le.mpr
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨⟨i, j, k⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m i j k * Original.a m = Original.a m * element m i j k
  rw [Original.a_eq]
  rcases swap_exponent_cases k with rfl | rfl
  · simp only [element_base_mul, add_comm]
  · rw [element_swap_mul, element_base_mul]
    simp only [add_comm, zero_add]

theorem modelCenterInV_le_center {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelCenter S e).subgroupOf (modelV S e) ≤ Subgroup.center (modelV S e) := by
  intro v hv
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp hv
  obtain ⟨q, hq, hqw⟩ := Subgroup.mem_map.mp w.property
  change (w : G) * (v : G) = (v : G) * (w : G)
  change wreathModelHom S e z = (v : G) at hzv
  rw [← hzv, ← hqw, ← map_mul, ← map_mul]
  exact congrArg (wreathModelHom S e)
    (Subgroup.mem_center_iff.mp (original_Z_le_center m hz) q)

instance modelCenterInV_normal {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    ((modelCenter S e).subgroupOf (modelV S e)).Normal :=
  Subgroup.normal_of_le_center (modelCenterInV_le_center S e)

@[expose] def modelVFullCenterQuotientEquiv (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelV S e ⧸ Subgroup.center (modelV S e) ≃*
      modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e) :=
  QuotientGroup.quotientMulEquivOfEq (modelV_center_eq_modelCenter_subgroup n hn S e)

theorem modelVFullCenterQuotientEquiv_mk (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (v : modelV S e) :
    modelVFullCenterQuotientEquiv n hn S e
      ((QuotientGroup.mk' (Subgroup.center (modelV S e))) v) =
        (QuotientGroup.mk' ((modelCenter S e).subgroupOf (modelV S e))) v := rfl

@[expose] def modelVFullCenterAction [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) →*
      MulAut (modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e)) :=
  (MulAut.congr (modelVFullCenterQuotientEquiv n hn S e)).toMonoidHom.comp
    (modelVActualQuotientAction S e)

theorem modelVFullCenterAction_mk [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) (v : modelV S e) :
    modelVFullCenterAction n hn S e g
      ((QuotientGroup.mk' ((modelCenter S e).subgroupOf (modelV S e))) v) =
        (QuotientGroup.mk' ((modelCenter S e).subgroupOf (modelV S e)))
          ((modelV S e).normalizerMonoidHom g v) := by
  change modelVFullCenterQuotientEquiv n hn S e
    (modelVActualQuotientAction S e g
      ((modelVFullCenterQuotientEquiv n hn S e).symm
        ((QuotientGroup.mk' ((modelCenter S e).subgroupOf (modelV S e))) v))) = _
  rw [← modelVFullCenterQuotientEquiv_mk n hn S e v, MulEquiv.symm_apply_apply,
    modelVActualQuotientAction_mk, modelVFullCenterQuotientEquiv_mk]

@[expose] def modelVNormalizerFullCenterQuotientAction [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e →*
      MulAut (modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e)) :=
  (MulAut.congr (modelVFullCenterQuotientEquiv n hn S e)).toMonoidHom.comp
    (modelVNormalizerActualQuotientAction n hn S e)

theorem modelVNormalizerFullCenterQuotientAction_injective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective (modelVNormalizerFullCenterQuotientAction n hn S e) :=
  (MulAut.congr (modelVFullCenterQuotientEquiv n hn S e)).injective.comp
    (modelVNormalizerActualQuotientAction_injective n hn S e)

theorem modelVNormalizerFullCenterQuotientAction_mk [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    modelVNormalizerFullCenterQuotientAction n hn S e
      ((QuotientGroup.mk' (modelVInnerCentralizer S e)) g) =
        modelVFullCenterAction n hn S e g := by
  change MulAut.congr (modelVFullCenterQuotientEquiv n hn S e)
    (modelVNormalizerActualQuotientAction n hn S e
      ((QuotientGroup.mk' (modelVInnerCentralizer S e)) g)) = _
  rw [modelVNormalizerActualQuotientAction_mk]
  rfl

@[expose] def modelVNormalizerFullCenterQuotientEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      (modelVNormalizerFullCenterQuotientAction n hn S e).range :=
  MonoidHom.ofInjective (modelVNormalizerFullCenterQuotientAction_injective n hn S e)

theorem modelVFullCenterAction_order [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    orderOf (modelVFullCenterAction n hn S e g) = orderOf (modelVQuotientAction S e g) :=
  ((MulAut.congr (modelVFullCenterQuotientEquiv n hn S e)).orderOf_eq _).trans
    (modelVActualQuotientAction_order n S e g)

theorem modelVFullCenterAction_cycles_nonzero [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3)
    (x : modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e)) (hx : x ≠ 1) :
    modelVFullCenterAction n hn S e g x ≠ x ∧
      modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x) ≠ x ∧
      modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x) ≠
        modelVFullCenterAction n hn S e g x ∧
      ∀ y : modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e), y ≠ 1 →
        y = x ∨ y = modelVFullCenterAction n hn S e g x ∨
          y = modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x) := by
  let E := modelVFullCenterQuotientEquiv n hn S e
  let a := modelVActualQuotientAction S e g
  let b := modelVFullCenterAction n hn S e g
  obtain ⟨x0, rfl⟩ := E.surjective x
  have hx0 : x0 ≠ 1 := by
    intro h
    apply hx
    rw [h, map_one]
  obtain ⟨hne, hne2, hne3, hcover⟩ :=
    modelVActualQuotientAction_cycles_nonzero n hn S e g horder x0 hx0
  have hmap (q) : b (E q) = E (a q) := by
    change E (a (E.symm (E q))) = _
    rw [MulEquiv.symm_apply_apply]
  change b (E x0) ≠ E x0 ∧ b (b (E x0)) ≠ E x0 ∧
    b (b (E x0)) ≠ b (E x0) ∧ ∀ y, y ≠ 1 →
      y = E x0 ∨ y = b (E x0) ∨ y = b (b (E x0))
  rw [hmap, hmap]
  refine ⟨fun h => hne (E.injective h), fun h => hne2 (E.injective h),
    fun h => hne3 (E.injective h), ?_⟩
  intro y hy
  obtain ⟨y0, rfl⟩ := E.surjective y
  have hy0 : y0 ≠ 1 := by
    intro h
    apply hy
    rw [h, map_one]
  rcases hcover y0 hy0 with h | h | h
  · exact Or.inl (congrArg E h)
  · exact Or.inr (Or.inl (congrArg E h))
  · exact Or.inr (Or.inr (congrArg E h))

theorem modelVFullCenterAction_image_alternatives [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (modelVNormalizerFullCenterQuotientAction n hn S e).range = 2 ∨
      Nonempty ((modelVNormalizerFullCenterQuotientAction n hn S e).range ≃*
        Equiv.Perm (Fin 3)) := by
  rcases modelVNormalizerQuotient_alternatives n hn S e with htwo | hsix
  · exact Or.inl ((Nat.card_congr
      (modelVNormalizerFullCenterQuotientEquiv n hn S e).toEquiv).symm.trans htwo)
  · obtain ⟨esix⟩ := hsix
    exact Or.inr ⟨(modelVNormalizerFullCenterQuotientEquiv n hn S e).symm.trans esix⟩

theorem modelVNormalizer_exists_full_center_odd_three_cycle [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    ∃ g : Subgroup.normalizer (modelV S e : Set G),
      (∃ k : ℕ, 0 < k ∧ orderOf g = 3 ^ k) ∧ Odd (orderOf g) ∧
      orderOf (modelVFullCenterAction n hn S e g) = 3 ∧
      (∀ x : modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e), x ≠ 1 →
        modelVFullCenterAction n hn S e g x ≠ x ∧
        modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x) ≠ x ∧
        modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x) ≠
          modelVFullCenterAction n hn S e g x ∧
        ∀ y : modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e), y ≠ 1 →
          y = x ∨ y = modelVFullCenterAction n hn S e g x ∨
            y = modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x)) ∧
      (∀ H : CyclicFourSubgroups (modelQ S e),
        let σ := cyclicFourAutomorphismAction (modelQAutomorphism n hn S e g)
        σ H ≠ H ∧ σ (σ H) ≠ H ∧ σ (σ H) ≠ σ H ∧
          ∀ J : CyclicFourSubgroups (modelQ S e), J = H ∨ J = σ H ∨ J = σ (σ H)) := by
  obtain ⟨g, hpower, hodd, horder⟩ :=
    modelVNormalizer_exists_odd_three_power_actor n hn S e hsix
  exact ⟨g, hpower, hodd, (modelVFullCenterAction_order n hn S e g).trans horder,
    modelVFullCenterAction_cycles_nonzero n hn S e g horder,
    modelQAutomorphism_cycles_cyclic_four n hn S e g horder⟩

theorem modelVNormalizer_swap_right_fusion [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    ∃ g : G, g ∈ Subgroup.normalizer (modelV S e : Set G) ∧
      (g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.x2 (2 ^ n)) ∨
      g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2))) := by
  obtain ⟨g, hg, h⟩ := modelVNormalizer_swap_fusion n hn S e hsix
  exact ⟨g⁻¹, (Subgroup.normalizer (modelV S e : Set G)).inv_mem hg, by
    simpa only [inv_inv] using h⟩

theorem modelVFullCenterQuotient_isKleinFour (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsKleinFour (modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e)) := by
  let E := (modelVCenterQuotientEquiv S e).trans (modelVFullCenterQuotientEquiv n hn S e)
  have h := original_v_center_quotient_isKleinFour n hn
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr E.toEquiv]
    exact h.card_four
  · rw [← Monoid.exponent_eq_of_mulEquiv E]
    exact h.exponent_two

theorem modelVFullCenterQuotient_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e)) = 4 :=
  (modelVFullCenterQuotient_isKleinFour n hn S e).card_four

theorem modelVFullCenterQuotient_nonidentity_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card {x : modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e) // x ≠ 1} = 3 := by
  let := modelVFullCenterQuotient_isKleinFour n hn S e
  exact CFSG.kleinFour_nonidentity_card _

structure ActualLocalNormalizerActions [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Prop where
  base_normalized_by_sylow :
    (S : Subgroup G) ≤ Subgroup.normalizer (modelBase S e : Set G)
  base_normalizer_sylow :
    (modelBaseNormalizerSylow S e :
      Subgroup (Subgroup.normalizer (modelBase S e : Set G))) =
        (S : Subgroup G).subgroupOf (Subgroup.normalizer (modelBase S e : Set G))
  base_quotient_alternatives :
    Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2 ∨
    Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))
  base_square_quotient_card :
    Nat.card (modelBase S e ⧸ squareSubgroup (modelBase S e)) = 4
  base_square_action_faithful :
    Function.Injective (modelBaseNormalizerSquareQuotientAction n (by omega) S e)
  base_involutions_card :
    Nat.card {x : G // x ∈ modelBase S e ∧ orderOf x = 2} = 3
  base_involutions_transitive :
    Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)) →
    ∀ x y : G, x ∈ modelBase S e → y ∈ modelBase S e →
      orderOf x = 2 → orderOf y = 2 →
        ∃ g : G, g ∈ Subgroup.normalizer (modelBase S e : Set G) ∧ g * x * g⁻¹ = y
  v_normalizer_sylow :
    (modelVNormalizerSylow n hn S e :
      Subgroup (Subgroup.normalizer (modelV S e : Set G))) =
        (S : Subgroup G).subgroupOf (Subgroup.normalizer (modelV S e : Set G))
  v_full_center :
    Subgroup.center (modelV S e) = (modelCenter S e).subgroupOf (modelV S e)
  v_full_center_quotient_card :
    Nat.card (modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e)) = 4
  v_full_center_nonidentity_card :
    Nat.card {x : modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e) // x ≠ 1} = 3
  v_normalizer_centralizes_center :
    Subgroup.normalizer (modelV S e : Set G) ≤ Subgroup.centralizer (modelCenter S e : Set G)
  v_quotient_denominator :
    modelVInnerCentralizer S e =
      (modelV S e ⊔ Subgroup.centralizer (modelV S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelV S e : Set G))
  v_quotient_alternatives :
    Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e) = 2 ∨
      Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
        Equiv.Perm (Fin 3))
  v_full_center_action_faithful :
    Function.Injective (modelVNormalizerFullCenterQuotientAction n hn S e)
  v_full_center_image_alternatives :
    Nat.card (modelVNormalizerFullCenterQuotientAction n hn S e).range = 2 ∨
      Nonempty ((modelVNormalizerFullCenterQuotientAction n hn S e).range ≃*
        Equiv.Perm (Fin 3))
  q_cyclic_four_card : Nat.card (CyclicFourSubgroups (modelQ S e)) = 3
  v_odd_three_actor :
    Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3)) →
    ∃ g : Subgroup.normalizer (modelV S e : Set G),
      (∃ k : ℕ, 0 < k ∧ orderOf g = 3 ^ k) ∧ Odd (orderOf g) ∧
      orderOf (modelVFullCenterAction n hn S e g) = 3 ∧
      (∀ x : modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e), x ≠ 1 →
        modelVFullCenterAction n hn S e g x ≠ x ∧
        modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x) ≠ x ∧
        modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x) ≠
          modelVFullCenterAction n hn S e g x ∧
        ∀ y : modelV S e ⧸ (modelCenter S e).subgroupOf (modelV S e), y ≠ 1 →
          y = x ∨ y = modelVFullCenterAction n hn S e g x ∨
            y = modelVFullCenterAction n hn S e g (modelVFullCenterAction n hn S e g x)) ∧
      (∀ H : CyclicFourSubgroups (modelQ S e),
        let σ := cyclicFourAutomorphismAction (modelQAutomorphism n hn S e g)
        σ H ≠ H ∧ σ (σ H) ≠ H ∧ σ (σ H) ≠ σ H ∧
          ∀ J : CyclicFourSubgroups (modelQ S e), J = H ∨ J = σ H ∨ J = σ (σ H))
  swapping_involution_fusion :
    Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3)) →
    ∃ g : G, g ∈ Subgroup.normalizer (modelV S e : Set G) ∧
      (g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.x2 (2 ^ n)) ∨
      g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)))
  base_order_two_replacement :
    Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2 →
    ∀ g : G, g ∈ Subgroup.normalizer (modelBase S e : Set G) →
      ∃ s : G, s ∈ (S : Subgroup G) ∧
        s ∈ Subgroup.normalizer (modelBase S e : Set G) ∧
          ∀ b ∈ modelBase S e, s⁻¹ * b * s = g⁻¹ * b * g
  v_order_two_replacement :
    Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2 →
    ∀ g : G, g ∈ Subgroup.normalizer (modelV S e : Set G) →
      ∃ s : G, s ∈ (S : Subgroup G) ∧
        s ∈ Subgroup.normalizer (modelV S e : Set G) ∧
          ∀ v ∈ modelV S e, s⁻¹ * v * s = g⁻¹ * v * g

theorem wreathed_actual_local_normalizer_actions [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : ActualLocalNormalizerActions n hn S e where
  base_normalized_by_sylow := sylow_le_modelBase_normalizer S e
  base_normalizer_sylow := modelBaseNormalizerSylow_coe S e
  base_quotient_alternatives := modelBaseNormalizerQuotient_alternatives n (by omega) S e
  base_square_quotient_card := modelBase_square_quotient_card n (by omega) S e
  base_square_action_faithful := modelBaseNormalizerSquareQuotientAction_injective n (by omega) S e
  base_involutions_card := modelBase_involutions_card n (by omega) S e
  base_involutions_transitive := modelBaseNormalizer_involutions_transitive n (by omega) S e
  v_normalizer_sylow := modelVNormalizerSylow_coe n hn S e
  v_full_center := modelV_center_eq_modelCenter_subgroup n hn S e
  v_full_center_quotient_card := modelVFullCenterQuotient_card n hn S e
  v_full_center_nonidentity_card := modelVFullCenterQuotient_nonidentity_card n hn S e
  v_normalizer_centralizes_center := modelVNormalizer_le_center_centralizer n hn S e
  v_quotient_denominator := modelVInnerCentralizer_eq S e
  v_quotient_alternatives := modelVNormalizerQuotient_alternatives n hn S e
  v_full_center_action_faithful := modelVNormalizerFullCenterQuotientAction_injective n hn S e
  v_full_center_image_alternatives := modelVFullCenterAction_image_alternatives n hn S e
  q_cyclic_four_card := modelQ_cyclic_four_card n hn S e
  v_odd_three_actor := modelVNormalizer_exists_full_center_odd_three_cycle n hn S e
  swapping_involution_fusion := modelVNormalizer_swap_right_fusion n hn S e
  base_order_two_replacement := modelBaseNormalizer_order_two_step_replacement S e
  v_order_two_replacement := modelVNormalizer_order_two_step_replacement n hn S e

end CFSG.Wreathed
