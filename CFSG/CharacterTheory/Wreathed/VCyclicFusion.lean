module

public import CFSG.CharacterTheory.Wreathed.CentricVCopies
public import CFSG.CharacterTheory.Wreathed.SubgroupDihedralQuotient
public import CFSG.GroupTheory.KleinFourAutomorphism
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v

@[expose] def CyclicFourSubgroups (K : Type u) [Group K] :=
  {H : Subgroup K // IsCyclic H ∧ Nat.card H = 4}

@[expose] def cyclicFourGenerator {K : Type u} [Group K] (H : CyclicFourSubgroups K) : K :=
  ((Subgroup.isCyclic_iff_exists_zpowers_eq_top H.val).mp H.property.1).choose

theorem cyclicFourGenerator_zpowers {K : Type u} [Group K] (H : CyclicFourSubgroups K) :
    Subgroup.zpowers (cyclicFourGenerator H) = H.val :=
  ((Subgroup.isCyclic_iff_exists_zpowers_eq_top H.val).mp H.property.1).choose_spec

theorem cyclicFourGenerator_order {K : Type u} [Group K] (H : CyclicFourSubgroups K) :
    orderOf (cyclicFourGenerator H) = 4 := by
  rw [← Nat.card_zpowers, cyclicFourGenerator_zpowers]
  exact H.property.2

theorem quaternion_order_four_noncentral (q : QuaternionGroup 2) (hq : orderOf q = 4) :
    q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 := by
  constructor
  · intro h
    rw [h, orderOf_one] at hq
    omega
  · intro h
    rw [h, QuaternionGroup.orderOf_a] at hq
    rw [show (2 : ZMod 4).val = 2 by decide] at hq
    norm_num at hq

theorem quaternion_cyclic_four_eq_iff (q r : QuaternionGroup 2)
    (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2)
    (hr : r ≠ 1 ∧ r ≠ QuaternionGroup.a 2) :
    Subgroup.zpowers q = Subgroup.zpowers r ↔
      q / r = 1 ∨ q / r = QuaternionGroup.a 2 := by
  constructor
  · intro h
    have hmem : q ∈ Subgroup.zpowers r := h ▸ Subgroup.mem_zpowers q
    rw [mem_zpowers_iff_mem_range_orderOf, quaternionEight_noncentral_order r hr] at hmem
    exact (show ∀ q r : QuaternionGroup 2,
      q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 → r ≠ 1 ∧ r ≠ QuaternionGroup.a 2 →
      q ∈ Finset.image (fun k : ℕ => r ^ k) (Finset.range 4) →
        q / r = 1 ∨ q / r = QuaternionGroup.a 2 by decide) q r hq hr hmem
  · intro h
    have hcases : q = r ∨ q = r⁻¹ :=
      (show ∀ q r : QuaternionGroup 2,
        r ≠ 1 ∧ r ≠ QuaternionGroup.a 2 →
        (q / r = 1 ∨ q / r = QuaternionGroup.a 2) → q = r ∨ q = r⁻¹ by decide) q r hr h
    rcases hcases with rfl | rfl
    · rfl
    · exact Subgroup.zpowers_inv

theorem quaternion_cover_projection_eq_iff {K : Type u} {E : Type v}
    [Group K] [Group E] (e : QuaternionGroup 2 ≃* K) (f : K →* E)
    (hker : ∀ q : QuaternionGroup 2, f (e q) = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2)
    (g h : K) (hg : orderOf g = 4) (hh : orderOf h = 4) :
    f g = f h ↔ Subgroup.zpowers g = Subgroup.zpowers h := by
  let q := e.symm g
  let r := e.symm h
  have hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 :=
    quaternion_order_four_noncentral q ((e.symm.orderOf_eq g).trans hg)
  have hr : r ≠ 1 ∧ r ≠ QuaternionGroup.a 2 :=
    quaternion_order_four_noncentral r ((e.symm.orderOf_eq h).trans hh)
  have hproject : f g = f h ↔ q / r = 1 ∨ q / r = QuaternionGroup.a 2 := by
    rw [← div_eq_one, ← map_div]
    have he : e (q / r) = g / h := by
      simp only [q, r, map_div, MulEquiv.apply_symm_apply]
    rw [← he, hker]
  rw [hproject, ← quaternion_cyclic_four_eq_iff q r hq hr]
  constructor
  · intro hqr
    have hmap := congrArg (fun H : Subgroup (QuaternionGroup 2) => H.map e.toMonoidHom) hqr
    simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      q, r, MulEquiv.apply_symm_apply] using hmap
  · intro hgh
    have hmap := congrArg (fun H : Subgroup K => H.map e.symm.toMonoidHom) hgh
    simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, q, r] using hmap

theorem quaternion_cover_projection_nonidentity {K : Type u} {E : Type v}
    [Group K] [Group E] (e : QuaternionGroup 2 ≃* K) (f : K →* E)
    (hker : ∀ q : QuaternionGroup 2, f (e q) = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2)
    (g : K) (hg : orderOf g = 4) : f g ≠ 1 := by
  have hnoncentral := quaternion_order_four_noncentral (e.symm g)
    ((e.symm.orderOf_eq g).trans hg)
  intro h
  have h' : f (e (e.symm g)) = 1 := by rw [e.apply_symm_apply]; exact h
  exact (not_or.mpr hnoncentral) ((hker _).mp h')

@[expose] def cyclicFourProjection {K : Type u} {E : Type v}
    [Group K] [Group E] (e : QuaternionGroup 2 ≃* K) (f : K →* E)
    (hker : ∀ q : QuaternionGroup 2, f (e q) = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2) :
    CyclicFourSubgroups K → {x : E // x ≠ 1} :=
  fun H => ⟨f (cyclicFourGenerator H),
    quaternion_cover_projection_nonidentity e f hker _ (cyclicFourGenerator_order H)⟩

theorem cyclicFourProjection_generator {K : Type u} {E : Type v}
    [Group K] [Group E] (e : QuaternionGroup 2 ≃* K) (f : K →* E)
    (hker : ∀ q : QuaternionGroup 2, f (e q) = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2)
    (H : CyclicFourSubgroups K) (g : K) (hg : Subgroup.zpowers g = H.val) :
    (cyclicFourProjection e f hker H).val = f g := by
  have horder : orderOf g = 4 := by rw [← Nat.card_zpowers, hg]; exact H.property.2
  exact (quaternion_cover_projection_eq_iff e f hker _ _
    (cyclicFourGenerator_order H) horder).mpr ((cyclicFourGenerator_zpowers H).trans hg.symm)

theorem cyclicFourProjection_injective {K : Type u} {E : Type v}
    [Group K] [Group E] (e : QuaternionGroup 2 ≃* K) (f : K →* E)
    (hker : ∀ q : QuaternionGroup 2, f (e q) = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2) :
    Function.Injective (cyclicFourProjection e f hker) := by
  intro H J hHJ
  apply Subtype.ext
  have h := (quaternion_cover_projection_eq_iff e f hker _ _
    (cyclicFourGenerator_order H) (cyclicFourGenerator_order J)).mp
      (congrArg Subtype.val hHJ)
  rwa [cyclicFourGenerator_zpowers, cyclicFourGenerator_zpowers] at h

theorem cyclicFourProjection_surjective {K : Type u} {E : Type v}
    [Group K] [Group E] (e : QuaternionGroup 2 ≃* K) (f : K →* E)
    (hker : ∀ q : QuaternionGroup 2, f (e q) = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2)
    (hsurj : Function.Surjective f) : Function.Surjective (cyclicFourProjection e f hker) := by
  intro x
  obtain ⟨g, hg⟩ := hsurj x.val
  have hnoncentral : e.symm g ≠ 1 ∧ e.symm g ≠ QuaternionGroup.a 2 := by
    apply not_or.mp
    intro h
    apply x.property
    rw [← hg, ← e.apply_symm_apply g]
    exact (hker _).mpr h
  have horder : orderOf g = 4 :=
    (e.symm.orderOf_eq g).symm.trans (quaternionEight_noncentral_order _ hnoncentral)
  let H : CyclicFourSubgroups K := ⟨Subgroup.zpowers g,
    inferInstance, (Nat.card_zpowers g).trans horder⟩
  refine ⟨H, Subtype.ext ?_⟩
  exact (cyclicFourProjection_generator e f hker H g rfl).trans hg

@[expose] def cyclicFourProjectionEquiv {K : Type u} {E : Type v}
    [Group K] [Group E] (e : QuaternionGroup 2 ≃* K) (f : K →* E)
    (hker : ∀ q : QuaternionGroup 2, f (e q) = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2)
    (hsurj : Function.Surjective f) : CyclicFourSubgroups K ≃ {x : E // x ≠ 1} :=
  Equiv.ofBijective (cyclicFourProjection e f hker)
    ⟨cyclicFourProjection_injective e f hker, cyclicFourProjection_surjective e f hker hsurj⟩

@[expose] def subgroupCenterProjection {A : Type u} [Group A]
    (H K : Subgroup A) (hHK : H ≤ K) : H →* K ⧸ Subgroup.center K :=
  (QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion hHK)

theorem original_quaternion_le_v (n : ℕ) (hn : 2 ≤ n) :
    Original.Q (2 ^ n) ≤ Original.V (2 ^ n) := by
  rw [(wreath_center_involution_and_quaternion_coordinates n hn).central_product]
  exact le_sup_right

@[expose] def originalQuaternionCenterProjection (n : ℕ) (hn : 2 ≤ n) :
    Original.Q (2 ^ n) →* Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n)) :=
  subgroupCenterProjection _ _ (original_quaternion_le_v n hn)

theorem original_quaternion_projection_cover (n : ℕ) (hn : 2 ≤ n) :
    ∃ e : QuaternionGroup 2 ≃* Original.Q (2 ^ n),
      (∀ q : QuaternionGroup 2, originalQuaternionCenterProjection n hn (e q) = 1 ↔
        q = 1 ∨ q = QuaternionGroup.a 2) ∧
      Function.Surjective (originalQuaternionCenterProjection n hn) := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  unfold originalQuaternionCenterProjection
  generalize original_quaternion_le_v n hn = hle
  revert hle
  rw [hm, Original.Q_atQuarter, Original.V_atQuarter]
  intro hle
  let l := 2 ^ (n - 2)
  have hl : 0 < l := pow_pos (by decide) _
  refine ⟨quaternionEightRangeEquiv l hl, ?_, ?_⟩
  · intro q
    change vQuotientQuaternionProjection l q = 1 ↔ _
    exact vQuotientQuaternionProjection_eq_one_iff l hl q
  · intro x
    obtain ⟨q, rfl⟩ := vQuotientQuaternionProjection_surjective l hl x
    exact ⟨quaternionEightRangeEquiv l hl q, rfl⟩

@[expose] def originalQuaternionProjectionEquiv (n : ℕ) (hn : 2 ≤ n) :
    QuaternionGroup 2 ≃* Original.Q (2 ^ n) :=
  (original_quaternion_projection_cover n hn).choose

theorem originalQuaternionCenterProjection_kernel (n : ℕ) (hn : 2 ≤ n)
    (q : QuaternionGroup 2) :
    originalQuaternionCenterProjection n hn (originalQuaternionProjectionEquiv n hn q) = 1 ↔
      q = 1 ∨ q = QuaternionGroup.a 2 :=
  (original_quaternion_projection_cover n hn).choose_spec.1 q

theorem originalQuaternionCenterProjection_surjective (n : ℕ) (hn : 2 ≤ n) :
    Function.Surjective (originalQuaternionCenterProjection n hn) :=
  (original_quaternion_projection_cover n hn).choose_spec.2

@[expose] def originalCyclicFourQuotientEquiv (n : ℕ) (hn : 2 ≤ n) :
    CyclicFourSubgroups (Original.Q (2 ^ n)) ≃
      {x : Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n)) // x ≠ 1} :=
  cyclicFourProjectionEquiv (originalQuaternionProjectionEquiv n hn)
    (originalQuaternionCenterProjection n hn)
    (originalQuaternionCenterProjection_kernel n hn)
    (originalQuaternionCenterProjection_surjective n hn)

theorem originalCyclicFourQuotientEquiv_generator (n : ℕ) (hn : 2 ≤ n)
    (H : CyclicFourSubgroups (Original.Q (2 ^ n)))
    (g : Original.Q (2 ^ n)) (hg : Subgroup.zpowers g = H.val) :
    (originalCyclicFourQuotientEquiv n hn H).val =
      originalQuaternionCenterProjection n hn g :=
  cyclicFourProjection_generator (originalQuaternionProjectionEquiv n hn)
    (originalQuaternionCenterProjection n hn) (originalQuaternionCenterProjection_kernel n hn)
    H g hg

theorem original_v_quotient_card_four (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) = 4 := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hcard := (Subgroup.center (Original.V (2 ^ n))).card_eq_card_quotient_mul_card_subgroup
  rw [hstructure.central_product_card, original_v_center_card n hn] at hcard
  nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) n]

theorem original_v_quotient_isKleinFour (n : ℕ) (hn : 2 ≤ n) :
    IsKleinFour (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hcenter : Subgroup.center (Wreath (2 ^ n)) ≤ Original.V (2 ^ n) := by
    rw [hstructure.center, hstructure.central_product]
    exact le_sup_left
  obtain ⟨k, hk, _, ⟨e⟩, hcard⟩ := nonabelian_subgroup_center_quotient_dihedral_card hn
    (Original.V (2 ^ n)) (original_v_is_nonabelian n hn) hcenter
  have hkone : k = 1 := by
    by_contra hne
    have hpow : 8 ≤ 2 ^ (k + 1) := by
      calc
        8 = 2 ^ 3 := by decide
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hstructure.central_product_card] at hcard
    nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) n]
  subst k
  refine ⟨original_v_quotient_card_four n hn, ?_⟩
  rw [Monoid.exponent_eq_of_mulEquiv e]
  exact IsKleinFour.exponent_two (G := DihedralGroup 2)

theorem original_quaternion_cyclic_four_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (CyclicFourSubgroups (Original.Q (2 ^ n))) = 3 := by
  let := original_v_quotient_isKleinFour n hn
  rw [Nat.card_congr (originalCyclicFourQuotientEquiv n hn)]
  exact CFSG.kleinFour_nonidentity_card _

@[expose] def cyclicFourAutomorphismAction {K : Type u} [Group K]
    (a : MulAut K) : Equiv.Perm (CyclicFourSubgroups K) :=
  a.mapSubgroup.toEquiv.subtypeEquiv (by
    intro H
    change (IsCyclic H ∧ Nat.card H = 4) ↔
      (IsCyclic (H.map a.toMonoidHom) ∧ Nat.card (H.map a.toMonoidHom) = 4)
    constructor
    · rintro ⟨hcyclic, hcard⟩
      exact ⟨(a.subgroupMap H).isCyclic.mp hcyclic,
        (Subgroup.card_map_of_injective a.injective).trans hcard⟩
    · rintro ⟨hcyclic, hcard⟩
      exact ⟨(a.subgroupMap H).isCyclic.mpr hcyclic,
        (Subgroup.card_map_of_injective a.injective).symm.trans hcard⟩)

theorem cyclicFourAutomorphismAction_coe {K : Type u} [Group K]
    (a : MulAut K) (H : CyclicFourSubgroups K) :
    (cyclicFourAutomorphismAction a H).val = H.val.map a.toMonoidHom := rfl

theorem cyclicFourProjection_intertwines {K : Type u} {E : Type v}
    [Group K] [Group E] (e : QuaternionGroup 2 ≃* K) (f : K →* E)
    (hker : ∀ q : QuaternionGroup 2, f (e q) = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2)
    (a : MulAut K) (b : MulAut E) (hintertwine : ∀ g : K, f (a g) = b (f g))
    (H : CyclicFourSubgroups K) :
    (cyclicFourProjection e f hker (cyclicFourAutomorphismAction a H)).val =
      b (cyclicFourProjection e f hker H).val := by
  rw [cyclicFourProjection_generator e f hker _ (a (cyclicFourGenerator H)) (by
    rw [cyclicFourAutomorphismAction_coe]
    exact ((a.toMonoidHom.map_zpowers (cyclicFourGenerator H)).symm).trans
      (congrArg (fun K : Subgroup K => K.map a.toMonoidHom) (cyclicFourGenerator_zpowers H)))]
  exact hintertwine _

theorem quaternionInsideOriginalV_characteristic (n : ℕ) (hn : 2 ≤ n) :
    ((Original.Q (2 ^ n)).subgroupOf (Original.V (2 ^ n))).Characteristic :=
  (wreath_center_involution_and_quaternion_coordinates n hn).quaternion_characteristic

@[expose] def originalQuaternionInclusionEquiv (n : ℕ) (hn : 2 ≤ n) :
    Original.Q (2 ^ n) ≃*
      (Original.Q (2 ^ n)).subgroupOf (Original.V (2 ^ n)) :=
  (Subgroup.subgroupOfEquivOfLe (original_quaternion_le_v n hn)).symm

@[expose] def originalQuaternionAutomorphism (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) : MulAut (Original.Q (2 ^ n)) :=
  letI := quaternionInsideOriginalV_characteristic n hn
  MulAut.congr (originalQuaternionInclusionEquiv n hn).symm
    (CFSG.FiveTransitive.CharacteristicAutomorphism.restrict
      ((Original.Q (2 ^ n)).subgroupOf (Original.V (2 ^ n))) a)

theorem originalQuaternionAutomorphism_coe (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) (g : Original.Q (2 ^ n)) :
    (originalQuaternionAutomorphism n hn a g).val =
      (a (Subgroup.inclusion (original_quaternion_le_v n hn) g)).val := by
  rfl

@[expose] def originalVQuotientAutomorphism (n : ℕ)
    (a : MulAut (Original.V (2 ^ n))) :
    MulAut (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) :=
  CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
    (Subgroup.center (Original.V (2 ^ n))) a

theorem originalVQuotientAutomorphism_mk (n : ℕ)
    (a : MulAut (Original.V (2 ^ n))) (g : Original.V (2 ^ n)) :
    originalVQuotientAutomorphism n a
      ((QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) g) =
        (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) (a g) :=
  CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk _ a g

theorem originalVQuotientAutomorphism_pow (n : ℕ)
    (a : MulAut (Original.V (2 ^ n))) (i : ℕ) :
    originalVQuotientAutomorphism n (a ^ i) = originalVQuotientAutomorphism n a ^ i :=
  map_pow (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
    (Subgroup.center (Original.V (2 ^ n)))) a i

theorem originalVQuotientAutomorphism_pow_mk (n : ℕ)
    (a : MulAut (Original.V (2 ^ n))) (i : ℕ) (g : Original.V (2 ^ n)) :
    (originalVQuotientAutomorphism n a ^ i)
      ((QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) g) =
        (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) ((a ^ i) g) := by
  rw [← originalVQuotientAutomorphism_pow, originalVQuotientAutomorphism_mk]

theorem originalQuaternionCenterProjection_intertwines (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) (g : Original.Q (2 ^ n)) :
    originalQuaternionCenterProjection n hn (originalQuaternionAutomorphism n hn a g) =
      originalVQuotientAutomorphism n a (originalQuaternionCenterProjection n hn g) := by
  change (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n))))
    (Subgroup.inclusion (original_quaternion_le_v n hn)
      (originalQuaternionAutomorphism n hn a g)) = _
  rw [show Subgroup.inclusion (original_quaternion_le_v n hn)
      (originalQuaternionAutomorphism n hn a g) =
      a (Subgroup.inclusion (original_quaternion_le_v n hn) g) from
        Subtype.ext (originalQuaternionAutomorphism_coe n hn a g)]
  exact (originalVQuotientAutomorphism_mk n a _).symm

theorem originalCyclicFourQuotientEquiv_intertwines (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) (H : CyclicFourSubgroups (Original.Q (2 ^ n))) :
    (originalCyclicFourQuotientEquiv n hn
      (cyclicFourAutomorphismAction (originalQuaternionAutomorphism n hn a) H)).val =
        originalVQuotientAutomorphism n a (originalCyclicFourQuotientEquiv n hn H).val :=
  cyclicFourProjection_intertwines (originalQuaternionProjectionEquiv n hn)
    (originalQuaternionCenterProjection n hn) (originalQuaternionCenterProjection_kernel n hn)
    (originalQuaternionAutomorphism n hn a) (originalVQuotientAutomorphism n a)
    (originalQuaternionCenterProjection_intertwines n hn a) H

theorem originalCyclicFourAction_congr (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) :
    (originalCyclicFourQuotientEquiv n hn).permCongrHom
      (cyclicFourAutomorphismAction (originalQuaternionAutomorphism n hn a)) =
        CFSG.nonidentityAutomorphismAction
          (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n)))
          (originalVQuotientAutomorphism n a) := by
  ext x
  change (originalCyclicFourQuotientEquiv n hn
    (cyclicFourAutomorphismAction (originalQuaternionAutomorphism n hn a)
      ((originalCyclicFourQuotientEquiv n hn).symm x))).val =
        originalVQuotientAutomorphism n a x.val
  rw [originalCyclicFourQuotientEquiv_intertwines, Equiv.apply_symm_apply]

theorem originalCyclicFourAction_order_three (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3) :
    orderOf (cyclicFourAutomorphismAction (originalQuaternionAutomorphism n hn a)) = 3 := by
  let := original_v_quotient_isKleinFour n hn
  rw [← (originalCyclicFourQuotientEquiv n hn).permCongrHom.orderOf_eq,
    originalCyclicFourAction_congr]
  change orderOf (CFSG.kleinFourAutomorphismEquiv _ (originalVQuotientAutomorphism n a)) = 3
  rw [MulEquiv.orderOf_eq, horder]

theorem originalVQuotientAutomorphism_cycles_three (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3)
    (x : Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) (hx : x ≠ 1) :
    originalVQuotientAutomorphism n a x ≠ x ∧
      originalVQuotientAutomorphism n a (originalVQuotientAutomorphism n a x) ≠ x ∧
      originalVQuotientAutomorphism n a (originalVQuotientAutomorphism n a x) ≠
        originalVQuotientAutomorphism n a x ∧
      ∀ y : Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n)),
        y ≠ 1 → y = x ∨ y = originalVQuotientAutomorphism n a x ∨
          y = originalVQuotientAutomorphism n a (originalVQuotientAutomorphism n a x) := by
  let := original_v_quotient_isKleinFour n hn
  exact CFSG.kleinFour_order_three_cycle _ (originalVQuotientAutomorphism n a) horder x hx

theorem originalQuaternionAutomorphism_cycles_cyclic_four (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3)
    (H : CyclicFourSubgroups (Original.Q (2 ^ n))) :
    let σ := cyclicFourAutomorphismAction (originalQuaternionAutomorphism n hn a)
    σ H ≠ H ∧ σ (σ H) ≠ H ∧ σ (σ H) ≠ σ H ∧
      ∀ J : CyclicFourSubgroups (Original.Q (2 ^ n)), J = H ∨ J = σ H ∨ J = σ (σ H) := by
  let σ := cyclicFourAutomorphismAction (originalQuaternionAutomorphism n hn a)
  let e := originalCyclicFourQuotientEquiv n hn
  let b := originalVQuotientAutomorphism n a
  have hσ : ∀ H, (e (σ H)).val = b (e H).val :=
    originalCyclicFourQuotientEquiv_intertwines n hn a
  have hσσ : (e (σ (σ H))).val = b (b (e H).val) := by
    rw [hσ, hσ]
  obtain ⟨hne, hne2, hne3, hcover⟩ :=
    originalVQuotientAutomorphism_cycles_three n hn a horder (e H).val (e H).property
  change σ H ≠ H ∧ σ (σ H) ≠ H ∧ σ (σ H) ≠ σ H ∧
    ∀ J, J = H ∨ J = σ H ∨ J = σ (σ H)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← hσ H, h]
  · intro h
    apply hne2
    rw [← hσσ, h]
  · intro h
    apply hne3
    rw [← hσσ, ← hσ H, h]
  · intro J
    rcases hcover (e J).val (e J).property with h | h | h
    · exact Or.inl (e.injective (Subtype.ext h))
    · exact Or.inr (Or.inl (e.injective (Subtype.ext (h.trans (hσ H).symm))))
    · exact Or.inr (Or.inr (e.injective (Subtype.ext (h.trans hσσ.symm))))

@[expose] def originalVSwap (m : ℕ) : Original.V m :=
  ⟨Original.z m, Subgroup.subset_closure (by simp)⟩

@[expose] def originalVHalf (m : ℕ) : Original.V m :=
  ⟨Original.x2 m, Subgroup.subset_closure (by simp)⟩

@[expose] def originalVSwapCoset (m : ℕ) : Original.V m ⧸ Subgroup.center (Original.V m) :=
  (QuotientGroup.mk' (Subgroup.center (Original.V m))) (originalVSwap m)

@[expose] def originalVHalfCoset (m : ℕ) : Original.V m ⧸ Subgroup.center (Original.V m) :=
  (QuotientGroup.mk' (Subgroup.center (Original.V m))) (originalVHalf m)

@[expose] def quarterVHalf (l : ℕ) : vSubgroup l :=
  ⟨element (4 * l) (2 * l : ℕ) 0 0, by simp⟩

@[expose] def quarterVSwap (l : ℕ) : vSubgroup l :=
  ⟨element (4 * l) 0 0 1, by simp⟩

theorem quarterVHalf_square (l : ℕ) : quarterVHalf l ^ 2 = 1 := by
  apply Subtype.ext
  change element (4 * l) (2 * l : ℕ) 0 0 ^ 2 = 1
  rw [element_base_pow, two_nsmul, twice_quarter_add_self, smul_zero, element_zero]

theorem quarter_swap_half_cosets_distinct (l : ℕ) (hl : 0 < l) :
    ((QuotientGroup.mk' (Subgroup.center (vSubgroup l))) (quarterVSwap l)) ≠ 1 ∧
      ((QuotientGroup.mk' (Subgroup.center (vSubgroup l))) (quarterVHalf l)) ≠ 1 ∧
      ((QuotientGroup.mk' (Subgroup.center (vSubgroup l))) (quarterVSwap l)) ≠
        ((QuotientGroup.mk' (Subgroup.center (vSubgroup l))) (quarterVHalf l)) := by
  have hhalf := half_quarter_ne_zero l hl
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hc := (QuotientGroup.eq_one_iff (quarterVSwap l)).mp h
    rw [v_mem_center_iff l hl] at hc
    change element (4 * l) 0 0 1 ∈ Subgroup.center (Wreath (4 * l)) at hc
    rw [element_mem_center_iff _ (by omega)] at hc
    exact one_ne_zero hc.1
  · intro h
    have hc := (QuotientGroup.eq_one_iff (quarterVHalf l)).mp h
    rw [v_mem_center_iff l hl] at hc
    change element (4 * l) (2 * l : ℕ) 0 0 ∈ Subgroup.center (Wreath (4 * l)) at hc
    rw [element_mem_center_iff _ (by omega)] at hc
    exact hhalf hc.2
  · intro h
    have hc := QuotientGroup.eq_iff_div_mem.mp h
    rw [v_mem_center_iff l hl] at hc
    change element (4 * l) 0 0 1 * (element (4 * l) (2 * l : ℕ) 0 0)⁻¹ ∈
      Subgroup.center (Wreath (4 * l)) at hc
    rw [element_base_inv, element_swap_mul, add_zero, zero_add,
      element_mem_center_iff _ (by omega)] at hc
    exact one_ne_zero hc.1

theorem quarter_involution_in_half_coset (l : ℕ) (hl : 0 < l) (g : vSubgroup l)
    (horder : orderOf g = 2)
    (hcoset : (QuotientGroup.mk' (Subgroup.center (vSubgroup l))) g =
      (QuotientGroup.mk' (Subgroup.center (vSubgroup l))) (quarterVHalf l)) :
    g.val = element (4 * l) (2 * l : ℕ) 0 0 ∨
      g.val = element (4 * l) 0 (2 * l : ℕ) 0 := by
  have hc := QuotientGroup.eq_iff_div_mem.mp hcoset
  rw [v_mem_center_iff l hl] at hc
  obtain ⟨⟨a, b, e⟩, hcoord⟩ := (coordinateEquiv (4 * l)).symm.surjective (g / quarterVHalf l).val
  change element (4 * l) a b e = (g / quarterVHalf l).val at hcoord
  rw [← hcoord, element_mem_center_iff _ (by omega)] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have hform : g.val = element (4 * l) (a + (2 * l : ℕ)) a 0 := by
    calc
      g.val = (g / quarterVHalf l).val * (quarterVHalf l).val := by
        change g.val = (g.val / (quarterVHalf l).val) * (quarterVHalf l).val
        exact (div_mul_cancel _ _).symm
      _ = element (4 * l) a a 0 * element (4 * l) (2 * l : ℕ) 0 0 := by rw [← hcoord]; rfl
      _ = element (4 * l) (a + (2 * l : ℕ)) a 0 := by rw [element_base_mul, add_zero]
  have hsquare : g.val ^ 2 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [horder] at h
    exact congrArg Subtype.val h
  rw [hform, element_base_pow, element_base_eq_one_iff] at hsquare
  rcases (two_smul_eq_zero_half_quarter l hl a).mp hsquare.2 with rfl | rfl
  · exact Or.inl (by simpa only [zero_add] using hform)
  · exact Or.inr (by simpa only [twice_quarter_add_self] using hform)

theorem original_swap_half_cosets_distinct (n : ℕ) (hn : 2 ≤ n) :
    originalVSwapCoset (2 ^ n) ≠ 1 ∧ originalVHalfCoset (2 ^ n) ≠ 1 ∧
      originalVSwapCoset (2 ^ n) ≠ originalVHalfCoset (2 ^ n) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hm : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have hcentral (g : Original.V (2 ^ n))
      (hg : g ∈ Subgroup.center (Original.V (2 ^ n))) :
      g.val ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [hstructure.center, ← hstructure.central_product_center]
    exact ⟨g, hg, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hc := hcentral _ ((QuotientGroup.eq_one_iff _).mp h)
    change element (2 ^ n) 0 0 1 ∈ Subgroup.center (Wreath (2 ^ n)) at hc
    exact one_ne_zero ((element_mem_center_iff _ hm _ _ _).mp hc).1
  · intro h
    have hc := hcentral _ ((QuotientGroup.eq_one_iff _).mp h)
    change Original.x2 (2 ^ n) ∈ Subgroup.center (Wreath (2 ^ n)) at hc
    rw [Original.x2_eq, element_mem_center_iff _ hm] at hc
    have hx : Original.x2 (2 ^ n) = 1 := by rw [Original.x2_eq, hc.2, element_zero]
    have ho := hstructure.involution_orders.2.1
    rw [hx, orderOf_one] at ho
    omega
  · intro h
    have hc := hcentral _ (QuotientGroup.eq_iff_div_mem.mp h)
    change Original.z (2 ^ n) * (Original.x2 (2 ^ n))⁻¹ ∈
      Subgroup.center (Wreath (2 ^ n)) at hc
    rw [Original.z, Original.x2_eq, element_base_inv, element_swap_mul, add_zero,
      zero_add, element_mem_center_iff _ hm] at hc
    exact one_ne_zero hc.1

theorem vCyclic_twice_half_height (n : ℕ) (hn : 1 ≤ n) :
    (((2 ^ n / 2 : ℕ) : ZMod (2 ^ n))) + (2 ^ n / 2 : ℕ) = 0 := by
  have hhalf : 2 ^ n / 2 + 2 ^ n / 2 = 2 ^ n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < (2 : ℕ))]
    omega
  rw [← Nat.cast_add, hhalf, ZMod.natCast_self]

theorem vCyclic_two_smul_eq_zero_height (n : ℕ) (hn : 1 ≤ n) (c : ZMod (2 ^ n)) :
    2 • c = 0 ↔ c = 0 ∨ c = (2 ^ n / 2 : ℕ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by
    rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < (2 : ℕ))]
  rw [hhalf]
  exact two_smul_eq_zero_iff k c

theorem original_involution_in_half_coset (n : ℕ) (hn : 2 ≤ n)
    (g : Original.V (2 ^ n)) (horder : orderOf g = 2)
    (hcoset : (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) g =
      originalVHalfCoset (2 ^ n)) :
    g.val = Original.x2 (2 ^ n) ∨
      g.val = Original.t (2 ^ n) ^ (2 ^ n / 2) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hm : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have hc : (g / originalVHalf (2 ^ n)).val ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [hstructure.center, ← hstructure.central_product_center]
    exact ⟨g / originalVHalf (2 ^ n), QuotientGroup.eq_iff_div_mem.mp hcoset, rfl⟩
  obtain ⟨⟨a, b, e⟩, hcoord⟩ :=
    (coordinateEquiv (2 ^ n)).symm.surjective (g / originalVHalf (2 ^ n)).val
  change element (2 ^ n) a b e = (g / originalVHalf (2 ^ n)).val at hcoord
  rw [← hcoord, element_mem_center_iff _ hm] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have hform : g.val = element (2 ^ n) (a + (2 ^ n / 2 : ℕ)) a 0 := by
    calc
      g.val = (g / originalVHalf (2 ^ n)).val * (originalVHalf (2 ^ n)).val := by
        change g.val = (g.val / (originalVHalf (2 ^ n)).val) * (originalVHalf (2 ^ n)).val
        exact (div_mul_cancel _ _).symm
      _ = element (2 ^ n) a a 0 * Original.x2 (2 ^ n) := by rw [← hcoord]; rfl
      _ = element (2 ^ n) (a + (2 ^ n / 2 : ℕ)) a 0 := by
        rw [Original.x2_eq, element_base_mul, add_zero]
  have hsquare : g.val ^ 2 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [horder] at h
    exact congrArg Subtype.val h
  rw [hform, element_base_pow, element_base_eq_one_iff] at hsquare
  rcases (vCyclic_two_smul_eq_zero_height n (by omega) a).mp hsquare.2 with rfl | rfl
  · exact Or.inl (by simpa only [zero_add, Original.x2_eq] using hform)
  · exact Or.inr (by simpa only [vCyclic_twice_half_height n (by omega), Original.t,
      element_base_pow, nsmul_eq_mul, mul_zero, mul_one] using hform)

theorem originalVSwap_order (m : ℕ) : orderOf (originalVSwap m) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact Original.orderOf_z m

theorem originalVAutomorphism_swap_half_endpoint (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (hcoset : originalVQuotientAutomorphism n a (originalVSwapCoset (2 ^ n)) =
      originalVHalfCoset (2 ^ n)) :
    (a (originalVSwap (2 ^ n))).val = Original.x2 (2 ^ n) ∨
      (a (originalVSwap (2 ^ n))).val = Original.t (2 ^ n) ^ (2 ^ n / 2) := by
  apply original_involution_in_half_coset n hn
  · exact (a.orderOf_eq _).trans (originalVSwap_order _)
  · exact (originalVQuotientAutomorphism_mk n a _).symm.trans hcoset

theorem originalVQuotientAutomorphism_swap_reaches_half (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3) :
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧
      (originalVQuotientAutomorphism n a ^ i) (originalVSwapCoset (2 ^ n)) =
        originalVHalfCoset (2 ^ n) := by
  obtain ⟨hswap, hhalf, hdistinct⟩ := original_swap_half_cosets_distinct n hn
  obtain ⟨_, _, _, hcover⟩ := originalVQuotientAutomorphism_cycles_three n hn a horder
    (originalVSwapCoset (2 ^ n)) hswap
  rcases hcover (originalVHalfCoset (2 ^ n)) hhalf with h | h | h
  · exact False.elim (hdistinct h.symm)
  · exact ⟨1, Or.inl rfl, by simpa only [pow_one] using h.symm⟩
  · exact ⟨2, Or.inr rfl, by simpa only [pow_two, MulAut.mul_apply] using h.symm⟩

theorem originalVAutomorphism_order_three_swap_endpoint (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3) :
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧
      (((a ^ i) (originalVSwap (2 ^ n))).val = Original.x2 (2 ^ n) ∨
        ((a ^ i) (originalVSwap (2 ^ n))).val = Original.t (2 ^ n) ^ (2 ^ n / 2)) := by
  obtain ⟨i, hi, hcoset⟩ := originalVQuotientAutomorphism_swap_reaches_half n hn a horder
  refine ⟨i, hi, originalVAutomorphism_swap_half_endpoint n hn (a ^ i) ?_⟩
  rwa [originalVQuotientAutomorphism_pow]

end CFSG.Wreathed
