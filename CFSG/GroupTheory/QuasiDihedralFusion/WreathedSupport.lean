module

public import CFSG.CharacterTheory.Wreathed.BrauerWongBaseNormalizer
public import CFSG.GroupTheory.QuasiDihedralFusion.Defs

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Wreathed CFSG.Wreathed.BrauerWong
open scoped commutatorElement

universe u

variable {H : Type u} [Group H] {n : ℕ}

section Indices

theorem automizerIndex_modelBase (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    automizerIndex (modelBase S e) =
      Nat.card (Subgroup.normalizer (modelBase S e : Set H) ⧸
        (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
          (Subgroup.normalizer (modelBase S e : Set H))) := rfl

theorem outerAutomizerIndex_modelV (S : Sylow 2 H) (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    outerAutomizerIndex (modelV S e) =
      Nat.card (Subgroup.normalizer (modelV S e : Set H) ⧸ modelVInnerCentralizer S e) := by
  rw [outerAutomizerIndex, Subgroup.relIndex, Subgroup.subgroupOf_sup Subgroup.le_normalizer
    (Subgroup.centralizer_le_normalizer (modelV S e : Set H))]
  rfl

theorem card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

end Indices

section Model

theorem base_inf_Y_eq (hn : 2 ≤ n) :
    baseSubgroup (2 ^ n) ⊓ Original.Y (2 ^ n) = Subgroup.zpowers (Original.r (2 ^ n)) := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hbase : (baseSubgroup (2 ^ n)).Normal := by
    unfold baseSubgroup
    infer_instance
  have hrY : Original.r (2 ^ n) ∈ Original.Y (2 ^ n) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hrU : Original.r (2 ^ n) ∈ baseSubgroup (2 ^ n) := by
    rw [Original.r_eq, element_mem_base]
  have hdY : Original.d (2 ^ n) ∈ Original.Y (2 ^ n) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdU : Original.d (2 ^ n) ∉ baseSubgroup (2 ^ n) := by
    rw [Original.d_eq, element_mem_base]
    decide
  have hidx2 : (baseSubgroup (2 ^ n)).index = 2 := by
    rw [← Original.U_eq]
    exact hstr.base_index
  have hindex : (baseSubgroup (2 ^ n)).relIndex (Original.Y (2 ^ n)) = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal (baseSubgroup (2 ^ n)) (Original.Y (2 ^ n))
    rw [hidx2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      rw [Subgroup.relIndex_eq_one] at h
      exact hdU (h hdY)
    · exact h
  have hcard : Nat.card (baseSubgroup (2 ^ n) ⊓ Original.Y (2 ^ n) : Subgroup _) = 2 ^ n := by
    have h := Subgroup.card_mul_index ((baseSubgroup (2 ^ n)).subgroupOf (Original.Y (2 ^ n)))
    rw [← Subgroup.relIndex, hindex, hstr.quaternion_card] at h
    have hmap : ((baseSubgroup (2 ^ n)).subgroupOf (Original.Y (2 ^ n))).map
        (Original.Y (2 ^ n)).subtype = baseSubgroup (2 ^ n) ⊓ Original.Y (2 ^ n) :=
      Subgroup.subgroupOf_map_subtype _ _
    rw [← hmap, Subgroup.card_map_of_injective (Original.Y (2 ^ n)).subtype_injective]
    omega
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    exact ⟨hrU, hrY⟩
  · rw [hcard, Nat.card_zpowers, hstr.generator_orders.2.2.2.1]

end Model

section Ambient

theorem centerOf_eq_modelCenter (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    centerOf (S : Subgroup H) = modelCenter S e := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  apply le_antisymm
  · rintro x ⟨hxS, hxC⟩
    obtain ⟨w, rfl⟩ := exists_wreathModelHom_eq S e hxS
    have hw : w ∈ Subgroup.center (Wreath (2 ^ n)) := by
      rw [Subgroup.mem_center_iff]
      intro v
      apply wreathModelHom_injective S e
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hxC _ (wreathModelHom_mem S e v)
    rw [hstr.center] at hw
    exact ⟨w, hw, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨wreathModelHom_mem S e w, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨v, rfl⟩ := exists_wreathModelHom_eq S e hy
    rw [← hstr.center] at hw
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw v]

theorem modelBase_inf_modelY (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    modelBase S e ⊓ modelY S e = Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) := by
  rw [modelBase, modelY, ← Subgroup.map_inf_eq (baseSubgroup (2 ^ n)) (Original.Y (2 ^ n))
    (wreathModelHom S e) (wreathModelHom_injective S e), base_inf_Y_eq hn, MonoidHom.map_zpowers]

theorem not_isConj_swap_of_v_order_two [Finite H] (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hβ : Nat.card (Subgroup.normalizer (modelV S e : Set H) ⧸ modelVInnerCentralizer S e) = 2)
    (x : H) (hx : x ∈ modelBase S e) : ¬ IsConj x (wreathModelHom S e (Original.z (2 ^ n))) := by
  intro hxz
  have hxS : x ∈ (S : Subgroup H) := modelBase_le_sylow S e hx
  have h := modelSwapValue_conjugate_eq_of_v_order_two n hn S e hβ x _ hxS
    (wreathModelHom_mem S e _) hxz
  rw [(modelSwapValue_eq_one_iff S e x hxS).mpr hx] at h
  have hz := (modelSwapValue_eq_one_iff S e _ (wreathModelHom_mem S e _)).mp h.symm
  rw [mem_modelBase_iff, Original.z, element_mem_base] at hz
  exact one_ne_zero hz

end Ambient

section FixedPointFree

theorem exists_eq_commutator_of_fixedPointFree [Finite H] {U : Subgroup H}
    (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {h : H}
    (hhN : h ∈ Subgroup.normalizer (U : Set H)) (hfix : ∀ u ∈ U, h⁻¹ * u * h = u → u = 1)
    (w : H) (hw : w ∈ U) : ∃ u ∈ U, w = u⁻¹ * (h⁻¹ * u * h) := by
  have hconj : ∀ u ∈ U, h⁻¹ * u * h ∈ U := by
    intro u hu
    have h' := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hhN) u).mp hu
    rwa [inv_inv] at h'
  let F : U → U := fun u => ⟨(u : H)⁻¹ * (h⁻¹ * u * h), U.mul_mem (U.inv_mem u.property)
    (hconj u u.property)⟩
  have hinj : Function.Injective F := by
    intro u v huv
    have h1 : (u : H)⁻¹ * (h⁻¹ * u * h) = (v : H)⁻¹ * (h⁻¹ * v * h) := congrArg Subtype.val huv
    have hvu : (v : H) * (u : H)⁻¹ ∈ U := U.mul_mem v.property (U.inv_mem u.property)
    have hfixed : h⁻¹ * ((v : H) * (u : H)⁻¹) * h = (v : H) * (u : H)⁻¹ := by
      have hc := hU _ (U.inv_mem u.property) _ (hconj _ u.property)
      have hc' := hU _ (U.inv_mem v.property) _ (hconj _ v.property)
      calc h⁻¹ * ((v : H) * (u : H)⁻¹) * h = (h⁻¹ * v * h) * (h⁻¹ * u * h)⁻¹ := by group
        _ = (v : H) * ((v : H)⁻¹ * (h⁻¹ * v * h)) * (h⁻¹ * u * h)⁻¹ := by group
        _ = (v : H) * ((u : H)⁻¹ * (h⁻¹ * u * h)) * (h⁻¹ * u * h)⁻¹ := by rw [h1]
        _ = (v : H) * (u : H)⁻¹ := by group
    have h1' := hfix _ hvu hfixed
    apply Subtype.ext
    rw [mul_inv_eq_one] at h1'
    exact h1'.symm
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  exact ⟨u, u.property, (congrArg Subtype.val hu).symm⟩

theorem le_commutator_of_fixedPointFree [Finite H] {U : Subgroup H}
    (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {h : H}
    (hhN : h ∈ Subgroup.normalizer (U : Set H)) (hfix : ∀ u ∈ U, h⁻¹ * u * h = u → u = 1)
    (D : Subgroup H) (hUD : U ≤ D) (hhD : h ∈ D) : U ≤ (commutator D).map D.subtype := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := exists_eq_commutator_of_fixedPointFree hU hhN hfix w hw
  refine ⟨⁅(⟨u⁻¹, D.inv_mem (hUD hu)⟩ : D), (⟨h⁻¹, D.inv_mem hhD⟩ : D)⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
  simp only [Subgroup.coe_subtype, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    inv_inv]
  group

theorem exists_odd_fixedPointFree_modelBase [Finite H] (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nonempty (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H)) ≃* Equiv.Perm (Fin 3))) :
    ∃ h ∈ Subgroup.normalizer (modelBase S e : Set H), Odd (orderOf h) ∧
      ∀ u ∈ modelBase S e, h⁻¹ * u * h = u → u = 1 := by
  set φ := wreathModelHom S e with hφ
  obtain ⟨Y, hYN, h1, h2, h3⟩ := exists_base_three_cycle hn S e hα
  let c : ZMod 3 → H := ![φ (Original.x (2 ^ n)), φ (Original.x2 (2 ^ n)),
    φ (Original.t (2 ^ n) ^ (2 ^ n / 2))]
  have hstep : ∀ i : ZMod 3, Y⁻¹ * c i * Y = c (i + 1) := by
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
  have hpow : ∀ (k : ℕ) (i : ZMod 3), (Y ^ k)⁻¹ * c i * Y ^ k = c (i + k) := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
        intro i
        calc (Y ^ (k + 1))⁻¹ * c i * Y ^ (k + 1) = Y⁻¹ * ((Y ^ k)⁻¹ * c i * Y ^ k) * Y := by
              rw [pow_succ]
              group
          _ = c (i + (k + 1 : ℕ)) := by
              rw [ih, hstep]
              push_cast
              ring_nf
  have hinj : Function.Injective c := by
    have h01 := modelHom_x_ne_x2 S e (by omega)
    have h02 := modelHom_x_ne_t_half S e (by omega)
    have h12 := modelHom_x2_ne_t_half S e (by omega)
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij h01 | exact absurd hij h02 | exact absurd hij h12
      | exact absurd hij.symm h01 | exact absurd hij.symm h02 | exact absurd hij.symm h12
  set v := (orderOf Y).factorization 2 with hv
  have hYpos : orderOf Y ≠ 0 := (orderOf_pos Y).ne'
  have hdvd : 2 ^ v ∣ orderOf Y := Nat.ordProj_dvd _ _
  refine ⟨Y ^ (2 ^ v), (Subgroup.normalizer _).pow_mem hYN _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd]
    have hcop := Nat.coprime_ordCompl Nat.prime_two hYpos
    exact Nat.coprime_two_left.mp hcop
  · intro u hu hfix
    by_contra hu1
    have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
      (S.isPGroup'.to_le ((Subgroup.zpowers_le.mpr hu).trans (modelBase_le_sylow S e)))
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (S.isPGroup'.to_le (modelBase_le_sylow S e))
      ⟨u, hu⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, orderOf_eq_one_iff] at hk
      exact hu1 hk
    set w := u ^ (2 ^ (k - 1)) with hw
    have hwU : w ∈ modelBase S e := (modelBase S e).pow_mem hu _
    have hdvdk : 2 ^ (k - 1) ∣ orderOf u := by
      rw [hk]
      exact pow_dvd_pow 2 (Nat.sub_le k 1)
    have hw2 : orderOf w = 2 := by
      rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvdk, hk,
        Nat.pow_div (Nat.sub_le k 1) two_pos, show k - (k - 1) = 1 by omega, pow_one]
    have hconjpow : ∀ (a b : H) (m : ℕ), (a⁻¹ * b * a) ^ m = a⁻¹ * b ^ m * a := by
      intro a b m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, ih, pow_succ]
          group
    have hwfix : (Y ^ (2 ^ v))⁻¹ * w * Y ^ (2 ^ v) = w := by
      rw [hw, ← hconjpow, hfix]
    obtain ⟨i, hi⟩ : ∃ i : ZMod 3, c i = w := by
      rcases modelBase_involution_cases S e (by omega) hwU hw2 with h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    have h' := hpow (2 ^ v) i
    rw [hi, hwfix, ← hi] at h'
    have h'' := hinj h'
    have h3 : ((2 ^ v : ℕ) : ZMod 3) = 0 :=
      (add_left_cancel ((add_zero i).trans h'')).symm
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3)
    omega

theorem modelBase_le_commutator [Finite H] (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nonempty (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H)) ≃* Equiv.Perm (Fin 3)))
    (K : Subgroup H) [K.Normal] (hK : ∃ k : ℕ, K.index = 2 ^ k) (hUK : modelBase S e ≤ K) :
    modelBase S e ≤ (commutator K).map K.subtype := by
  obtain ⟨h, hhN, hodd, hfix⟩ := exists_odd_fixedPointFree_modelBase hn S e hα
  exact le_commutator_of_fixedPointFree (fun x hx y hy => modelBase_commute S e x y hx hy) hhN
    hfix K hUK (mem_of_odd_of_two_power_index K hK h hodd)

theorem modelBase_le_derived [Finite H] (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nonempty (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H)) ≃* Equiv.Perm (Fin 3))) :
    modelBase S e ≤ commutator H := by
  obtain ⟨h, hhN, -, hfix⟩ := exists_odd_fixedPointFree_modelBase hn S e hα
  intro w hw
  obtain ⟨u, -, rfl⟩ := exists_eq_commutator_of_fixedPointFree
    (fun x hx y hy => modelBase_commute S e x y hx hy) hhN hfix w hw
  have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top u⁻¹) (Subgroup.mem_top h⁻¹)
  rw [commutatorElement_def, inv_inv, inv_inv] at hc
  change u⁻¹ * (h⁻¹ * u * h) ∈ ⁅(⊤ : Subgroup H), ⊤⁆
  simpa only [mul_assoc] using hc

theorem modelY_le_commutator [Finite H] (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hβ : Nonempty (Subgroup.normalizer (modelV S e : Set H) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3)))
    (K : Subgroup H) [K.Normal] (hK : ∃ k : ℕ, K.index = 2 ^ k) (hYK : modelY S e ≤ K) :
    modelY S e ≤ (commutator K).map K.subtype := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  obtain ⟨g, -, hodd, -, -, -, hrel, -, -⟩ :=
    modelVNormalizer_exists_quaternion_commutator_actor n hn S e hβ
  have hgK : (g : H) ∈ K := mem_of_odd_of_two_power_index K hK g (by
    rw [Subgroup.orderOf_coe]
    exact hodd)
  have hQ := hrel K ((modelQ_le_modelY n S e).trans hYK) hgK
  have hd : wreathModelHom S e (Original.d (2 ^ n)) ∈ (commutator K).map K.subtype :=
    hQ ⟨Original.d (2 ^ n), Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
  have hnormal : ((commutator K).map K.subtype).Normal := inferInstance
  have hcomap : (((commutator K).map K.subtype).comap (wreathModelHom S e)).Normal :=
    hnormal.comap _
  have hcl : Subgroup.normalClosure {Original.d (2 ^ n)} ≤
      ((commutator K).map K.subtype).comap (wreathModelHom S e) := by
    apply Subgroup.normalClosure_le_normal
    rintro _ rfl
    exact hd
  rw [hstr.normal_closure] at hcl
  rw [modelY, Subgroup.map_le_iff_le_comap]
  exact hcl

end FixedPointFree

end CFSG.QuasiDihedralFusion
