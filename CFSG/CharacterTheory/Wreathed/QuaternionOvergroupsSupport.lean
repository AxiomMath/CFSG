module

public import CFSG.CharacterTheory.Wreathed.CyclicDisjointActorSupport
public import CFSG.CharacterTheory.Wreathed.QuaternionCentralQuotient
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.Wreathed.QuaternionOvergroups

open CFSG.Wreathed.Original CFSG.Wreathed.CyclicDisjointActor

@[expose] noncomputable def nu (N : ℕ) :
    Wreath (2 ^ (N + 1)) →* Multiplicative (ZMod (2 ^ (N + 1))) where
  toFun g :=
    let c := coordinateEquiv (2 ^ (N + 1)) g
    Multiplicative.ofAdd
      (c.1 + c.2.1 + if c.2.2 = 0 then 0 else ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1))))
  map_one' := by
    change Multiplicative.ofAdd ((0 : ZMod (2 ^ (N + 1))) + 0 +
      if (0 : ZMod 2) = 0 then 0 else ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1)))) = 1
    simp
  map_mul' g h := by
    obtain ⟨a, b, e, rfl⟩ := exists_element g
    obtain ⟨c, d, f, rfl⟩ := exists_element h
    rcases swap_exponent_cases e with rfl | rfl <;>
      rcases swap_exponent_cases f with rfl | rfl
    · rw [element_base_mul]
      apply Multiplicative.toAdd.injective
      change a + c + (b + d) + 0 = (a + b + 0) + (c + d + 0)
      abel
    · rw [element_base_mul]
      apply Multiplicative.toAdd.injective
      change a + c + (b + d) + _ = (a + b + 0) + (c + d + _)
      abel
    · rw [element_swap_mul, add_zero]
      apply Multiplicative.toAdd.injective
      change a + d + (b + c) + _ = (a + b + _) + (c + d + 0)
      abel
    · rw [element_swap_mul, show (1 + 1 : ZMod 2) = 0 by decide]
      apply Multiplicative.toAdd.injective
      change a + d + (b + c) + 0 = (a + b + ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1)))) +
        (c + d + ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1))))
      linear_combination -(half_add_half N)

theorem nu_element (N : ℕ) (a b : ZMod (2 ^ (N + 1))) (e : ZMod 2) :
    nu N (element (2 ^ (N + 1)) a b e) =
      Multiplicative.ofAdd (a + b + if e = 0 then 0 else ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1)))) :=
  rfl

theorem nu_base (N : ℕ) (a b : ZMod (2 ^ (N + 1))) :
    nu N (element (2 ^ (N + 1)) a b 0) = Multiplicative.ofAdd (a + b) := by
  simp [nu_element]

theorem nu_swap (N : ℕ) (a b : ZMod (2 ^ (N + 1))) :
    nu N (element (2 ^ (N + 1)) a b 1) =
      Multiplicative.ofAdd (a + b + ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1)))) := by
  simp [nu_element]

theorem half_eq (N : ℕ) : 2 ^ (N + 1) / 2 = 2 ^ N := by
  rw [pow_succ, Nat.mul_div_cancel _ two_pos]

theorem d_eq_element (N : ℕ) :
    d (2 ^ (N + 1)) = element (2 ^ (N + 1)) (2 ^ N : ℕ) 0 1 := by
  rw [d_eq, half_eq]

theorem r_mem_ker (N : ℕ) : r (2 ^ (N + 1)) ∈ (nu N).ker := by
  rw [MonoidHom.mem_ker, r_eq, nu_base, add_neg_cancel, ofAdd_zero]

theorem d_mem_ker (N : ℕ) : d (2 ^ (N + 1)) ∈ (nu N).ker := by
  rw [MonoidHom.mem_ker, d_eq_element, nu_swap, add_zero, half_add_half, ofAdd_zero]

theorem nu_surjective (N : ℕ) : Function.Surjective (nu N) := by
  intro c
  refine ⟨element _ (Multiplicative.toAdd c) 0 0, ?_⟩
  rw [nu_base, add_zero, ofAdd_toAdd]

theorem card_ker_nu (N : ℕ) : Nat.card (nu N).ker = 2 * 2 ^ (N + 1) := by
  have h := (nu N).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (nu_surjective N), Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, card_wreath, sq, ← mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem index_ker_nu (N : ℕ) : (nu N).ker.index = 2 ^ (N + 1) := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (nu_surjective N), Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem Y_eq_ker (N : ℕ) (hN : 1 ≤ N) : Y (2 ^ (N + 1)) = (nu N).ker := by
  have hstr := wreath_center_involution_and_quaternion_coordinates (N + 1) (by omega)
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Y, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact r_mem_ker N
    · exact d_mem_ker N
  · rw [card_ker_nu, hstr.quaternion_card]

theorem Y_normal (N : ℕ) (hN : 1 ≤ N) : (Y (2 ^ (N + 1))).Normal := by
  rw [Y_eq_ker N hN]
  infer_instance

theorem Y_index (N : ℕ) (hN : 1 ≤ N) : (Y (2 ^ (N + 1))).index = 2 ^ (N + 1) := by
  rw [Y_eq_ker N hN, index_ker_nu]

theorem quaternion_card (N : ℕ) : Nat.card (QuaternionGroup (2 ^ N)) = 4 * 2 ^ N := by
  have : NeZero (2 ^ N) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem quaternion_nonabelian {H : Type*} [Group H] (N : ℕ) (hN : 1 ≤ N)
    (e : QuaternionGroup (2 ^ N) ≃* H) : ∃ u v : H, u * v ≠ v * u := by
  refine ⟨e (QuaternionGroup.a 1), e (QuaternionGroup.xa 0), fun h => ?_⟩
  have hsource : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ N)) * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
    apply e.injective
    simpa only [map_mul] using h
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, zero_sub, zero_add] at hsource
  have hsum : ((2 : ℕ) : ZMod (2 * 2 ^ N)) = 0 := by
    have hi : -(1 : ZMod (2 * 2 ^ N)) = 1 := QuaternionGroup.xa.inj hsource
    push_cast
    linear_combination -hi
  have hdiv : 2 * 2 ^ N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * 2 ^ N)).mp hsum
  have hle : 2 * 2 ^ N ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hge : 2 ^ 1 ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) hN
  omega

theorem nu_sq_eq_one_of_quaternion (N : ℕ) (hN : 1 ≤ N) (Y₁ : Subgroup (Wreath (2 ^ (N + 1))))
    (e : QuaternionGroup (2 ^ N) ≃* Y₁) (g : Wreath (2 ^ (N + 1))) (hg : g ∈ Y₁) :
    nu N g ^ 2 = 1 := by
  have : NeZero (2 ^ N) := ⟨pow_ne_zero _ two_ne_zero⟩
  let f : QuaternionGroup (2 ^ N) →* Multiplicative (ZMod (2 ^ (N + 1))) :=
    (nu N).comp (Y₁.subtype.comp e.toMonoidHom)
  have hf1 : f (QuaternionGroup.a 1) ^ 2 = 1 := by
    have h1 : f (QuaternionGroup.xa 0) * f (QuaternionGroup.a 1) =
        f (QuaternionGroup.a (-1)) * f (QuaternionGroup.xa 0) := by
      rw [← map_mul, ← map_mul, QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add,
        zero_sub, neg_neg]
    have h2 : f (QuaternionGroup.a 1) * f (QuaternionGroup.a (-1)) = 1 := by
      rw [← map_mul, QuaternionGroup.a_mul_a, add_neg_cancel, QuaternionGroup.a_zero, map_one]
    have h3 : f (QuaternionGroup.a 1) = f (QuaternionGroup.a (-1)) :=
      mul_right_cancel ((mul_comm _ _).trans h1)
    calc f (QuaternionGroup.a 1) ^ 2 = f (QuaternionGroup.a 1) * f (QuaternionGroup.a 1) :=
          sq _
      _ = 1 := by rw [← h3] at h2; exact h2
  have hfsq : ∀ q, f q ^ 2 = 1 := by
    intro q
    cases q with
    | a i =>
      have hi : (QuaternionGroup.a i : QuaternionGroup (2 ^ N)) =
          QuaternionGroup.a 1 ^ i.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      rw [hi, map_pow, ← pow_mul, Nat.mul_comm i.val 2, pow_mul, hf1, one_pow]
    | xa i =>
      rw [← map_pow, QuaternionGroup.xa_sq, ← QuaternionGroup.a_one_pow, map_pow]
      have key : f (QuaternionGroup.a 1) ^ (2 * 2 ^ (N - 1)) = 1 := by
        rw [pow_mul, hf1, one_pow]
      rwa [← pow_succ' 2 (N - 1), show N - 1 + 1 = N by omega] at key
  have h := hfsq (e.symm ⟨g, hg⟩)
  simpa [f] using h

theorem quaternion_unique (N : ℕ) (hN : 1 ≤ N) (Y₁ : Subgroup (Wreath (2 ^ (N + 1))))
    (e : QuaternionGroup (2 ^ N) ≃* Y₁) : Y₁ = Y (2 ^ (N + 1)) := by
  have hstr := wreath_center_involution_and_quaternion_coordinates (N + 1) (by omega)
  have hnonab := quaternion_nonabelian N hN e
  have hinv : ∀ y : Y₁, orderOf y = 2 →
      y = e (QuaternionGroup.a ((2 ^ N : ℕ) : ZMod (2 * 2 ^ N))) := by
    intro y hy
    obtain ⟨q, rfl⟩ := e.surjective y
    rw [MulEquiv.orderOf_eq] at hy
    rw [nativeQuaternion_unique_involution (2 ^ N) (by positivity) q hy]
  have hcentral : ∀ g ∈ Y₁, orderOf g = 2 → g ∈ U (2 ^ (N + 1)) := by
    intro g hg ho
    have hgc : (⟨g, hg⟩ : Y₁) ∈ Subgroup.center Y₁ := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : orderOf (MulAut.conj y ⟨g, hg⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
        exact ho
      have h2 := (hinv _ h1).trans (hinv ⟨g, hg⟩ (by rw [Subgroup.orderOf_mk]; exact ho)).symm
      rw [MulAut.conj_apply] at h2
      calc y * ⟨g, hg⟩ = y * ⟨g, hg⟩ * y⁻¹ * y := by group
        _ = ⟨g, hg⟩ * y := by rw [h2]
    have hmem : g ∈ Y₁ ⊓ Z (2 ^ (N + 1)) := by
      rw [← (hstr.nonabelian_centralizers Y₁ hnonab).2]
      exact ⟨_, hgc, rfl⟩
    have haU : a (2 ^ (N + 1)) ∈ U (2 ^ (N + 1)) := by
      rw [U_eq, a_eq, element_mem_base]
    exact Subgroup.zpowers_le.mpr haU hmem.2
  have hout : ∀ g ∈ Y₁, g ∉ U (2 ^ (N + 1)) → g ∈ (nu N).ker := by
    intro g hg hgU
    obtain ⟨p, q, eg, rfl⟩ := exists_element g
    rw [U_eq, element_mem_base] at hgU
    have heg : eg = 1 := (swap_exponent_cases eg).resolve_left hgU
    subst heg
    have hsq := nu_sq_eq_one_of_quaternion N hN Y₁ e _ hg
    rw [nu_swap] at hsq
    have h2 : 2 • (p + q + ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1)))) = 0 := by
      have h := congrArg Multiplicative.toAdd hsq
      rwa [toAdd_pow, toAdd_ofAdd, toAdd_one] at h
    rcases (two_smul_eq_zero_iff N _).mp h2 with h | h
    · rw [MonoidHom.mem_ker, nu_swap, h, ofAdd_zero]
    · exfalso
      have hpq : p + q = 0 := add_eq_right.mp h
      have ho : orderOf (element (2 ^ (N + 1)) p q 1) = 2 :=
        (element_swap_involution_iff _ p q).mpr hpq
      have hU := hcentral _ hg ho
      rw [U_eq, element_mem_base] at hU
      exact one_ne_zero hU
  have hY₁U : ¬ Y₁ ≤ U (2 ^ (N + 1)) := by
    intro hle
    obtain ⟨u, v, huv⟩ := hnonab
    apply huv
    have h := congrArg Subtype.val
      ((isMulCommutative_iff.mp hstr.base_abelian) ⟨u, hle u.2⟩ ⟨v, hle v.2⟩)
    exact Subtype.ext h
  obtain ⟨u₀, hu₀Y, hu₀U⟩ := Set.not_subset.mp hY₁U
  have hle : Y₁ ≤ (nu N).ker := by
    intro g hg
    by_cases hgU : g ∈ U (2 ^ (N + 1))
    · have hprod : u₀ * g ∉ U (2 ^ (N + 1)) := fun h => hu₀U (by
        have h' := (U (2 ^ (N + 1))).mul_mem h ((U (2 ^ (N + 1))).inv_mem hgU)
        rwa [mul_inv_cancel_right] at h')
      have h1 := hout _ (Y₁.mul_mem hu₀Y hg) hprod
      have h2 := hout _ hu₀Y hu₀U
      have hg' : g = u₀⁻¹ * (u₀ * g) := by group
      rw [hg']
      exact (nu N).ker.mul_mem ((nu N).ker.inv_mem h2) h1
    · exact hout g hg hgU
  rw [Y_eq_ker N hN]
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_ker_nu, ← Nat.card_congr e.toEquiv, quaternion_card, pow_succ]
  apply le_of_eq
  ring

theorem overgroup_relIndex (N : ℕ) (hN : 1 ≤ N) (P : Subgroup (Wreath (2 ^ (N + 1))))
    (hYP : Y (2 ^ (N + 1)) ≤ P) (hP : P < ⊤) :
    ∃! k : ℕ, k < N + 1 ∧ (Y (2 ^ (N + 1))).relIndex P = 2 ^ k := by
  have hmul := Subgroup.relIndex_mul_index hYP
  rw [Y_index N hN] at hmul
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ hmul)
  refine ⟨k, ⟨?_, hkeq⟩, fun k' hk' => Nat.pow_right_injective le_rfl (hk'.2.symm.trans hkeq)⟩
  by_contra hlt
  have hkN : k = N + 1 := by omega
  rw [hkeq, hkN] at hmul
  have h1 : P.index = 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) (hmul.trans (mul_one _).symm)
  exact hP.ne (Subgroup.index_eq_one.mp h1)

theorem overgroup_index (N : ℕ) (hN : 1 ≤ N) (P : Subgroup (Wreath (2 ^ (N + 1))))
    (hYP : Y (2 ^ (N + 1)) ≤ P) (k j : ℕ) (hkj : k + j = N + 1)
    (hk : (Y (2 ^ (N + 1))).relIndex P = 2 ^ k) : P.index = 2 ^ j := by
  have hmul := Subgroup.relIndex_mul_index hYP
  rw [Y_index N hN, hk] at hmul
  have h2 : 2 ^ (N + 1) = 2 ^ k * 2 ^ j := by rw [← pow_add, hkj]
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (hmul.trans h2)

@[expose] noncomputable def nuMod (N j : ℕ) (hj : j ≤ N + 1) :
    Wreath (2 ^ (N + 1)) →* Multiplicative (ZMod (2 ^ j)) :=
  (ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j))).toAddMonoidHom.toMultiplicative.comp (nu N)

theorem nuMod_apply (N j : ℕ) (hj : j ≤ N + 1) (g : Wreath (2 ^ (N + 1))) :
    nuMod N j hj g = Multiplicative.ofAdd
      (ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j)) (Multiplicative.toAdd (nu N g))) :=
  rfl

theorem mem_ker_nuMod_base (N j : ℕ) (hj : j ≤ N + 1) (a b : ZMod (2 ^ (N + 1))) :
    element (2 ^ (N + 1)) a b 0 ∈ (nuMod N j hj).ker ↔
      ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j)) (a + b) = 0 := by
  rw [MonoidHom.mem_ker, nuMod_apply, nu_base, toAdd_ofAdd, ofAdd_eq_one]

theorem mem_ker_nuMod_swap (N j : ℕ) (hj : j ≤ N + 1) (a b : ZMod (2 ^ (N + 1))) :
    element (2 ^ (N + 1)) a b 1 ∈ (nuMod N j hj).ker ↔
      ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j))
        (a + b + ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1)))) = 0 := by
  rw [MonoidHom.mem_ker, nuMod_apply, nu_swap, toAdd_ofAdd, ofAdd_eq_one]

theorem castHom_eq_zero_iff (N j : ℕ) (hj : j ≤ N + 1) (c : ZMod (2 ^ (N + 1))) :
    ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j)) c = 0 ↔ 2 ^ j ∣ c.val := by
  have : NeZero (2 ^ (N + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

theorem castHom_natCast_eq_zero_iff (N j : ℕ) (hj : j ≤ N + 1) (t : ℕ) :
    ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j)) (t : ZMod (2 ^ (N + 1))) = 0 ↔
      2 ^ j ∣ t := by
  rw [map_natCast, ZMod.natCast_eq_zero_iff]

theorem castHom_half_eq_zero (N j : ℕ) (hj : j ≤ N) :
    ZMod.castHom (pow_dvd_pow 2 (by omega : j ≤ N + 1)) (ZMod (2 ^ j))
      ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1))) = 0 :=
  (castHom_natCast_eq_zero_iff N j (by omega) _).mpr (pow_dvd_pow 2 hj)

theorem two_pow_dvd_mul_iff (N k j : ℕ) (hkj : k + j = N + 1) (v : ℕ) :
    2 ^ (N + 1) ∣ 2 ^ k * v ↔ 2 ^ j ∣ v := by
  rw [← hkj, pow_add, Nat.mul_dvd_mul_iff_left (by positivity)]

theorem pow_smul_eq_zero_iff (N k j : ℕ) (hkj : k + j = N + 1) (hj : j ≤ N + 1)
    (c : ZMod (2 ^ (N + 1))) :
    (2 ^ k) • c = 0 ↔ ZMod.castHom (pow_dvd_pow 2 hj) (ZMod (2 ^ j)) c = 0 := by
  have : NeZero (2 ^ (N + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [castHom_eq_zero_iff N j hj, ← two_pow_dvd_mul_iff N k j hkj, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]

theorem nuMod_surjective (N j : ℕ) (hj : j ≤ N + 1) : Function.Surjective (nuMod N j hj) := by
  have : NeZero (2 ^ j) := ⟨pow_ne_zero _ two_ne_zero⟩
  intro y
  refine ⟨element _ ((Multiplicative.toAdd y).val : ZMod (2 ^ (N + 1))) 0 0, ?_⟩
  rw [nuMod_apply, nu_base, toAdd_ofAdd, add_zero, map_natCast, ZMod.natCast_zmod_val,
    ofAdd_toAdd]

theorem index_ker_nuMod (N j : ℕ) (hj : j ≤ N + 1) : (nuMod N j hj).ker.index = 2 ^ j := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (nuMod_surjective N j hj),
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_ker_nuMod (N j : ℕ) (hj : j ≤ N + 1) :
    Nat.card (nuMod N j hj).ker * 2 ^ j = 2 * (2 ^ (N + 1)) ^ 2 := by
  have h := (nuMod N j hj).ker.card_mul_index
  rwa [index_ker_nuMod, card_wreath] at h

theorem overgroup_eq_ker (N : ℕ) (hN : 1 ≤ N) (P : Subgroup (Wreath (2 ^ (N + 1))))
    (hYP : Y (2 ^ (N + 1)) ≤ P) (k j : ℕ) (hkj : k + j = N + 1) (hj : j ≤ N + 1)
    (hk : (Y (2 ^ (N + 1))).relIndex P = 2 ^ k) :
    P = (nuMod N j hj).ker := by
  have hYn := Y_normal N hN
  have hle : P ≤ (nuMod N j hj).ker := by
    intro g hg
    have hpow := Subgroup.pow_relIndex_mem (Y (2 ^ (N + 1))) hg
    rw [hk, Y_eq_ker N hN, MonoidHom.mem_ker, map_pow] at hpow
    have h2 : (2 ^ k) • Multiplicative.toAdd (nu N g) = 0 := by
      have h := congrArg Multiplicative.toAdd hpow
      rwa [toAdd_pow, toAdd_one] at h
    rw [MonoidHom.mem_ker, nuMod_apply, (pow_smul_eq_zero_iff N k j hkj hj _).mp h2,
      ofAdd_zero]
  apply Subgroup.eq_of_le_of_card_ge hle
  have hP := P.card_mul_index
  rw [overgroup_index N hN P hYP k j hkj hk, card_wreath] at hP
  exact le_of_eq (Nat.eq_of_mul_eq_mul_right (by positivity)
    ((card_ker_nuMod N j hj).trans hP.symm))

theorem d_mem_ker_nuMod (N j : ℕ) (hj : j ≤ N + 1) : d (2 ^ (N + 1)) ∈ (nuMod N j hj).ker := by
  rw [d_eq_element, mem_ker_nuMod_swap, add_zero, half_add_half, map_zero]

theorem r_mem_ker_nuMod (N j : ℕ) (hj : j ≤ N + 1) : r (2 ^ (N + 1)) ∈ (nuMod N j hj).ker := by
  rw [r_eq, mem_ker_nuMod_base, add_neg_cancel, map_zero]

theorem U_normal (m : ℕ) : (U m).Normal := by
  rw [U_eq]
  exact baseSubgroup_normal m

theorem U_index (N : ℕ) : (U (2 ^ (N + 1))).index = 2 := by
  rw [U_eq]
  exact base_index_two _ (by positivity)

theorem relIndex_base_eq_two (N : ℕ) (K : Subgroup (Wreath (2 ^ (N + 1))))
    (hK : ¬ K ≤ U (2 ^ (N + 1))) : (U (2 ^ (N + 1))).relIndex K = 2 := by
  have := U_normal (2 ^ (N + 1))
  have h1 := Subgroup.relIndex_dvd_index_of_normal (H := U (2 ^ (N + 1))) (K := K)
  rw [U_index] at h1
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact absurd (Subgroup.relIndex_eq_one.mp h) hK
  · exact h

theorem ker_nuMod_not_le_base (N j : ℕ) (hj : j ≤ N + 1) :
    ¬ (nuMod N j hj).ker ≤ U (2 ^ (N + 1)) := by
  intro h
  have hd := h (d_mem_ker_nuMod N j hj)
  rw [U_eq, d_eq_element, element_mem_base] at hd
  exact one_ne_zero hd

theorem ker_nuMod_inf_base (N j : ℕ) (hj : j ≤ N + 1) :
    (nuMod N j hj).ker ⊓ U (2 ^ (N + 1)) =
      Subgroup.closure {r (2 ^ (N + 1)), s (2 ^ (N + 1)) ^ (2 ^ j)} := by
  have : NeZero (2 ^ (N + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  apply le_antisymm
  · intro g hg
    obtain ⟨hgP, hgU⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨a, b, e, rfl⟩ := exists_element g
    rw [U_eq, element_mem_base] at hgU
    subst hgU
    rw [mem_ker_nuMod_base N j hj, castHom_eq_zero_iff N j hj] at hgP
    obtain ⟨w, hw⟩ := hgP
    have h1 : ((-b).val : ZMod (2 ^ (N + 1))) = -b := ZMod.natCast_zmod_val (-b)
    have h2 : ((2 ^ j * w : ℕ) : ZMod (2 ^ (N + 1))) = a + b := by
      rw [← hw, ZMod.natCast_zmod_val]
    have hsplit : element (2 ^ (N + 1)) a b 0 =
        r (2 ^ (N + 1)) ^ (-b).val * (s (2 ^ (N + 1)) ^ 2 ^ j) ^ w := by
      rw [r_eq, s, ← pow_mul, element_base_pow, element_base_pow, element_base_mul,
        element_eq_iff, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, smul_zero, h1, h2]
      refine ⟨by ring, by ring, rfl⟩
    rw [hsplit]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · rw [SetLike.mem_coe]
      exact Subgroup.mem_inf.mpr ⟨r_mem_ker_nuMod N j hj, by rw [U_eq, r_eq, element_mem_base]⟩
    · rw [SetLike.mem_coe]
      refine Subgroup.mem_inf.mpr ⟨?_, by rw [U_eq, s, element_base_pow, element_mem_base]⟩
      rw [s, element_base_pow, mem_ker_nuMod_base N j hj, smul_zero, add_zero, nsmul_eq_mul,
        mul_one, castHom_natCast_eq_zero_iff N j hj]

theorem card_ker_nuMod_inf_base (N k j : ℕ) (hkj : k + j = N + 1) :
    Nat.card ((nuMod N j (by omega)).ker ⊓ U (2 ^ (N + 1)) : Subgroup (Wreath (2 ^ (N + 1)))) =
      2 ^ (N + 1) * 2 ^ k := by
  have hrel := relIndex_base_eq_two N _ (ker_nuMod_not_le_base N j (by omega))
  have h := Subgroup.relIndex_mul_card (H := U (2 ^ (N + 1))) (K := (nuMod N j (by omega)).ker)
  rw [hrel, inf_comm] at h
  have hK := card_ker_nuMod N j (by omega)
  have h2 : 2 * (2 ^ (N + 1)) ^ 2 = 2 * (2 ^ (N + 1) * 2 ^ k) * 2 ^ j := by
    rw [show (2 ^ (N + 1)) ^ 2 = 2 ^ (N + 1) * (2 ^ k * 2 ^ j) by
      rw [sq, ← pow_add 2 k j, hkj]]
    ring
  have hK' := Nat.eq_of_mul_eq_mul_right (by positivity) (hK.trans h2)
  exact Nat.eq_of_mul_eq_mul_left two_pos (h.trans hK')

@[expose] noncomputable def scaleHom (N k j : ℕ) (hkj : k + j = N + 1) :
    ZMod (2 ^ k) →+ ZMod (2 ^ (N + 1)) :=
  ZMod.lift (2 ^ k) ⟨zmultiplesHom (ZMod (2 ^ (N + 1))) ((2 ^ j : ℕ) : ZMod (2 ^ (N + 1))), by
    rw [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, ← pow_add, hkj,
      ZMod.natCast_self]⟩

theorem scaleHom_natCast (N k j : ℕ) (hkj : k + j = N + 1) (t : ℕ) :
    scaleHom N k j hkj (t : ZMod (2 ^ k)) = ((2 ^ j * t : ℕ) : ZMod (2 ^ (N + 1))) := by
  unfold scaleHom
  conv_lhs => rw [← Int.cast_natCast t, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, Nat.cast_mul]
  ring

theorem scaleHom_injective (N k j : ℕ) (hkj : k + j = N + 1) :
    Function.Injective (scaleHom N k j hkj) := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [injective_iff_map_eq_zero]
  intro d hd
  rw [← ZMod.natCast_zmod_val d, scaleHom_natCast, ZMod.natCast_eq_zero_iff,
    two_pow_dvd_mul_iff N j k (by omega)] at hd
  have h0 : d.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt d)
  rwa [ZMod.val_eq_zero] at h0

@[expose] noncomputable def baseProductHom (N k j : ℕ) (hkj : k + j = N + 1) :
    Multiplicative (ZMod (2 ^ (N + 1))) × Multiplicative (ZMod (2 ^ k)) →*
      Wreath (2 ^ (N + 1)) where
  toFun c := element (2 ^ (N + 1))
    (Multiplicative.toAdd c.1 + scaleHom N k j hkj (Multiplicative.toAdd c.2))
    (-Multiplicative.toAdd c.1) 0
  map_one' := by simp
  map_mul' c c' := by
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, map_add, element_base_mul,
      element_eq_iff]
    exact ⟨by abel, by abel, trivial⟩

theorem baseProductHom_injective (N k j : ℕ) (hkj : k + j = N + 1) :
    Function.Injective (baseProductHom N k j hkj) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨c, d⟩ h
  change element _ (Multiplicative.toAdd c + scaleHom N k j hkj (Multiplicative.toAdd d))
    (-Multiplicative.toAdd c) 0 = 1 at h
  rw [← element_zero, element_eq_iff] at h
  obtain ⟨h1, h2, -⟩ := h
  have hc : Multiplicative.toAdd c = 0 := neg_eq_zero.mp h2
  rw [hc, zero_add] at h1
  have hd := scaleHom_injective N k j hkj (h1.trans (map_zero _).symm)
  rw [← toAdd_one] at hc hd
  exact Prod.ext (Multiplicative.toAdd.injective hc) (Multiplicative.toAdd.injective hd)

theorem baseProductHom_mem (N k j : ℕ) (hkj : k + j = N + 1)
    (c : Multiplicative (ZMod (2 ^ (N + 1))) × Multiplicative (ZMod (2 ^ k))) :
    baseProductHom N k j hkj c ∈ (nuMod N j (by omega)).ker ⊓ U (2 ^ (N + 1)) := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  change element _ (Multiplicative.toAdd c.1 + scaleHom N k j hkj (Multiplicative.toAdd c.2))
    (-Multiplicative.toAdd c.1) 0 ∈ _
  refine Subgroup.mem_inf.mpr ⟨?_, by rw [U_eq, element_mem_base]⟩
  rw [mem_ker_nuMod_base N j (by omega), add_neg_cancel_comm,
    ← ZMod.natCast_zmod_val (Multiplicative.toAdd c.2), scaleHom_natCast,
    castHom_natCast_eq_zero_iff N j (by omega)]
  exact Dvd.intro _ rfl

theorem ker_nuMod_inf_base_equiv (N k j : ℕ) (hkj : k + j = N + 1) :
    Nonempty (((nuMod N j (by omega)).ker ⊓ U (2 ^ (N + 1)) : Subgroup (Wreath (2 ^ (N + 1)))) ≃*
      Multiplicative (ZMod (2 ^ (N + 1))) × Multiplicative (ZMod (2 ^ k))) := by
  let f := (baseProductHom N k j hkj).codRestrict _ (baseProductHom_mem N k j hkj)
  have hinj : Function.Injective f := fun c c' h =>
    baseProductHom_injective N k j hkj (congrArg Subtype.val h)
  have hcard : Nat.card ((nuMod N j (by omega)).ker ⊓ U (2 ^ (N + 1)) :
      Subgroup (Wreath (2 ^ (N + 1)))) ≤
      Nat.card (Multiplicative (ZMod (2 ^ (N + 1))) × Multiplicative (ZMod (2 ^ k))) := by
    rw [card_ker_nuMod_inf_base N k j hkj, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ (N + 1))) ≃ _),
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ k)) ≃ _),
      Nat.card_zmod, Nat.card_zmod]
  exact ⟨(MulEquiv.ofBijective f (hinj.bijective_of_nat_card_le hcard)).symm⟩

theorem a_pow_eq (N t : ℕ) :
    a (2 ^ (N + 1)) ^ t = element (2 ^ (N + 1)) (t : ZMod (2 ^ (N + 1))) t 0 := by
  rw [a_eq, element_base_pow, nsmul_eq_mul, mul_one]

theorem two_pow_dvd_add_self_iff (j : ℕ) (hj : 1 ≤ j) (t : ℕ) :
    2 ^ j ∣ t + t ↔ 2 ^ (j - 1) ∣ t := by
  rw [← two_mul, show 2 ^ j = 2 * 2 ^ (j - 1) by rw [← pow_succ']; congr 1; omega,
    Nat.mul_dvd_mul_iff_left two_pos]

theorem ker_nuMod_inf_center (N j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ N + 1) :
    (nuMod N j hj).ker ⊓ Z (2 ^ (N + 1)) =
      Subgroup.zpowers (a (2 ^ (N + 1)) ^ 2 ^ (j - 1)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgP, hgZ⟩ := Subgroup.mem_inf.mp hg
    change g ∈ Subgroup.zpowers (a _) at hgZ
    obtain ⟨t, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hgZ)
    rw [a_pow_eq, mem_ker_nuMod_base N j hj, ← Nat.cast_add, castHom_natCast_eq_zero_iff N j hj,
      two_pow_dvd_add_self_iff j hj1] at hgP
    obtain ⟨w, rfl⟩ := hgP
    rw [pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
    rw [a_pow_eq, mem_ker_nuMod_base N j hj, ← Nat.cast_add, castHom_natCast_eq_zero_iff N j hj,
      two_pow_dvd_add_self_iff j hj1]

theorem orderOf_center_generator (N k j : ℕ) (hkj : k + j = N + 1) (hj1 : 1 ≤ j) :
    orderOf (a (2 ^ (N + 1)) ^ 2 ^ (j - 1)) = 2 ^ (k + 1) := by
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
    (by rw [orderOf_a]; exact pow_dvd_pow 2 (by omega)), orderOf_a,
    Nat.pow_div (by omega) two_pos]
  congr 1
  omega

theorem commute_swap_iff {m : ℕ} (p q i i' : ZMod m) (e : ZMod 2) :
    element m i i' e * element m p q 1 = element m p q 1 * element m i i' e ↔
      (e = 0 ∧ i = i') ∨ (e = 1 ∧ i - i' = p - q) := by
  rcases swap_exponent_cases e with rfl | rfl
  · rw [element_base_mul, element_swap_mul, add_zero, element_eq_iff]
    constructor
    · rintro ⟨h1, -, -⟩
      exact Or.inl ⟨rfl, by linear_combination h1⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact ⟨by rw [h]; ring, by rw [h]; ring, rfl⟩
      · exact absurd h (by decide)
  · rw [element_swap_mul, element_swap_mul, element_eq_iff]
    constructor
    · rintro ⟨h1, -, -⟩
      exact Or.inr ⟨rfl, by linear_combination h1⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h (by decide)
      · exact ⟨by linear_combination h, by linear_combination -h, rfl⟩

theorem centralizer_swap_comm {m : ℕ} (hm : 1 < m) (p q : ZMod m) {g₁ g₂ : Wreath m}
    (h₁ : g₁ ∈ Subgroup.centralizer {element m p q 1})
    (h₂ : g₂ ∈ Subgroup.centralizer {element m p q 1}) : g₁ * g₂ = g₂ * g₁ := by
  obtain ⟨i, i', e, rfl⟩ := exists_element g₁
  obtain ⟨l, l', f, rfl⟩ := exists_element g₂
  rw [Subgroup.mem_centralizer_singleton_iff, commute_swap_iff] at h₁ h₂
  rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, h₁⟩
  · exact (Subgroup.mem_center_iff.mp
      ((element_mem_center_iff m hm _ _ _).mpr ⟨rfl, rfl⟩) _).symm
  · rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, h₂⟩
    · exact Subgroup.mem_center_iff.mp ((element_mem_center_iff m hm _ _ _).mpr ⟨rfl, rfl⟩) _
    · rw [element_swap_mul, element_swap_mul, element_eq_iff]
      exact ⟨by linear_combination h₁ - h₂, by linear_combination h₂ - h₁, rfl⟩

theorem centralizer_inf_base (N j : ℕ) (hj : j ≤ N + 1) (p q : ZMod (2 ^ (N + 1))) :
    U (2 ^ (N + 1)) ⊓
        ((nuMod N j hj).ker ⊓ Subgroup.centralizer {element (2 ^ (N + 1)) p q 1}) =
      (nuMod N j hj).ker ⊓ Z (2 ^ (N + 1)) := by
  have hm := one_lt_modulus N
  ext g
  obtain ⟨i, i', e, rfl⟩ := exists_element g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, commute_swap_iff, U_eq,
    element_mem_base, Z_eq _ hm, element_mem_center_iff _ hm]
  constructor
  · rintro ⟨he, hK, (⟨-, h⟩ | ⟨h1, -⟩)⟩
    · exact ⟨hK, he, h⟩
    · exact absurd (he.symm.trans h1) (by decide)
  · rintro ⟨hK, he, h⟩
    exact ⟨he, hK, Or.inl ⟨he, h⟩⟩

theorem card_centralizer_swap (N k j : ℕ) (hkj : k + j = N + 1) (hj1 : 1 ≤ j)
    (p q : ZMod (2 ^ (N + 1))) (hu : element (2 ^ (N + 1)) p q 1 ∈ (nuMod N j (by omega)).ker) :
    Nat.card ((nuMod N j (by omega)).ker ⊓
        Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} : Subgroup (Wreath (2 ^ (N + 1)))) =
      2 * 2 ^ (k + 1) := by
  have hnot : ¬ ((nuMod N j (by omega)).ker ⊓
      Subgroup.centralizer {element (2 ^ (N + 1)) p q 1}) ≤ U (2 ^ (N + 1)) := by
    intro h
    have hU := h (Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    rw [U_eq, element_mem_base] at hU
    exact one_ne_zero hU
  have hrel := relIndex_base_eq_two N _ hnot
  have h := Subgroup.relIndex_mul_card (H := U (2 ^ (N + 1)))
    (K := (nuMod N j (by omega)).ker ⊓ Subgroup.centralizer {element (2 ^ (N + 1)) p q 1})
  rw [hrel, centralizer_inf_base, ker_nuMod_inf_center N j hj1, Nat.card_zpowers,
    orderOf_center_generator N k j hkj hj1] at h
  exact h.symm

theorem centralizer_swap_cyclic (N : ℕ) (p q : ZMod (2 ^ (N + 1)))
    (hu : element (2 ^ (N + 1)) p q 1 ∈ (nuMod N (N + 1) le_rfl).ker) :
    IsCyclic ((nuMod N (N + 1) le_rfl).ker ⊓
        Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} : Subgroup (Wreath (2 ^ (N + 1)))) ∧
      Nat.card ((nuMod N (N + 1) le_rfl).ker ⊓
        Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} : Subgroup (Wreath (2 ^ (N + 1)))) =
        4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero (2 ^ (N + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hcard := card_centralizer_swap N 0 (N + 1) (by omega) (by omega) p q hu
  rw [show 2 * 2 ^ (0 + 1) = 4 by norm_num] at hcard
  refine ⟨?_, hcard⟩
  have hsum : p + q + ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1))) = 0 := by
    rw [mem_ker_nuMod_swap N (N + 1) le_rfl, castHom_eq_zero_iff N (N + 1) le_rfl] at hu
    have h0 := Nat.eq_zero_of_dvd_of_lt hu (ZMod.val_lt _)
    rwa [ZMod.val_eq_zero] at h0
  have hpq : p + q = ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1))) := by
    linear_combination hsum - half_add_half N
  have hsq : element (2 ^ (N + 1)) p q 1 ^ 2 = element (2 ^ (N + 1)) (2 ^ N : ℕ) (2 ^ N : ℕ) 0 := by
    rw [element_swap_sq, hpq]
  have hord : orderOf (element (2 ^ (N + 1)) p q 1) = 2 ^ 2 := by
    apply orderOf_eq_prime_pow
    · rw [pow_one, hsq, ← element_zero, element_eq_iff]
      exact fun h => half_residue_ne_zero N h.1
    · rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, hsq, element_base_pow, ← element_zero,
        element_eq_iff, two_smul, half_add_half]
      exact ⟨rfl, rfl, rfl⟩
  have huC : element (2 ^ (N + 1)) p q 1 ∈ (nuMod N (N + 1) le_rfl).ker ⊓
      Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} :=
    Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  exact isCyclic_of_orderOf_eq_card (⟨_, huC⟩ : ((nuMod N (N + 1) le_rfl).ker ⊓
      Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} : Subgroup (Wreath (2 ^ (N + 1)))))
    (by rw [Subgroup.orderOf_mk, hord, hcard]; norm_num)

theorem centralizer_swap_equiv (N k j : ℕ) (hkj : k + j = N + 1) (hj1 : 1 ≤ j) (hk : 1 ≤ k)
    (p q : ZMod (2 ^ (N + 1))) (hu : element (2 ^ (N + 1)) p q 1 ∈ (nuMod N j (by omega)).ker) :
    Nonempty (((nuMod N j (by omega)).ker ⊓
        Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} : Subgroup (Wreath (2 ^ (N + 1)))) ≃*
      Multiplicative (ZMod (2 ^ (k + 1))) × Multiplicative (ZMod 2)) := by
  have hm := one_lt_modulus N
  have hjN : j ≤ N := by omega
  have : NeZero (2 ^ (N + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : NeZero (2 ^ (k + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hpq : 2 ∣ (p + q).val := by
    rw [mem_ker_nuMod_swap N j (by omega), map_add, castHom_half_eq_zero N j hjN, add_zero,
      castHom_eq_zero_iff N j (by omega)] at hu
    exact (pow_dvd_pow 2 hj1).trans hu
  obtain ⟨h, hh⟩ := hpq
  have hpq' : p + q = (h : ZMod (2 ^ (N + 1))) + h := by
    rw [← ZMod.natCast_zmod_val (p + q), hh, two_mul, Nat.cast_add]
  have hβ : (p - h) - (h - p) = p - q := by linear_combination hpq'
  let ι : Multiplicative (ZMod (2 ^ (k + 1))) →* Multiplicative (ZMod (2 ^ (N + 1))) :=
    AddMonoidHom.toMultiplicative (scaleHom N (k + 1) (j - 1) (by omega))
  let φ := (diagonalInvolutionProductHom (2 ^ (N + 1)) (p - h)).comp
    (MonoidHom.prodMap ι (MonoidHom.id (Multiplicative (ZMod 2))))
  have hdiag : ∀ t : Multiplicative (ZMod (2 ^ (k + 1))),
      ZMod.castHom (pow_dvd_pow 2 (by omega : j ≤ N + 1)) (ZMod (2 ^ j))
        (scaleHom N (k + 1) (j - 1) (by omega) (Multiplicative.toAdd t) +
          scaleHom N (k + 1) (j - 1) (by omega) (Multiplicative.toAdd t)) = 0 := by
    intro t
    rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd t), scaleHom_natCast, ← Nat.cast_add,
      castHom_natCast_eq_zero_iff N j (by omega), two_pow_dvd_add_self_iff j hj1]
    exact Dvd.intro _ rfl
  have hmem : ∀ c, φ c ∈ (nuMod N j (by omega)).ker ⊓
      Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} := by
    rintro ⟨t, ε⟩
    rcases swap_coordinate_cases ε with rfl | rfl
    · change element _ (scaleHom N (k + 1) (j - 1) (by omega) (Multiplicative.toAdd t))
        (scaleHom N (k + 1) (j - 1) (by omega) (Multiplicative.toAdd t)) 0 ∈ _
      refine Subgroup.mem_inf.mpr ⟨(mem_ker_nuMod_base N j _ _ _).mpr (hdiag t), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, commute_swap_iff]
      exact Or.inl ⟨rfl, rfl⟩
    · change element _ (scaleHom N (k + 1) (j - 1) (by omega) (Multiplicative.toAdd t) +
          (p - (h : ZMod (2 ^ (N + 1)))))
        (scaleHom N (k + 1) (j - 1) (by omega) (Multiplicative.toAdd t) -
          (p - (h : ZMod (2 ^ (N + 1))))) 1 ∈ _
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_ker_nuMod_swap N j (by omega), map_add, castHom_half_eq_zero N j hjN, add_zero,
          ← hdiag t]
        congr 1
        ring
      · rw [Subgroup.mem_centralizer_singleton_iff, commute_swap_iff]
        exact Or.inr ⟨rfl, by linear_combination hβ⟩
  have hι : Function.Injective ι := fun x y hxy =>
    Multiplicative.toAdd.injective (scaleHom_injective N (k + 1) (j - 1) (by omega)
      (Multiplicative.ofAdd.injective hxy))
  have hinj : Function.Injective φ := by
    refine (diagonalInvolutionProductHom_injective _ _).comp ?_
    rw [MonoidHom.coe_prodMap]
    exact hι.prodMap Function.injective_id
  let f := φ.codRestrict _ hmem
  have hfinj : Function.Injective f := fun c c' hcc => hinj (congrArg Subtype.val hcc)
  have hcard : Nat.card ((nuMod N j (by omega)).ker ⊓
      Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} : Subgroup (Wreath (2 ^ (N + 1)))) ≤
      Nat.card (Multiplicative (ZMod (2 ^ (k + 1))) × Multiplicative (ZMod 2)) := by
    rw [card_centralizer_swap N k j hkj hj1 p q hu, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ (k + 1))) ≃ _),
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ _),
      Nat.card_zmod, Nat.card_zmod, mul_comm]
  exact ⟨(MulEquiv.ofBijective f (hfinj.bijective_of_nat_card_le hcard)).symm⟩

@[expose] noncomputable def reduction (h l : ℕ) (hh : h ≠ 0) (hl : l ≠ 0)
    (x : Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) : ZMod 2 × ZMod 2 :=
  (ZMod.castHom (dvd_pow_self 2 hh) (ZMod 2) (Multiplicative.toAdd x.1),
    ZMod.castHom (dvd_pow_self 2 hl) (ZMod 2) (Multiplicative.toAdd x.2))

section Reduction

variable (h l : ℕ) (hh : h ≠ 0) (hl : l ≠ 0)

theorem reduction_mul (x y : Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) :
    reduction h l hh hl (x * y) = reduction h l hh hl x + reduction h l hh hl y := by
  simp only [reduction, Prod.fst_mul, Prod.snd_mul, toAdd_mul, map_add, Prod.mk_add_mk]

theorem reduction_one : reduction h l hh hl 1 = 0 := by
  simp [reduction]

theorem reduction_pow (x : Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l)))
    (t : ℕ) : reduction h l hh hl (x ^ t) = (t : ZMod 2) • reduction h l hh hl x := by
  induction t with
  | zero => rw [pow_zero, reduction_one, Nat.cast_zero, zero_smul]
  | succ t ih => rw [pow_succ, reduction_mul, ih, Nat.cast_succ, add_smul, one_smul]

theorem reduction_inv (x : Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) :
    reduction h l hh hl x⁻¹ = -reduction h l hh hl x := by
  have h1 := reduction_mul h l hh hl x⁻¹ x
  rw [inv_mul_cancel, reduction_one] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

theorem decompose (x : Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) :
    x = (Multiplicative.ofAdd 1, 1) ^ (Multiplicative.toAdd x.1).val *
      (1, Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd x.2).val := by
  have : NeZero (2 ^ h) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : NeZero (2 ^ l) := ⟨pow_ne_zero _ two_ne_zero⟩
  ext
  · rw [Prod.fst_mul, Prod.pow_fst, Prod.pow_fst, one_pow, mul_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  · rw [Prod.snd_mul, Prod.pow_snd, Prod.pow_snd, one_pow, one_mul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem reduction_apply
    (σ : MulAut (Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))))
    (x : Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) :
    reduction h l hh hl (σ x) =
      (reduction h l hh hl x).1 • reduction h l hh hl (σ (Multiplicative.ofAdd 1, 1)) +
        (reduction h l hh hl x).2 • reduction h l hh hl (σ (1, Multiplicative.ofAdd 1)) := by
  have : NeZero (2 ^ h) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : NeZero (2 ^ l) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h1 : (((Multiplicative.toAdd x.1).val : ℕ) : ZMod 2) = (reduction h l hh hl x).1 := by
    simp only [reduction, ZMod.castHom_apply, ZMod.cast_eq_val]
  have h2 : (((Multiplicative.toAdd x.2).val : ℕ) : ZMod 2) = (reduction h l hh hl x).2 := by
    simp only [reduction, ZMod.castHom_apply, ZMod.cast_eq_val]
  conv_lhs => rw [decompose h l x]
  rw [map_mul, map_pow, map_pow, reduction_mul, reduction_pow, reduction_pow, h1, h2]

theorem exists_sq_of_reduction_eq_zero
    (x : Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l)))
    (hx : reduction h l hh hl x = 0) : ∃ y, x = y ^ 2 := by
  have : NeZero (2 ^ h) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : NeZero (2 ^ l) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h1 : 2 ∣ (Multiplicative.toAdd x.1).val := by
    have h := congrArg Prod.fst hx
    simp only [reduction, Prod.fst_zero, ZMod.castHom_apply, ZMod.cast_eq_val] at h
    rwa [ZMod.natCast_eq_zero_iff] at h
  have h2 : 2 ∣ (Multiplicative.toAdd x.2).val := by
    have h := congrArg Prod.snd hx
    simp only [reduction, Prod.snd_zero, ZMod.castHom_apply, ZMod.cast_eq_val] at h
    rwa [ZMod.natCast_eq_zero_iff] at h
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨(Multiplicative.ofAdd (a : ZMod (2 ^ h)), Multiplicative.ofAdd (b : ZMod (2 ^ l))), ?_⟩
  ext
  · rw [Prod.pow_fst]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, ← ZMod.natCast_zmod_val (Multiplicative.toAdd x.1), ha,
      nsmul_eq_mul, Nat.cast_mul]
  · rw [Prod.pow_snd]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, ← ZMod.natCast_zmod_val (Multiplicative.toAdd x.2), hb,
      nsmul_eq_mul, Nat.cast_mul]

end Reduction

theorem reduction_key : ∀ U W : ZMod 2 × ZMod 2, W.1 = 0 →
    ∀ a b c d : ZMod 2, a • U + b • W = (1, 0) → c • U + d • W = (0, 1) →
      ∀ v : ZMod 2 × ZMod 2, (v.1 • U + v.2 • W).1 • U + (v.1 • U + v.2 • W).2 • W = v := by
  decide

theorem mulAut_prod_isPGroup (h l : ℕ) (hl : l ≠ 0) (hlh : l < h) :
    IsPGroup 2 (MulAut (Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh : h ≠ 0 := by omega
  have : NeZero (2 ^ h) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : NeZero (2 ^ l) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hM : IsPGroup 2 (Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) := by
    refine IsPGroup.of_card (n := h + l) ?_
    rw [Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ h)) ≃ _),
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ l)) ≃ _),
      Nat.card_zmod, Nat.card_zmod, pow_add]
  obtain ⟨hquot, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hM
  have hsq : ∀ y : Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l)),
      y ^ 2 ∈ frattini (Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) := by
    intro y
    have h1 := CFSG.OrderReductions.FrattiniElementary.frattini_quotient_exponent 2 hM
      (QuotientGroup.mk' (frattini (Multiplicative (ZMod (2 ^ h)) ×
        Multiplicative (ZMod (2 ^ l)))) y)
    rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  intro σ
  have hW1 : (reduction h l hh hl (σ (1, Multiplicative.ofAdd 1))).1 = 0 := by
    have he₂ : ((1, Multiplicative.ofAdd 1) :
        Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) ^ 2 ^ l = 1 := by
      ext
      · rw [Prod.pow_fst, one_pow, Prod.fst_one]
      · rw [Prod.pow_snd, Prod.snd_one]
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, toAdd_one, ZMod.natCast_self]
    have hσ : (σ (1, Multiplicative.ofAdd 1)) ^ 2 ^ l = 1 := by rw [← map_pow, he₂, map_one]
    have h1 : 2 ^ h ∣ 2 ^ l * (Multiplicative.toAdd (σ (1, Multiplicative.ofAdd 1)).1).val := by
      have h := congrArg (fun z => Multiplicative.toAdd z.1) hσ
      simp only [Prod.pow_fst, toAdd_pow, Prod.fst_one, toAdd_one] at h
      rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd (σ (1, Multiplicative.ofAdd 1)).1),
        nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
      exact h
    have h2 : 2 ^ l * 2 ∣ 2 ^ l * (Multiplicative.toAdd (σ (1, Multiplicative.ofAdd 1)).1).val :=
      (show 2 ^ l * 2 ∣ 2 ^ h by rw [← pow_succ]; exact pow_dvd_pow 2 hlh).trans h1
    rw [Nat.mul_dvd_mul_iff_left (by positivity)] at h2
    rw [reduction, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
    exact h2
  obtain ⟨y₁, hy₁⟩ := σ.surjective (Multiplicative.ofAdd 1, 1)
  obtain ⟨y₂, hy₂⟩ := σ.surjective (1, Multiplicative.ofAdd 1)
  have he₁ : reduction h l hh hl (Multiplicative.ofAdd 1, 1) = (1, 0) := by
    simp only [reduction, toAdd_ofAdd, toAdd_one, map_one, map_zero]
  have he₂ : reduction h l hh hl (1, Multiplicative.ofAdd 1) = (0, 1) := by
    simp only [reduction, toAdd_ofAdd, toAdd_one, map_one, map_zero]
  have hc₁ := reduction_apply h l hh hl σ y₁
  have hc₂ := reduction_apply h l hh hl σ y₂
  rw [hy₁, he₁] at hc₁
  rw [hy₂, he₂] at hc₂
  have hfix : ∀ x, x⁻¹ * σ (σ x) ∈
      frattini (Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))) := by
    intro x
    have hred : reduction h l hh hl (σ (σ x)) = reduction h l hh hl x := by
      rw [reduction_apply h l hh hl σ (σ x), reduction_apply h l hh hl σ x]
      exact reduction_key _ _ hW1 _ _ _ _ hc₁.symm hc₂.symm _
    obtain ⟨y, hy⟩ := exists_sq_of_reduction_eq_zero h l hh hl (x⁻¹ * σ (σ x)) (by
      rw [reduction_mul, reduction_inv, hred]
      exact neg_add_cancel _)
    rw [hy]
    exact hsq y
  have hσ2 : σ ^ 2 ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini (Multiplicative (ZMod (2 ^ h)) × Multiplicative (ZMod (2 ^ l))))).ker := by
    rw [MonoidHom.mem_ker]
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hquot, MulAut.one_apply, pow_two, MulAut.mul_apply, QuotientGroup.eq]
    have h1 := Subgroup.inv_mem _ (hfix x)
    rwa [mul_inv_rev, inv_inv] at h1
  obtain ⟨t, ht⟩ := hker ⟨σ ^ 2, hσ2⟩
  refine ⟨t + 1, ?_⟩
  have h1 := congrArg Subtype.val ht
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul, ← pow_succ'] at h1
  exact h1

theorem abelian_centric_isPGroup (N : ℕ) (hN : 1 ≤ N) (k j : ℕ) (hkj : k + j = N + 1)
    (hj1 : 1 ≤ j) (A : Subgroup (Wreath (2 ^ (N + 1))))
    (hAP : A ≤ (nuMod N j (by omega)).ker) (habel : IsMulCommutative A)
    (hcent : (nuMod N j (by omega)).ker ⊓
      Subgroup.centralizer (A : Set (Wreath (2 ^ (N + 1)))) = A) :
    IsPGroup 2 (MulAut A) := by
  have hm := one_lt_modulus N
  have hstr := wreath_center_involution_and_quaternion_coordinates (N + 1) (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := (CyclicDisjointActor.wreath_isPGroup N).to_subgroup A
  by_cases hAU : A ≤ U (2 ^ (N + 1))
  ·
    have hle : (nuMod N j (by omega)).ker ⊓ U (2 ^ (N + 1)) ≤ A := by
      intro g hg
      obtain ⟨hgK, hgU⟩ := Subgroup.mem_inf.mp hg
      rw [← hcent]
      refine Subgroup.mem_inf.mpr ⟨hgK, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg Subtype.val
        ((isMulCommutative_iff.mp hstr.base_abelian) ⟨y, hAU hy⟩ ⟨g, hgU⟩)
      exact h
    have hA : A = (nuMod N j (by omega)).ker ⊓ U (2 ^ (N + 1)) :=
      le_antisymm (le_inf hAP hAU) hle
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hr : r (2 ^ (N + 1)) ∈ A := by
        rw [hA]
        exact Subgroup.mem_inf.mpr ⟨r_mem_ker_nuMod N j _, by rw [U_eq, r_eq, element_mem_base]⟩
      have hcard := card_ker_nuMod_inf_base N k j hkj
      rw [show 2 ^ k = 1 by rw [hk0, pow_zero], mul_one, ← hA] at hcard
      have : IsCyclic A := isCyclic_of_orderOf_eq_card (⟨_, hr⟩ : A)
        (by rw [Subgroup.orderOf_mk, orderOf_r, hcard])
      exact CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup A hA2
    · obtain ⟨e⟩ := ker_nuMod_inf_base_equiv N k j hkj
      exact (mulAut_prod_isPGroup (N + 1) k (by omega) (by omega)).of_equiv
        (MulAut.congr ((MulEquiv.subgroupCongr hA).trans e)).symm
  ·
    obtain ⟨u, huA, huU⟩ := Set.not_subset.mp hAU
    obtain ⟨p, q, eu, rfl⟩ := exists_element u
    rw [SetLike.mem_coe, U_eq, element_mem_base] at huU
    have heu : eu = 1 := (swap_exponent_cases eu).resolve_left huU
    subst heu
    have huK := hAP huA
    have hA : A = (nuMod N j (by omega)).ker ⊓
        Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} := by
      apply le_antisymm
      · intro g hg
        refine Subgroup.mem_inf.mpr ⟨hAP hg, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg Subtype.val ((isMulCommutative_iff.mp habel) ⟨g, hg⟩ ⟨_, huA⟩)
        exact h
      · intro g hg
        obtain ⟨hgK, hgC⟩ := Subgroup.mem_inf.mp hg
        rw [← hcent]
        refine Subgroup.mem_inf.mpr ⟨hgK, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyC : y ∈ Subgroup.centralizer {element (2 ^ (N + 1)) p q 1} := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h := congrArg Subtype.val ((isMulCommutative_iff.mp habel) ⟨y, hy⟩ ⟨_, huA⟩)
          exact h
        exact centralizer_swap_comm hm p q hyC hgC
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · obtain rfl : j = N + 1 := by omega
      obtain ⟨hcyc, -⟩ := centralizer_swap_cyclic N p q huK
      have : IsCyclic A := (MulEquiv.subgroupCongr hA).isCyclic.mpr hcyc
      exact CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup A hA2
    · obtain ⟨e⟩ := centralizer_swap_equiv N k j hkj hj1 hk0 p q huK
      exact cyclicTimesTwoAut_isPGroup_of_equiv (k + 1) (by omega)
        ((MulEquiv.subgroupCongr hA).trans e)

theorem nonabelian_centric (N : ℕ) (hN : 1 ≤ N) (P : Subgroup (Wreath (2 ^ (N + 1))))
    (hYP : Y (2 ^ (N + 1)) ≤ P) (A : Subgroup (Wreath (2 ^ (N + 1)))) (_hAP : A ≤ P)
    (hA : ∃ u v : A, u * v ≠ v * u)
    (hcent : P ⊓ Subgroup.centralizer (A : Set (Wreath (2 ^ (N + 1)))) =
      (Subgroup.center A).map A.subtype) :
    (Subgroup.center A).map A.subtype = (Subgroup.center P).map P.subtype ∧
      IsCyclic (Subgroup.center A) ∧ x (2 ^ (N + 1)) ∈ (Subgroup.center A).map A.subtype ∧
      (∀ g ∈ (Subgroup.center A).map A.subtype, orderOf g = 2 → g = x (2 ^ (N + 1))) ∧
      ∃ hx : x (2 ^ (N + 1)) ∈ A, ∀ φ : MulAut A,
        φ ⟨x (2 ^ (N + 1)), hx⟩ = ⟨x (2 ^ (N + 1)), hx⟩ := by
  have hstr := wreath_center_involution_and_quaternion_coordinates (N + 1) (by omega)
  have hPnonab : ∃ u v : P, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := originalY_is_nonabelian (N + 1) (by omega)
    refine ⟨⟨u, hYP u.2⟩, ⟨v, hYP v.2⟩, fun h => huv ?_⟩
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  obtain ⟨hcA, -⟩ := hstr.nonabelian_centralizers A hA
  obtain ⟨-, hZP⟩ := hstr.nonabelian_centralizers P hPnonab
  have hZA : (Subgroup.center A).map A.subtype = P ⊓ Z (2 ^ (N + 1)) := by
    rw [← hcent, hcA]
  have hle : (Subgroup.center A).map A.subtype ≤ Subgroup.center (Wreath (2 ^ (N + 1))) := by
    rw [hZA, hstr.center]
    exact inf_le_right
  have hxZ : x (2 ^ (N + 1)) ∈ (Subgroup.center A).map A.subtype := by
    rw [hZA]
    exact Subgroup.mem_inf.mpr ⟨hYP (original_x_mem_Y (N + 1) (by omega)),
      Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
  have hinv : ∀ g ∈ (Subgroup.center A).map A.subtype, orderOf g = 2 → g = x (2 ^ (N + 1)) := by
    intro g hg ho
    rw [unique_central_involution N g ho (hle hg), x_eq_element]
  have hcyc : IsCyclic (Subgroup.center A) := by
    have hZle : (Subgroup.center A).map A.subtype ≤ Subgroup.zpowers (a (2 ^ (N + 1))) := by
      rw [hZA]
      exact inf_le_right
    have hcycZ : IsCyclic ((Subgroup.center A).map A.subtype) :=
      (Subgroup.subgroupOfEquivOfLe hZle).isCyclic.mp inferInstance
    exact (Subgroup.equivMapOfInjective (Subgroup.center A) A.subtype
      A.subtype_injective).isCyclic.mpr hcycZ
  refine ⟨hZA.trans hZP.symm, hcyc, hxZ, hinv, ?_⟩
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxZ
  have hcx' : (c : Wreath (2 ^ (N + 1))) = x (2 ^ (N + 1)) := hcx
  have hxA : x (2 ^ (N + 1)) ∈ A := hcx' ▸ c.2
  refine ⟨hxA, fun φ => ?_⟩
  have hc' : c = ⟨x (2 ^ (N + 1)), hxA⟩ := Subtype.ext hcx'
  have hφc : φ c ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hc y']
  have hord : orderOf ((φ c : A) : Wreath (2 ^ (N + 1))) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hcx']
    exact hstr.involution_orders.1
  have h := hinv _ ⟨φ c, hφc, rfl⟩ hord
  rw [← hc']
  exact Subtype.ext (h.trans hcx'.symm)

end CFSG.Wreathed.QuaternionOvergroups
