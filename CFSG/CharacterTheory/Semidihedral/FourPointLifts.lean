module

public import CFSG.CharacterTheory.Semidihedral.FourPointPresentation
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.Semidihedral.FourPointLifts

open Equiv

@[expose] def fourKlein : Subgroup (Perm (Fin 4)) where
  carrier := {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem fourKlein_carrier :
    (fourKlein : Set (Perm (Fin 4))) =
      {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2} := rfl

theorem mem_fourKlein (g : Perm (Fin 4)) :
    g ∈ fourKlein ↔ g = 1 ∨ g = swap 0 1 * swap 2 3 ∨
      g = swap 0 2 * swap 1 3 ∨ g = swap 0 3 * swap 1 2 := by
  change g ∈ ({1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
    swap 0 3 * swap 1 2} : Set (Perm (Fin 4))) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem double_transposition_mem_fourKlein :
    swap (0 : Fin 4) 1 * swap 2 3 ∈ fourKlein := (mem_fourKlein _).2 (Or.inr (Or.inl rfl))

theorem double_transposition_ne_one : swap (0 : Fin 4) 1 * swap 2 3 ≠ 1 := by decide

theorem adjacent_swaps_ab_cube : (swap (0 : Fin 4) 1 * swap 1 2) ^ 3 = 1 := by decide

theorem adjacent_swaps_bc_cube : (swap (1 : Fin 4) 2 * swap 2 3) ^ 3 = 1 := by decide

theorem adjacent_swaps_generate :
    Subgroup.closure ({swap 0 1, swap 1 2, swap 2 3} : Set (Perm (Fin 4))) = ⊤ := by
  have hr : (Set.range fun i : Fin 3 => swap i.castSucc i.succ) =
      ({swap 0 1, swap 1 2, swap 2 3} : Set (Perm (Fin 4))) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [← hr]
  exact Subgroup.closure_eq_top_of_mclosure_eq_top (Perm.mclosure_swap_castSucc_succ 3)

variable {H : Type*} [Group H]

theorem square_eq_one_of_order_two (x : H) (hx : orderOf x = 2) : x ^ 2 = 1 := by
  simpa only [hx] using pow_orderOf_eq_one x

theorem ne_one_of_order_two (x : H) (hx : orderOf x = 2) : x ≠ 1 := by
  intro h
  have h' := orderOf_eq_one_iff.mpr h
  omega

theorem mem_zpowers_order_two_iff (z x : H) (hz : orderOf z = 2) :
    x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
  classical
  have hfin : IsOfFinOrder z := orderOf_pos_iff.mp (by omega)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hz]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, h⟩
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · exact Or.inl (by simpa only [pow_zero] using h.symm)
    · exact Or.inr (by simpa only [pow_one] using h.symm)
  · intro h
    rcases h with h | h
    · exact ⟨0, by decide, (pow_zero z).trans h.symm⟩
    · exact ⟨1, by decide, (pow_one z).trans h.symm⟩

theorem image_z_eq_one (z : H) (pi : H →* Perm (Fin 4))
    (hker : pi.ker = Subgroup.zpowers z) : pi z = 1 := by
  exact MonoidHom.mem_ker.mp (hker.symm ▸ Subgroup.mem_zpowers z)

theorem exists_involution_lift (pi : H →* Perm (Fin 4))
    (hpi : Function.Surjective pi) (u : H) (hu : orderOf u = 2)
    (hswap : (pi u).IsSwap) (i j : Fin 4) (hij : i ≠ j) :
    ∃ x : H, pi x = swap i j ∧ x ^ 2 = 1 := by
  obtain ⟨k, l, hkl, h⟩ := hswap
  have hc : IsConj (pi u) (swap i j) := by
    rw [h]
    exact Perm.isConj_swap hkl hij
  obtain ⟨p, hp⟩ := isConj_iff.mp hc
  obtain ⟨v, hv⟩ := hpi p
  refine ⟨v * u * v⁻¹, ?_, ?_⟩
  · simpa only [map_mul, map_inv, hv] using hp
  · calc
      (v * u * v⁻¹) ^ 2 = v * (u ^ 2) * v⁻¹ := by
        simp only [pow_two, mul_assoc, inv_mul_cancel_left]
      _ = 1 := by rw [square_eq_one_of_order_two u hu]; group

theorem card_eq_48 (z : H) (hz : orderOf z = 2) (pi : H →* Perm (Fin 4))
    (hpi : Function.Surjective pi) (hker : pi.ker = Subgroup.zpowers z) :
    Nat.card H = 48 := by
  have hc := Subgroup.card_ker_mul_card_of_surjective hpi
  have hperm : Nat.card (Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [hker, Nat.card_zpowers, hz, hperm] at hc
  exact hc.symm

theorem quaternion_square_one_iff (q : QuaternionGroup 2) :
    q ^ 2 = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2 := by
  have h : ∀ q : QuaternionGroup 2,
      q ^ 2 = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2 := by decide
  exact h q

theorem quaternion_square_of_ne (q : QuaternionGroup 2)
    (h1 : q ≠ 1) (h2 : q ≠ QuaternionGroup.a 2) : q ^ 2 = QuaternionGroup.a 2 := by
  have h : ∀ q : QuaternionGroup 2,
      q ≠ 1 → q ≠ QuaternionGroup.a 2 → q ^ 2 = QuaternionGroup.a 2 := by decide
  exact h q h1 h2

theorem central_involution_mem_preimage (z : H) (pi : H →* Perm (Fin 4))
    (hker : pi.ker = Subgroup.zpowers z) : z ∈ fourKlein.comap pi := by
  change pi z ∈ fourKlein
  rw [image_z_eq_one z pi hker]
  exact fourKlein.one_mem

theorem disjoint_lifts_square (z : H) (hz : orderOf z = 2)
    (pi : H →* Perm (Fin 4)) (hker : pi.ker = Subgroup.zpowers z)
    (hQ : Nonempty (fourKlein.comap pi ≃* QuaternionGroup 2))
    (a c : H) (ha : pi a = swap 0 1) (hc : pi c = swap 2 3) :
    (a * c) ^ 2 = z := by
  obtain ⟨e⟩ := hQ
  have hzmem := central_involution_mem_preimage z pi hker
  have hacmem : a * c ∈ fourKlein.comap pi := by
    change pi (a * c) ∈ fourKlein
    rw [map_mul, ha, hc]
    exact double_transposition_mem_fourKlein
  let zk : fourKlein.comap pi := ⟨z, hzmem⟩
  let xk : fourKlein.comap pi := ⟨a * c, hacmem⟩
  have hzk_sq : zk ^ 2 = 1 := by
    apply Subtype.ext
    exact square_eq_one_of_order_two z hz
  have hzk_ne : zk ≠ 1 := by
    intro h
    exact ne_one_of_order_two z hz (congrArg Subtype.val h)
  have hez_sq : (e zk) ^ 2 = 1 := by rw [← map_pow, hzk_sq, map_one]
  have hez_ne : e zk ≠ 1 := by
    intro h
    exact hzk_ne (e.injective (h.trans e.map_one.symm))
  have hez : e zk = QuaternionGroup.a 2 :=
    (quaternion_square_one_iff (e zk)).mp hez_sq |>.resolve_left hez_ne
  have hximage : pi (a * c) ≠ 1 := by
    rw [map_mul, ha, hc]
    exact double_transposition_ne_one
  have hex1 : e xk ≠ 1 := by
    intro h
    have hk : xk = 1 := e.injective (h.trans e.map_one.symm)
    have hval : a * c = 1 := congrArg Subtype.val hk
    exact hximage (by rw [hval, map_one])
  have hex2 : e xk ≠ QuaternionGroup.a 2 := by
    intro h
    have hk : xk = zk := e.injective (h.trans hez.symm)
    have hval : a * c = z := congrArg Subtype.val hk
    exact hximage (by rw [hval, image_z_eq_one z pi hker])
  have hs : xk ^ 2 = zk := by
    apply e.injective
    rw [map_pow, quaternion_square_of_ne (e xk) hex1 hex2, hez]
  exact congrArg Subtype.val hs

theorem central_twist_square (z : H) (hz : z ∈ Subgroup.center H)
    (hzsq : z ^ 2 = 1) (x : H) (hx : x ^ 2 = 1) : (z * x) ^ 2 = 1 := by
  have hcomm : Commute z x := (Subgroup.mem_center_iff.mp hz x).symm
  rw [hcomm.mul_pow, hzsq, hx, mul_one]

theorem normalize_left_lift (z : H) (hz : z ∈ Subgroup.center H)
    (hord : orderOf z = 2) (pi : H →* Perm (Fin 4))
    (hker : pi.ker = Subgroup.zpowers z) (x y : H) (hx : x ^ 2 = 1)
    (hxy : (pi x * pi y) ^ 3 = 1) :
    ∃ x' : H, pi x' = pi x ∧ x' ^ 2 = 1 ∧ (x' * y) ^ 3 = 1 := by
  have hcub : (x * y) ^ 3 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker, map_pow, map_mul]
    exact hxy
  have hcases := (mem_zpowers_order_two_iff z ((x * y) ^ 3) hord).mp hcub
  rcases hcases with h | h
  · exact ⟨x, rfl, hx, h⟩
  · refine ⟨z * x, ?_, central_twist_square z hz
      (square_eq_one_of_order_two z hord) x hx, ?_⟩
    · rw [map_mul, image_z_eq_one z pi hker, one_mul]
    · have hcomm : Commute z (x * y) := (Subgroup.mem_center_iff.mp hz (x * y)).symm
      have hz3 : z ^ 3 = z := by
        rw [show 3 = 2 + 1 from rfl, pow_add, square_eq_one_of_order_two z hord, pow_one,
          one_mul]
      rw [mul_assoc, hcomm.mul_pow, hz3, h, ← pow_two, square_eq_one_of_order_two z hord]

theorem normalize_right_lift (z : H) (hz : z ∈ Subgroup.center H)
    (hord : orderOf z = 2) (pi : H →* Perm (Fin 4))
    (hker : pi.ker = Subgroup.zpowers z) (x y : H) (hy : y ^ 2 = 1)
    (hxy : (pi x * pi y) ^ 3 = 1) :
    ∃ y' : H, pi y' = pi y ∧ y' ^ 2 = 1 ∧ (x * y') ^ 3 = 1 := by
  have hcub : (x * y) ^ 3 ∈ Subgroup.zpowers z := by
    rw [← hker, MonoidHom.mem_ker, map_pow, map_mul]
    exact hxy
  have hcases := (mem_zpowers_order_two_iff z ((x * y) ^ 3) hord).mp hcub
  rcases hcases with h | h
  · exact ⟨y, rfl, hy, h⟩
  · refine ⟨z * y, ?_, central_twist_square z hz
      (square_eq_one_of_order_two z hord) y hy, ?_⟩
    · rw [map_mul, image_z_eq_one z pi hker, one_mul]
    · have hcomm : Commute z (x * y) := (Subgroup.mem_center_iff.mp hz (x * y)).symm
      have hz3 : z ^ 3 = z := by
        rw [show 3 = 2 + 1 from rfl, pow_add, square_eq_one_of_order_two z hord, pow_one,
          one_mul]
      calc
        (x * (z * y)) ^ 3 = (z * (x * y)) ^ 3 := by
          rw [← mul_assoc, Subgroup.mem_center_iff.mp hz x, mul_assoc]
        _ = 1 := by
          rw [hcomm.mul_pow, hz3, h, ← pow_two, square_eq_one_of_order_two z hord]

theorem normalized_lifts_generate (z : H) (pi : H →* Perm (Fin 4))
    (hker : pi.ker = Subgroup.zpowers z) (a b c : H)
    (ha : pi a = swap 0 1) (hb : pi b = swap 1 2) (hc : pi c = swap 2 3)
    (hac : (a * c) ^ 2 = z) : Subgroup.closure ({a, b, c} : Set H) = ⊤ := by
  let K := Subgroup.closure ({a, b, c} : Set H)
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hcK : c ∈ K := Subgroup.subset_closure (by simp)
  have hzK : z ∈ K := hac ▸ K.pow_mem (K.mul_mem haK hcK) 2
  have hkerK : pi.ker ≤ K := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr hzK
  have hmap : K.map pi = ⊤ := by
    have himage : pi '' ({a, b, c} : Set H) =
        ({swap 0 1, swap 1 2, swap 2 3} : Set (Perm (Fin 4))) := by
      simp only [Set.image_insert_eq, Set.image_singleton, ha, hb, hc]
    dsimp only [K]
    rw [MonoidHom.map_closure, himage, adjacent_swaps_generate]
  calc
    Subgroup.closure ({a, b, c} : Set H) = (K.map pi).comap pi :=
      (Subgroup.comap_map_eq_self hkerK).symm
    _ = ⊤ := by rw [hmap, Subgroup.comap_top]

theorem closure_four_eq_top (a b c z : H)
    (hgen : Subgroup.closure ({a, b, c} : Set H) = ⊤) :
    Subgroup.closure ({a, b, c, z} : Set H) = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem exists_normalized_generators [Finite H] (z : H)
    (hz : z ∈ Subgroup.center H) (hord : orderOf z = 2)
    (pi : H →* Perm (Fin 4)) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (hQ : Nonempty (fourKlein.comap pi ≃* QuaternionGroup 2))
    (hu : ∃ u : H, orderOf u = 2 ∧ (pi u).IsSwap) :
    Nat.card H = 48 ∧ ∃ a b c : H,
      pi a = swap 0 1 ∧ pi b = swap 1 2 ∧ pi c = swap 2 3 ∧
      a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ c ^ 2 = 1 ∧
      (a * b) ^ 3 = 1 ∧ (b * c) ^ 3 = 1 ∧ (a * c) ^ 2 = z ∧
      Subgroup.closure ({a, b, c} : Set H) = ⊤ := by
  refine ⟨card_eq_48 z hord pi hpi hker, ?_⟩
  obtain ⟨u, huord, huswap⟩ := hu
  obtain ⟨a₀, ha₀, ha₀sq⟩ := exists_involution_lift pi hpi u huord huswap 0 1 (by decide)
  obtain ⟨b, hb, hbsq⟩ := exists_involution_lift pi hpi u huord huswap 1 2 (by decide)
  obtain ⟨c₀, hc₀, hc₀sq⟩ := exists_involution_lift pi hpi u huord huswap 2 3 (by decide)
  have habimage : (pi a₀ * pi b) ^ 3 = 1 := by
    rw [ha₀, hb]
    exact adjacent_swaps_ab_cube
  obtain ⟨a, haimage, hasq, hab⟩ :=
    normalize_left_lift z hz hord pi hker a₀ b ha₀sq habimage
  have ha : pi a = swap 0 1 := haimage.trans ha₀
  have hbcimage : (pi b * pi c₀) ^ 3 = 1 := by
    rw [hb, hc₀]
    exact adjacent_swaps_bc_cube
  obtain ⟨c, hcimage, hcsq, hbc⟩ :=
    normalize_right_lift z hz hord pi hker b c₀ hc₀sq hbcimage
  have hc : pi c = swap 2 3 := hcimage.trans hc₀
  have hac := disjoint_lifts_square z hord pi hker hQ a c ha hc
  exact ⟨a, b, c, ha, hb, hc, hasq, hbsq, hcsq, hab, hbc, hac,
    normalized_lifts_generate z pi hker a b c ha hb hc hac⟩

theorem exists_normalized_relations [Finite H] (z : H)
    (hz : z ∈ Subgroup.center H) (hord : orderOf z = 2)
    (pi : H →* Perm (Fin 4)) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (hQ : Nonempty (fourKlein.comap pi ≃* QuaternionGroup 2))
    (hu : ∃ u : H, orderOf u = 2 ∧ (pi u).IsSwap) :
    Nat.card H = 48 ∧ ∃ a b c : H,
      pi a = swap 0 1 ∧ pi b = swap 1 2 ∧ pi c = swap 2 3 ∧
      FourPointPresentation.Relations a b c z ∧
      Subgroup.closure ({a, b, c} : Set H) = ⊤ ∧
      Subgroup.closure ({a, b, c, z} : Set H) = ⊤ := by
  obtain ⟨hcard, a, b, c, ha, hb, hc, hasq, hbsq, hcsq, hab, hbc, hac, hgen⟩ :=
    exists_normalized_generators z hz hord pi hpi hker hQ hu
  exact ⟨hcard, a, b, c, ha, hb, hc,
    ⟨hz, hasq, hbsq, hcsq, square_eq_one_of_order_two z hord, hab, hbc, hac⟩,
    hgen, closure_four_eq_top a b c z hgen⟩

end CFSG.Semidihedral.FourPointLifts
