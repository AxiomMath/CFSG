module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionExistence
public import CFSG.CharacterTheory.Wreathed.BrauerWongBaseFusion

public noncomputable section

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong

universe u v

theorem mem_closure_cases {M : Type v} [Group M] {α β : M} (hα : α * α = 1)
    (hβ : β * (β * β) = 1) (hβα : β * α = α * (β * β)) {φ : M}
    (hφ : φ ∈ Subgroup.closure {α, β}) :
    φ = 1 ∨ φ = β ∨ φ = β * β ∨ φ = α ∨ φ = α * β ∨ φ = α * (β * β) := by
  have hα' : ∀ x : M, α * (α * x) = x := fun x => by rw [← mul_assoc, hα, one_mul]
  have hβα' : ∀ x : M, β * (α * x) = α * (β * (β * x)) := fun x => by
    rw [← mul_assoc, hβα, mul_assoc, mul_assoc]
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have hβinv : β⁻¹ = β * β := inv_eq_of_mul_eq_one_right hβ
  have hstep : ∀ x : M, (x = 1 ∨ x = β ∨ x = β * β ∨ x = α ∨ x = α * β ∨ x = α * (β * β)) →
      (x * α = 1 ∨ x * α = β ∨ x * α = β * β ∨ x * α = α ∨ x * α = α * β ∨
        x * α = α * (β * β)) ∧
      (x * β = 1 ∨ x * β = β ∨ x * β = β * β ∨ x * β = α ∨ x * β = α * β ∨
        x * β = α * (β * β)) := by
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [mul_assoc, one_mul, hα, hβ, hβα, hα', hβα', mul_one] <;> simp
  induction hφ using Subgroup.closure_induction_right with
  | one => exact Or.inl rfl
  | mul_right x _ y hy hx =>
    rcases hy with rfl | rfl
    · exact (hstep x hx).1
    · exact (hstep x hx).2
  | mul_inv_cancel x _ y hy hx =>
    rcases hy with rfl | rfl
    · rw [hαinv]
      exact (hstep x hx).1
    · rw [hβinv, ← mul_assoc]
      exact (hstep _ (hstep x hx).2).2

variable {G : Type u} [Group G]

@[expose] def conjAut (U : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (U : Set G)) :
    MulAut U :=
  U.normalizerMonoidHom ⟨x⁻¹, (Subgroup.normalizer (U : Set G)).inv_mem hx⟩

theorem conjAut_apply_coe (U : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (U : Set G))
    (y : U) : (conjAut U hx y : G) = x⁻¹ * y * x := by
  rw [conjAut, Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]

theorem conjAut_eq_inv (U : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (U : Set G)) :
    conjAut U hx = (U.normalizerMonoidHom ⟨x, hx⟩)⁻¹ := by
  rw [conjAut, ← map_inv]
  rfl

theorem conjAut_mem_range (U : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (U : Set G)) :
    conjAut U hx ∈ U.normalizerMonoidHom.range :=
  ⟨_, rfl⟩

theorem mulAut_ext_of_closure {U : Subgroup G} {x y : U} (hcl : Subgroup.closure {x, y} = ⊤)
    {φ ψ : MulAut U} (hx : φ x = ψ x) (hy : φ y = ψ y) : φ = ψ := by
  have h : φ.toMonoidHom = ψ.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense hcl
    rintro z (rfl | rfl)
    · exact hx
    · exact hy
  ext z
  exact congrArg Subtype.val (DFunLike.congr_fun h z)

theorem closure_subtype_eq_top {U : Subgroup G} {x y : G} (hx : x ∈ U) (hy : y ∈ U)
    (hcl : Subgroup.closure {x, y} = U) :
    Subgroup.closure {(⟨x, hx⟩ : U), ⟨y, hy⟩} = ⊤ := by
  apply Subgroup.map_injective U.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact hcl

namespace IsAdaptedBase

variable {U : Subgroup G} {a w σ υ g : G}

@[expose] def left (h : IsAdaptedBase U a w σ υ g) : U := ⟨σ, h.left_mem⟩

@[expose] def right (h : IsAdaptedBase U a w σ υ g) : U := ⟨υ, h.right_mem⟩

@[expose] def aut (h : IsAdaptedBase U a w σ υ g) : MulAut U := conjAut U h.mem_normalizer

theorem coe_left (h : IsAdaptedBase U a w σ υ g) : (h.left : G) = σ := rfl

theorem coe_right (h : IsAdaptedBase U a w σ υ g) : (h.right : G) = υ := rfl

theorem coe_left_mul_right (h : IsAdaptedBase U a w σ υ g) :
    ((h.left * h.right : U) : G) = a := h.mul_eq

theorem aut_apply_coe (h : IsAdaptedBase U a w σ υ g) (y : U) :
    (h.aut y : G) = g⁻¹ * y * g :=
  conjAut_apply_coe U h.mem_normalizer y

theorem closure_eq_top (h : IsAdaptedBase U a w σ υ g) :
    Subgroup.closure {h.left, h.right} = ⊤ :=
  closure_subtype_eq_top h.left_mem h.right_mem h.closure_eq

theorem aut_left (h : IsAdaptedBase U a w σ υ g) : h.aut h.left = h.right :=
  Subtype.ext (by rw [aut_apply_coe]; exact h.conj_left)

theorem aut_right (h : IsAdaptedBase U a w σ υ g) :
    h.aut h.right = (h.left * h.right)⁻¹ :=
  Subtype.ext (by
    rw [aut_apply_coe, Subgroup.coe_inv, coe_left_mul_right]
    exact h.conj_right)

theorem aut_left_mul_right (h : IsAdaptedBase U a w σ υ g) :
    h.aut (h.left * h.right) = h.left⁻¹ := by
  rw [map_mul, aut_left, aut_right, mul_inv_rev, mul_inv_cancel_left]

theorem swap_left (h : IsAdaptedBase U a w σ υ g)
    (hw : w ∈ Subgroup.normalizer (U : Set G)) : conjAut U hw h.left = h.right :=
  Subtype.ext (by rw [conjAut_apply_coe]; exact h.conj_swap)

theorem swap_right (h : IsAdaptedBase U a w σ υ g)
    (hw : w ∈ Subgroup.normalizer (U : Set G)) (hw2 : w⁻¹ = w) :
    conjAut U hw h.right = h.left :=
  Subtype.ext (by
    rw [conjAut_apply_coe, coe_right, coe_left, ← h.conj_swap, hw2]
    calc w * (w * σ * w) * w = (w * w) * σ * (w * w) := by simp only [mul_assoc]
      _ = σ := by
        rw [show w * w = 1 by rw [← mul_inv_cancel w, hw2], one_mul, mul_one])

theorem aut_cube (h : IsAdaptedBase U a w σ υ g) : h.aut * (h.aut * h.aut) = 1 := by
  apply mulAut_ext_of_closure h.closure_eq_top
  · rw [MulAut.mul_apply, MulAut.mul_apply, aut_left, aut_right, map_inv, aut_left_mul_right,
      inv_inv, MulAut.one_apply]
  · rw [MulAut.mul_apply, MulAut.mul_apply, aut_right, map_inv, aut_left_mul_right, inv_inv,
      aut_left, MulAut.one_apply]

end IsAdaptedBase

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem swap_mem_normalizer :
    wreathModelHom S e (Original.z (2 ^ n)) ∈ Subgroup.normalizer (modelBase S e : Set G) :=
  sylow_le_modelBase_normalizer S e (wreathModelHom_mem S e _)

theorem swap_inv :
    (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ = wreathModelHom S e (Original.z (2 ^ n)) := by
  rw [← map_inv]
  congr 1
  rw [Original.z, element_swap_inv, neg_zero]

@[expose] def swapAut : MulAut (modelBase S e) := conjAut _ (swap_mem_normalizer S e)

theorem swapAut_apply_coe (y : modelBase S e) :
    (swapAut S e y : G) = (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ * y *
      wreathModelHom S e (Original.z (2 ^ n)) :=
  conjAut_apply_coe _ _ y

theorem swapAut_mem_range : swapAut S e ∈ (modelBase S e).normalizerMonoidHom.range :=
  conjAut_mem_range _ _

theorem mul_comm_base (x y : modelBase S e) : x * y = y * x :=
  Subtype.ext (modelBase_commute S e _ _ x.2 y.2)

section Adapted

variable {S e} {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
    (wreathModelHom S e (Original.z (2 ^ n))) σ υ g)
include h

variable [Finite G] in
theorem orderOf_left : orderOf σ = 2 ^ n :=
  ((closure_pair_eq_modelBase_iff S e h.left_mem h.right_mem).mp h.closure_eq).1

variable [Finite G] in
theorem orderOf_right : orderOf υ = 2 ^ n :=
  ((closure_pair_eq_modelBase_iff S e h.left_mem h.right_mem).mp h.closure_eq).2.1

variable [Finite G] in
theorem zpowers_left_inf_right : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥ :=
  ((closure_pair_eq_modelBase_iff S e h.left_mem h.right_mem).mp h.closure_eq).2.2

variable [Finite G] in
theorem left_ne_right (hn : 1 ≤ n) : h.left ≠ h.right := by
  intro heq
  have hσυ : σ = υ := congrArg Subtype.val heq
  have hmem : σ ∈ Subgroup.zpowers σ ⊓ Subgroup.zpowers υ :=
    ⟨Subgroup.mem_zpowers σ, hσυ ▸ Subgroup.mem_zpowers υ⟩
  rw [zpowers_left_inf_right h, Subgroup.mem_bot] at hmem
  have hord := orderOf_left h
  rw [hmem, orderOf_one] at hord
  have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  omega

theorem swapAut_left : swapAut S e h.left = h.right := h.swap_left _

theorem swapAut_right : swapAut S e h.right = h.left := h.swap_right _ (swap_inv S e)

theorem swapAut_left_mul_right : swapAut S e (h.left * h.right) = h.left * h.right := by
  rw [map_mul, swapAut_left h, swapAut_right h, mul_comm_base]

theorem swapAut_mul_self : swapAut S e * swapAut S e = 1 := by
  apply mulAut_ext_of_closure h.closure_eq_top
  · rw [MulAut.mul_apply, swapAut_left h, swapAut_right h, MulAut.one_apply]
  · rw [MulAut.mul_apply, swapAut_right h, swapAut_left h, MulAut.one_apply]

theorem aut_mul_swapAut : h.aut * swapAut S e = swapAut S e * (h.aut * h.aut) := by
  apply mulAut_ext_of_closure h.closure_eq_top
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, swapAut_left h, h.aut_left,
      h.aut_right, map_inv, swapAut_left_mul_right h]
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, swapAut_right h, h.aut_left,
      h.aut_right, map_inv, h.aut_left_mul_right, inv_inv, swapAut_left h]

theorem mem_closure_swapAut_aut {φ : MulAut (modelBase S e)}
    (hφ : φ ∈ Subgroup.closure {swapAut S e, h.aut}) :
    φ = 1 ∨ φ = h.aut ∨ φ = h.aut * h.aut ∨ φ = swapAut S e ∨ φ = swapAut S e * h.aut ∨
      φ = swapAut S e * (h.aut * h.aut) :=
  mem_closure_cases (swapAut_mul_self h) h.aut_cube (aut_mul_swapAut h) hφ

theorem orderOf_aut : orderOf h.aut = 3 := by
  rw [IsAdaptedBase.aut, conjAut_eq_inv, orderOf_inv]
  exact h.orderOf_conj

theorem closure_le_range :
    Subgroup.closure {swapAut S e, h.aut} ≤ (modelBase S e).normalizerMonoidHom.range := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact swapAut_mem_range S e
  · exact conjAut_mem_range _ _

variable [Finite G]

theorem orderOf_swapAut (hn : 1 ≤ n) : orderOf (swapAut S e) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [pow_two]
    exact swapAut_mul_self h
  · intro h1
    have h' := swapAut_left h
    rw [h1, MulAut.one_apply] at h'
    exact left_ne_right h hn h'

theorem card_range (hn : 1 ≤ n) :
    Nat.card (modelBase S e).normalizerMonoidHom.range = 6 := by
  have hiso : Nat.card (modelBase S e).normalizerMonoidHom.range =
      Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
        (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelBase S e : Set G))) :=
    Nat.card_congr ((QuotientGroup.quotientKerEquivRange _).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalizerMonoidHom_ker _))).toEquiv
  have h3 : 3 ∣ Nat.card (modelBase S e).normalizerMonoidHom.range := by
    have hd := Subgroup.orderOf_dvd_natCard _ (conjAut_mem_range _ h.mem_normalizer)
    rwa [← IsAdaptedBase.aut, orderOf_aut h] at hd
  rcases modelBaseNormalizerQuotient_alternatives n hn S e with h2 | hsix
  · rw [hiso, h2] at h3
    omega
  · obtain ⟨esix⟩ := hsix
    rw [hiso, Nat.card_congr esix.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    rfl

theorem range_eq_closure (hn : 1 ≤ n) :
    (modelBase S e).normalizerMonoidHom.range = Subgroup.closure {swapAut S e, h.aut} := by
  have hle := closure_le_range h
  have h2 : 2 ∣ Nat.card (Subgroup.closure {swapAut S e, h.aut}) := by
    have hd := Subgroup.orderOf_dvd_natCard (Subgroup.closure {swapAut S e, h.aut})
      (Subgroup.subset_closure (Set.mem_insert (swapAut S e) {h.aut}))
    rwa [orderOf_swapAut h hn] at hd
  have h3 : 3 ∣ Nat.card (Subgroup.closure {swapAut S e, h.aut}) := by
    have hd := Subgroup.orderOf_dvd_natCard (Subgroup.closure {swapAut S e, h.aut})
      (Subgroup.subset_closure (Set.mem_insert_of_mem (swapAut S e) (Set.mem_singleton h.aut)))
    rwa [orderOf_aut h] at hd
  have h6 : 6 ∣ Nat.card (Subgroup.closure {swapAut S e, h.aut}) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_range h hn]
  exact Nat.le_of_dvd Nat.card_pos h6

theorem card_closure (hn : 1 ≤ n) : Nat.card (Subgroup.closure {swapAut S e, h.aut}) = 6 := by
  rw [← range_eq_closure h hn, card_range h hn]

theorem isConj_iff_exists (hn : 2 ≤ n) (x y : modelBase S e) :
    IsConj (x : G) y ↔ ∃ φ ∈ Subgroup.closure {swapAut S e, h.aut}, φ x = y := by
  rw [← range_eq_closure h (by omega)]
  constructor
  · intro hxy
    obtain ⟨k, hk, hxk⟩ := (base_isConj_iff S e hn x.2 y.2).mp hxy
    exact ⟨conjAut _ hk, conjAut_mem_range _ hk,
      Subtype.ext (by rw [conjAut_apply_coe]; exact hxk)⟩
  · rintro ⟨φ, ⟨k, rfl⟩, hφ⟩
    refine isConj_iff.mpr ⟨k, ?_⟩
    rw [← hφ, Subgroup.normalizerMonoidHom_apply_apply_coe]

end Adapted

end CFSG.Wreathed.AdaptedBaseFusion
