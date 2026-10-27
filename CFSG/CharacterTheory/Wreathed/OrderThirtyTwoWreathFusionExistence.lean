module

public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusionClasses

public noncomputable section

namespace CFSG.Wreathed.OrderThirtyTwo

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.AdaptedBaseFusion

universe u

variable {G : Type u} [Group G] {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ 2)}

theorem swap_conj_s :
    (wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * wreathModelHom S e (Original.s (2 ^ 2)) *
      wreathModelHom S e (Original.z (2 ^ 2)) = wreathModelHom S e (Original.t (2 ^ 2)) := by
  rw [← map_inv, ← map_mul, ← map_mul, Original.s, swap_conj_base]
  rfl

theorem isAdaptedBase_swap_sq {σ υ g : G}
    (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ 2)))
      (wreathModelHom S e (Original.z (2 ^ 2))) σ υ g) :
    IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ 2)))
      (wreathModelHom S e (Original.z (2 ^ 2))) υ σ (g ^ 2) where
  left_mem := h.right_mem
  right_mem := h.left_mem
  closure_eq := by
    rw [Set.pair_comm]
    exact h.closure_eq
  mul_eq := (modelBase_commute S e υ σ h.right_mem h.left_mem).trans h.mul_eq
  conj_swap := by
    have h' := congrArg Subtype.val (h.swap_right (swap_mem_normalizer S e) (swap_inv S e))
    rwa [conjAut_apply_coe] at h'
  conj_left := by
    have hA : g⁻¹ * wreathModelHom S e (Original.a (2 ^ 2)) * g = σ⁻¹ := by
      rw [← h.mul_eq, conj_mul_eq, h.conj_left, h.conj_right, ← h.mul_eq, mul_inv_rev,
        mul_inv_cancel_left]
    calc (g ^ 2)⁻¹ * υ * g ^ 2 = g⁻¹ * (g⁻¹ * υ * g) * g := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = (g⁻¹ * wreathModelHom S e (Original.a (2 ^ 2)) * g)⁻¹ := by
          rw [h.conj_right]
          simp only [mul_inv_rev, inv_inv, mul_assoc]
      _ = σ := by rw [hA, inv_inv]
  conj_right := by
    calc (g ^ 2)⁻¹ * σ * g ^ 2 = g⁻¹ * (g⁻¹ * σ * g) * g := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = _ := by rw [h.conj_left, h.conj_right]
  mem_normalizer := Subgroup.pow_mem _ h.mem_normalizer 2
  orderOf_conj := by
    have hpow : (modelBase S e).normalizerMonoidHom
        ⟨g ^ 2, Subgroup.pow_mem _ h.mem_normalizer 2⟩ =
          ((modelBase S e).normalizerMonoidHom ⟨g, h.mem_normalizer⟩) ^ 2 := by
      rw [← map_pow]
      rfl
    rw [hpow, orderOf_pow' _ two_ne_zero, h.orderOf_conj]
    rfl

variable [Finite G]

theorem exists_isAdaptedBase_special [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x) :
    ∃ σ υ g : G, ((σ = wreathModelHom S e (Original.s (2 ^ 2)) ∧
        υ = wreathModelHom S e (Original.t (2 ^ 2))) ∨
      (σ = wreathModelHom S e (Original.s (2 ^ 2)) ^ 2 *
          wreathModelHom S e (Original.t (2 ^ 2)) ^ 3 ∧
        υ = wreathModelHom S e (Original.s (2 ^ 2)) ^ 3 *
          wreathModelHom S e (Original.t (2 ^ 2)) ^ 2)) ∧
      IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ 2)))
        (wreathModelHom S e (Original.z (2 ^ 2))) σ υ g := by
  obtain ⟨σ₀, υ₀, g₀, h₀⟩ := exists_isAdaptedBase S e hnonab (le_refl 2)
  set s := wreathModelHom S e (Original.s (2 ^ 2))
  set t := wreathModelHom S e (Original.t (2 ^ 2))
  have hsB : s ∈ modelBase S e :=
    (mem_modelBase_iff S e _).mpr (by rw [Original.s, element_mem_base])
  have hσ := left_pow_four h₀
  have hυ := right_pow_four h₀
  have hc := commute_left_right' h₀
  obtain ⟨p, hp⟩ := exists_coord_of_mem h₀ hsB
  have ht : t = coord σ₀ υ₀ (swapMap p) := by
    rw [← swap_coord h₀ p, ← hp]
    exact swap_conj_s.symm
  have hsum : p + swapMap p = (1, 1) := by
    apply coord_inj h₀
    rw [← coord_mul hσ hυ hc, ← hp, ← ht,
      show ((1, 1) : ZMod 4 × ZMod 4) = (1, 0) + (0, 1) by decide, ← coord_mul hσ hυ hc,
      coord_left, coord_right, h₀.mul_eq]
    change wreathModelHom S e (Original.s (2 ^ 2)) * wreathModelHom S e (Original.t (2 ^ 2)) =
      wreathModelHom S e (Original.s (2 ^ 2) * Original.t (2 ^ 2))
    rw [map_mul]
  have hcases : ∀ q : ZMod 4 × ZMod 4, q + swapMap q = (1, 1) →
      q = (1, 0) ∨ q = (0, 1) ∨ q = (2, 3) ∨ q = (3, 2) := by decide
  have hpow2 : ∀ r : ZMod 4 × ZMod 4, coord σ₀ υ₀ r ^ 2 = coord σ₀ υ₀ (2 • r) :=
    fun r => coord_pow hσ hυ hc r 2
  have hpow3 : ∀ r : ZMod 4 × ZMod 4, coord σ₀ υ₀ r ^ 3 = coord σ₀ υ₀ (3 • r) :=
    fun r => coord_pow hσ hυ hc r 3
  rcases hcases p hsum with rfl | rfl | rfl | rfl
  ·
    refine ⟨s, t, g₀, Or.inl ⟨rfl, rfl⟩, ?_⟩
    rw [hp, ht, show swapMap ((1, 0) : ZMod 4 × ZMod 4) = (0, 1) from rfl, coord_left,
      coord_right]
    exact h₀
  ·
    refine ⟨s, t, g₀ ^ 2, Or.inl ⟨rfl, rfl⟩, ?_⟩
    rw [hp, ht, show swapMap ((0, 1) : ZMod 4 × ZMod 4) = (1, 0) from rfl, coord_left,
      coord_right]
    exact isAdaptedBase_swap_sq h₀
  ·
    refine ⟨s ^ 2 * t ^ 3, s ^ 3 * t ^ 2, g₀, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [hp, ht, hpow2, hpow3, hpow2, hpow3, coord_mul hσ hυ hc, coord_mul hσ hυ hc,
      show 2 • ((2, 3) : ZMod 4 × ZMod 4) + 3 • swapMap (2, 3) = (1, 0) by decide,
      show 3 • ((2, 3) : ZMod 4 × ZMod 4) + 2 • swapMap (2, 3) = (0, 1) by decide,
      coord_left, coord_right]
    exact h₀
  ·
    refine ⟨s ^ 2 * t ^ 3, s ^ 3 * t ^ 2, g₀ ^ 2, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [hp, ht, hpow2, hpow3, hpow2, hpow3, coord_mul hσ hυ hc, coord_mul hσ hυ hc,
      show 2 • ((3, 2) : ZMod 4 × ZMod 4) + 3 • swapMap (3, 2) = (0, 1) by decide,
      show 3 • ((3, 2) : ZMod 4 × ZMod 4) + 2 • swapMap (3, 2) = (1, 0) by decide,
      coord_left, coord_right]
    exact isAdaptedBase_swap_sq h₀

end CFSG.Wreathed.OrderThirtyTwo
