module

public import CFSG.LieType.ReflectionGroups.F4ModThree
import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.LieType.ReflectionGroups.F4ModThree

private theorem f4Bil3_smul_left (x : ZMod 3) (u w : Fin 4 → ZMod 3) :
    f4Bil3 (x • u) w = x * f4Bil3 u w := by
  simp only [f4Bil3, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
  ring

private theorem f4Bil3_smul_right (x : ZMod 3) (u w : Fin 4 → ZMod 3) :
    f4Bil3 u (x • w) = x * f4Bil3 u w := by
  rw [f4Bil3_comm, f4Bil3_smul_left, f4Bil3_comm]

private theorem f4Bil3_neg_left (u w : Fin 4 → ZMod 3) : f4Bil3 (-u) w = -f4Bil3 u w := by
  simp only [f4Bil3, Fin.sum_univ_four, Pi.neg_apply]
  ring

private theorem f4Bil3_neg_right (u w : Fin 4 → ZMod 3) : f4Bil3 u (-w) = -f4Bil3 u w := by
  rw [f4Bil3_comm, f4Bil3_neg_left, f4Bil3_comm]

private theorem zmod3_eq_zero_of_neg_eq : ∀ x : ZMod 3, -x = x → x = 0 := by
  decide

private theorem zmod3_eq_zero_of_two_mul : ∀ x : ZMod 3, 2 * x = 0 → x = 0 := by
  decide

private theorem fin3_eq_sum_smul_single : ∀ u : Fin 3 → ZMod 3,
    u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 := by
  decide +kernel

private theorem update_single_neg_self : ∀ i : Fin 3,
    Function.update (Pi.single i 1 : Fin 3 → ZMod 3) i (-(Pi.single i 1 : Fin 3 → ZMod 3) i) =
      -Pi.single i 1 := by
  decide +kernel

private theorem update_single_neg_of_ne : ∀ i j : Fin 3, i ≠ j →
    Function.update (Pi.single j 1 : Fin 3 → ZMod 3) i (-(Pi.single j 1 : Fin 3 → ZMod 3) i) =
      Pi.single j 1 := by
  decide +kernel

private theorem single_comp_swap : ∀ i j : Fin 3,
    Pi.single i (1 : ZMod 3) ∘ Equiv.swap i j = Pi.single j 1 := by
  decide +kernel

private theorem card_ne_zero_fin3 : ∀ u : Fin 3 → ZMod 3,
    ((Finset.univ.filter fun i => u i ≠ 0).card : ZMod 3) = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  decide +kernel

private theorem eq_of_card_sumSq : ∀ c q : ZMod 3, q ≠ 0 →
    (Finset.univ.filter fun u : Fin 3 → ZMod 3 =>
      (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * c = q).card = 6 → c = q := by
  decide +kernel

theorem f4Q3_tau_of_signedPerms (v : Fin 4 → ZMod 3) (τ : (Fin 3 → ZMod 3) →+ (Fin 4 → ZMod 3))
    (hτ : Function.Injective τ) (hv : v ∉ Set.range τ)
    (hsign : ∀ i : Fin 3, ∃ g : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3),
      (∀ a b, f4Bil3 (g a) (g b) = f4Bil3 a b) ∧ g v = v ∧
      ∀ u, g (τ u) = τ (Function.update u i (-u i)))
    (hswap : ∀ i j : Fin 3, ∃ g : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3),
      (∀ a b, f4Bil3 (g a) (g b) = f4Bil3 a b) ∧ g v = v ∧
      ∀ u, g (τ u) = τ (u ∘ Equiv.swap i j)) :
    f4Q3 v ≠ 0 ∧ (∀ u, f4Bil3 v (τ u) = 0) ∧
      ∀ u, f4Q3 (τ u) = ((Finset.univ.filter fun i => u i ≠ 0).card : ZMod 3) * f4Q3 v := by
  have hτu : ∀ u, τ u =
      u 0 • τ (Pi.single 0 1) + u 1 • τ (Pi.single 1 1) + u 2 • τ (Pi.single 2 1) := by
    intro u
    conv_lhs => rw [fin3_eq_sum_smul_single u]
    rw [map_add, map_add, ZMod.map_smul, ZMod.map_smul, ZMod.map_smul]
  have hvi : ∀ i, f4Bil3 v (τ (Pi.single i 1)) = 0 := by
    intro i
    obtain ⟨g, hg, hgv, hgτ⟩ := hsign i
    have h := hg v (τ (Pi.single i 1))
    rw [hgv, hgτ, update_single_neg_self, map_neg, f4Bil3_neg_right] at h
    exact zmod3_eq_zero_of_neg_eq _ h
  have hij : ∀ i j, i ≠ j → f4Bil3 (τ (Pi.single i 1)) (τ (Pi.single j 1)) = 0 := by
    intro i j hne
    obtain ⟨g, hg, -, hgτ⟩ := hsign i
    have h := hg (τ (Pi.single i 1)) (τ (Pi.single j 1))
    rw [hgτ, hgτ, update_single_neg_self, update_single_neg_of_ne i j hne, map_neg,
      f4Bil3_neg_left] at h
    exact zmod3_eq_zero_of_neg_eq _ h
  have hii : ∀ i, f4Bil3 (τ (Pi.single i 1)) (τ (Pi.single i 1)) =
      f4Bil3 (τ (Pi.single 0 1)) (τ (Pi.single 0 1)) := by
    intro i
    obtain ⟨g, hg, -, hgτ⟩ := hswap i 0
    have h := hg (τ (Pi.single i 1)) (τ (Pi.single i 1))
    rw [hgτ, single_comp_swap] at h
    exact h.symm
  have hBv : ∀ u, f4Bil3 v (τ u) = 0 := by
    intro u
    simp only [hτu u, f4Bil3_add_right, f4Bil3_smul_right, hvi, mul_zero, add_zero]
  have hQτ : ∀ u, f4Q3 (τ u) = (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * f4Q3 (τ (Pi.single 0 1)) := by
    intro u
    simp only [f4Q3, hτu u, f4Bil3_add_left, f4Bil3_add_right, f4Bil3_smul_left,
      f4Bil3_smul_right, hij 0 1 (by decide), hij 0 2 (by decide), hij 1 0 (by decide),
      hij 1 2 (by decide), hij 2 0 (by decide), hij 2 1 (by decide), hii 1, hii 2]
    ring
  have hv0 : v ≠ 0 := fun h => hv ⟨0, by rw [map_zero, h]⟩
  have himage : Finset.univ.image τ =
      Finset.univ.filter fun w : Fin 4 → ZMod 3 => f4Bil3 v w = 0 := by
    refine Finset.eq_of_subset_of_card_le (fun w hw => ?_) ?_
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBv u⟩
    · rw [card_f4Perp3 v hv0, Finset.card_image_of_injective _ hτ]
      decide
  have hperp : ∀ w, f4Bil3 v w = 0 → ∃ u, τ u = w := by
    intro w hw
    have hw' : w ∈ Finset.univ.image τ := by
      rw [himage]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
    obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hw'
    exact ⟨u, hu⟩
  have hQv : f4Q3 v ≠ 0 := fun h => by
    obtain ⟨u, hu⟩ := hperp v (zmod3_eq_zero_of_two_mul _ h)
    exact hv ⟨u, hu⟩
  have hframe : f4Frame3 v = (Finset.univ.filter fun u : Fin 3 → ZMod 3 =>
      (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * f4Q3 (τ (Pi.single 0 1)) = f4Q3 v).image τ := by
    ext w
    simp only [f4Frame3, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hw, hQw⟩
      obtain ⟨u, rfl⟩ := hperp w hw
      exact ⟨u, (hQτ u).symm.trans hQw, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hBv u, (hQτ u).trans hu⟩
  have h6 := card_f4Frame3 v hQv
  rw [hframe, Finset.card_image_of_injective _ hτ] at h6
  refine ⟨hQv, hBv, fun u => ?_⟩
  rw [hQτ u, card_ne_zero_fin3 u, eq_of_card_sumSq _ _ hQv h6]

end CFSG.LieType.ReflectionGroups.F4ModThree
