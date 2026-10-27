module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

@[expose] def k5g0 : SL23 := ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def k5g1 : SL23 := ⟨!![1, 0; 2, 1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def k5g2 : SL23 := ⟨!![0, 1; 2, 2], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def k5g3 : SL23 := ⟨!![2, 1; 2, 0], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def k5g : Fin 4 → SL23 := ![k5g0, k5g1, k5g2, k5g3]

@[expose] def klein : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {v | v * v = 1 ∧ (v = 1 ∨ ∀ i, v i ≠ i)}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

theorem k5g_pow_three (i : Fin 4) : k5g i ^ 3 = 1 := by
  revert i
  decide +kernel

theorem k5g_ne_one (i : Fin 4) : k5g i ≠ 1 := by
  revert i
  decide +kernel

theorem exists_k5g_of_pow_three {s : SL23} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ i, s = k5g i ∨ s = (k5g i)⁻¹ :=
  (by decide +kernel : ∀ s : SL23, s ^ 3 = 1 → s ≠ 1 → ∃ i, s = k5g i ∨ s = (k5g i)⁻¹) s hs3 hs1

theorem comm_k5g {i j : Fin 4} (h : k5g i * k5g j = k5g j * k5g i) : i = j :=
  (by decide +kernel : ∀ i j : Fin 4, k5g i * k5g j = k5g j * k5g i → i = j) i j h

theorem card_cent_of_pow_three {s : SL23} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    (Finset.univ.filter fun t : SL23 => t * s = s * t).card = 6 :=
  (by decide +kernel : ∀ s : SL23, s ^ 3 = 1 → s ≠ 1 →
    (Finset.univ.filter fun t : SL23 => t * s = s * t).card = 6) s hs3 hs1

theorem sq_of_central {s : SL23} (h : ∀ t : SL23, s * t = t * s) : s * s = 1 :=
  (by decide +kernel : ∀ s : SL23, (∀ t : SL23, s * t = t * s) → s * s = 1) s h

theorem faith_k5g {x y : SL23} (hx : x = k5g 0 ∨ x = (k5g 0)⁻¹) (hy : y = k5g 1 ∨ y = (k5g 1)⁻¹)
    (h2 : x * y * x⁻¹ = k5g 2 ∨ x * y * x⁻¹ = (k5g 2)⁻¹)
    (h4 : (x * y) ^ 4 = 1 ↔ (k5g 0 * k5g 1) ^ 4 = 1) : x = k5g 0 ∧ y = k5g 1 :=
  (by decide +kernel : ∀ x y : SL23, (x = k5g 0 ∨ x = (k5g 0)⁻¹) → (y = k5g 1 ∨ y = (k5g 1)⁻¹) →
    (x * y * x⁻¹ = k5g 2 ∨ x * y * x⁻¹ = (k5g 2)⁻¹) →
    ((x * y) ^ 4 = 1 ↔ (k5g 0 * k5g 1) ^ 4 = 1) → x = k5g 0 ∧ y = k5g 1) x y hx hy h2 h4

private def growBy (W : Finset SL23) : Finset SL23 :=
  W ∪ W.image (· * k5g 0) ∪ W.image (· * (k5g 0)⁻¹) ∪ W.image (· * k5g 1) ∪
    W.image (· * (k5g 1)⁻¹)

private theorem grow4 : growBy (growBy (growBy (growBy {1}))) = Finset.univ := by
  decide +kernel

private theorem growBy_mem (W : Finset SL23)
    (h : ∀ w ∈ W, w ∈ Subgroup.closure {k5g 0, k5g 1}) :
    ∀ w ∈ growBy W, w ∈ Subgroup.closure {k5g 0, k5g 1} := by
  have h0 : k5g 0 ∈ Subgroup.closure {k5g 0, k5g 1} := Subgroup.subset_closure (by simp)
  have h1 : k5g 1 ∈ Subgroup.closure {k5g 0, k5g 1} := Subgroup.subset_closure (by simp)
  intro w hw
  simp only [growBy, Finset.mem_union, Finset.mem_image] at hw
  rcases hw with ((((hw | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
  · exact h w hw
  · exact mul_mem (h u hu) h0
  · exact mul_mem (h u hu) (inv_mem h0)
  · exact mul_mem (h u hu) h1
  · exact mul_mem (h u hu) (inv_mem h1)

theorem closure_k5g (s : SL23) : s ∈ Subgroup.closure {k5g 0, k5g 1} := by
  have h : s ∈ (growBy (growBy (growBy (growBy {1})))) := by
    rw [grow4]
    exact Finset.mem_univ s
  exact growBy_mem _ (growBy_mem _ (growBy_mem _ (growBy_mem _ (by simp)))) s h

theorem exists_pow_four_of_klein {v : Equiv.Perm (Fin 4)} (hv : v ∈ klein) :
    ∃ q : SL23, q ^ 4 = 1 ∧ ∀ i, q * k5g i * q⁻¹ = k5g (v i) ∨
      q * k5g i * q⁻¹ = (k5g (v i))⁻¹ :=
  (by decide +kernel : ∀ v : Equiv.Perm (Fin 4), (v * v = 1 ∧ (v = 1 ∨ ∀ i, v i ≠ i)) →
    ∃ q : SL23, q ^ 4 = 1 ∧ ∀ i, q * k5g i * q⁻¹ = k5g (v i) ∨
      q * k5g i * q⁻¹ = (k5g (v i))⁻¹) v hv

theorem sign_of_act {s : SL23} {τ : Equiv.Perm (Fin 4)}
    (h : ∀ i, s * k5g i * s⁻¹ = k5g (τ i) ∨ s * k5g i * s⁻¹ = (k5g (τ i))⁻¹) :
    Equiv.Perm.sign τ = 1 :=
  (by decide +kernel : ∀ (s : SL23) (τ : Equiv.Perm (Fin 4)),
    (∀ i, s * k5g i * s⁻¹ = k5g (τ i) ∨ s * k5g i * s⁻¹ = (k5g (τ i))⁻¹) →
    Equiv.Perm.sign τ = 1) s τ h

theorem odd_mul_klein_involution {p : Equiv.Perm (Fin 4)} (hp : Equiv.Perm.sign p = -1) :
    ∃ v ∈ klein, (p * v) * (p * v) = 1 := by
  obtain ⟨v, hv, h⟩ := (by decide +kernel : ∀ p : Equiv.Perm (Fin 4), Equiv.Perm.sign p = -1 →
    ∃ v : Equiv.Perm (Fin 4), (v * v = 1 ∧ (v = 1 ∨ ∀ i, v i ≠ i)) ∧ (p * v) * (p * v) = 1) p hp
  exact ⟨v, hv, h⟩

theorem three_of_even_not_klein {p : Equiv.Perm (Fin 4)} (hp : Equiv.Perm.sign p = 1)
    (hk : p ∉ klein) : p ^ 3 = 1 ∧ p ≠ 1 :=
  (by decide +kernel : ∀ p : Equiv.Perm (Fin 4), Equiv.Perm.sign p = 1 →
    ¬ (p * p = 1 ∧ (p = 1 ∨ ∀ i, p i ≠ i)) → p ^ 3 = 1 ∧ p ≠ 1) p hp hk

theorem sign_of_mem_klein {v : Equiv.Perm (Fin 4)} (hv : v ∈ klein) :
    Equiv.Perm.sign v = 1 :=
  (by decide +kernel : ∀ v : Equiv.Perm (Fin 4), (v * v = 1 ∧ (v = 1 ∨ ∀ i, v i ≠ i)) →
    Equiv.Perm.sign v = 1) v hv

end CFSG.OddStandard.SmallF3.Omega.K5
