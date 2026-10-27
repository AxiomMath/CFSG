module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Model
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSevenP0

public section

namespace CFSG.ComponentClassification.HSFLit

open Equiv Subgroup

@[expose] def half8 (b : ZMod 8) : ZMod 4 := ((b.val / 2 : ℕ) : ZMod 4)

@[expose] def ebit8 (u : ZMod 8) : ZMod 2 := if u = 3 ∨ u = 7 then 1 else 0

@[expose] def sgn8 (u : ZMod 8) : ZMod 4 := if ebit8 u = 0 then 1 else -1

@[expose] def coordP (s r : ZMod 4) (u : ZMod 8) (c : ZMod 4) : ZMod 4 × ZMod 2 × ZMod 2 :=
  (s * (c - r * ((ebit8 u).val : ZMod 4)), ebit8 u,
    ((s * (c - r * ((ebit8 u).val : ZMod 4))).val : ZMod 2) + ebit8 u + fbit8 u)

@[expose] def coordK (s r : ZMod 4) (σ : Perm (ZMod 8)) : ZMod 4 × ZMod 2 × ZMod 2 :=
  coordP s r (σ 1 - σ 0) (half8 (σ 0))

@[expose] def P7 (v : ZMod 4 × ZMod 2 × ZMod 2) : Perm (Fin 7) :=
  a0 ^ v.1.val * b0 ^ v.2.1.val * c0 ^ v.2.2.val

@[expose] def cmul (v w : ZMod 4 × ZMod 2 × ZMod 2) : ZMod 4 × ZMod 2 × ZMod 2 :=
  (v.1 + (if v.2.1 = 0 then w.1 else -w.1), v.2.1 + w.2.1, v.2.2 + w.2.2)

@[expose] def phiK (s r : ZMod 4) (σ : Perm (ZMod 8)) : Perm (Fin 7) := P7 (coordK s r σ)

theorem two_mul_val_add_mul : ∀ (u : (ZMod 8)ˣ) (c c' : ZMod 4),
    2 * (c.val : ZMod 8) + u * (2 * (c'.val : ZMod 8)) = 2 * ((c + sgn8 u * c').val : ZMod 8) := by
  decide

theorem neg_inv_mul_two_mul_val : ∀ (u : (ZMod 8)ˣ) (c : ZMod 4),
    -(↑u⁻¹ * (2 * (c.val : ZMod 8))) = 2 * ((-(sgn8 u * c)).val : ZMod 8) := by
  decide

@[expose] def R8KP : Subgroup (Perm (ZMod 8)) where
  carrier := {σ | ∃ (u : (ZMod 8)ˣ) (c : ZMod 4), aff8 u (2 * (c.val : ZMod 8)) = σ}
  one_mem' := ⟨1, 0, by rw [ZMod.val_zero, Nat.cast_zero, mul_zero, aff8_one]⟩
  mul_mem' := by
    rintro _ _ ⟨u, c, rfl⟩ ⟨u', c', rfl⟩
    exact ⟨u * u', c + sgn8 u * c', by rw [aff8_mul, two_mul_val_add_mul u c c']⟩
  inv_mem' := by
    rintro _ ⟨u, c, rfl⟩
    exact ⟨u⁻¹, -(sgn8 u * c), by rw [aff8_inv, neg_inv_mul_two_mul_val u c]⟩

theorem half8_two_mul : ∀ c : ZMod 4, half8 (2 * (c.val : ZMod 8)) = c := by decide

theorem two_mul_eq_two_mul_val : ∀ c : ZMod 8, ∃ c' : ZMod 4, 2 * c = 2 * (c'.val : ZMod 8) := by
  decide

theorem coordK_aff8 (s r : ZMod 4) (u : (ZMod 8)ˣ) (c : ZMod 4) :
    coordK s r (aff8 u (2 * (c.val : ZMod 8))) = coordP s r u c := by
  simp only [coordK, aff8_apply, mul_zero, zero_add, mul_one, add_sub_cancel_right,
    half8_two_mul]

theorem coordP_mul : ∀ s r : ZMod 4, (s = 1 ∨ s = 3) → ∀ (u u' : (ZMod 8)ˣ) (c c' : ZMod 4),
    coordP s r (u * u' : (ZMod 8)ˣ) (c + sgn8 u * c') =
      cmul (coordP s r u c) (coordP s r u' c') := by
  decide +kernel

theorem P7_mul : ∀ v w, P7 (cmul v w) = P7 v * P7 w := by decide +kernel

theorem P7_eq_one : ∀ v, P7 v = 1 → v = (0, 0, 0) := by decide +kernel

theorem phiK_one : ∀ s r, phiK s r 1 = 1 := by decide +kernel

theorem coordP_eq_zero : ∀ s r : ZMod 4, (s = 1 ∨ s = 3) → ∀ (u : (ZMod 8)ˣ) (c : ZMod 4),
    coordP s r u c = (0, 0, 0) → u = 1 ∧ c = 0 := by
  decide +kernel

theorem coordP_gens : ∀ s r : ZMod 4, (s = 1 ∨ s = 3) →
    coordP s r (1 : (ZMod 8)ˣ) s = (1, 0, 1) ∧ coordP s r (-1 : (ZMod 8)ˣ) r = (0, 1, 1) ∧
      coordP s r u5 0 = (0, 0, 1) := by
  decide +kernel

theorem coordP_inner : ∀ (s r : ZMod 4) (u : (ZMod 8)ˣ) (c : ZMod 4), (u = 1 ∨ u = -1) →
    (coordP s r u c).2.2 = ((coordP s r u c).1.val : ZMod 2) + (coordP s r u c).2.1 := by
  decide +kernel

theorem P7_inner : ∀ (a : ZMod 4) (e : ZMod 2),
    P7 (a, e, (a.val : ZMod 2) + e) = (a0 * b0 * (c0 * b0)) ^ a.val * (c0 * b0) ^ e.val := by
  decide +kernel

theorem P7_mem_P0 (v : ZMod 4 × ZMod 2 × ZMod 2) : P7 v ∈ P0 :=
  mul_mem (mul_mem (pow_mem a0_mem_P0 _) (pow_mem b0_mem_P0 _)) (pow_mem c0_mem_P0 _)

theorem R8_le_R8KP : R8 ≤ R8KP := by
  rintro _ ⟨u, c, -, rfl⟩
  obtain ⟨c', hc'⟩ := two_mul_eq_two_mul_val c
  exact ⟨u, c', by rw [hc']⟩

theorem k8_mem_R8KP : k8 ∈ R8KP :=
  ⟨u5, 0, by rw [ZMod.val_zero, Nat.cast_zero, mul_zero]⟩

theorem phiK_mul {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) {σ τ : Perm (ZMod 8)}
    (hσ : σ ∈ R8KP) (hτ : τ ∈ R8KP) : phiK s r (σ * τ) = phiK s r σ * phiK s r τ := by
  obtain ⟨u, c, rfl⟩ := hσ
  obtain ⟨u', c', rfl⟩ := hτ
  rw [phiK, aff8_mul, two_mul_val_add_mul u c c', coordK_aff8, coordP_mul s r hs, phiK, phiK,
    coordK_aff8, coordK_aff8, P7_mul]

theorem phiK_eq_one {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) {σ : Perm (ZMod 8)}
    (hσ : σ ∈ R8KP) : phiK s r σ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    obtain ⟨u, c, rfl⟩ := hσ
    rw [phiK, coordK_aff8] at h
    obtain ⟨rfl, rfl⟩ := coordP_eq_zero s r hs u c (P7_eq_one _ h)
    rw [ZMod.val_zero, Nat.cast_zero, mul_zero, aff8_one]
  · rintro rfl
    exact phiK_one s r

theorem phiK_mem_P0 (s r : ZMod 4) (σ : Perm (ZMod 8)) : phiK s r σ ∈ P0 := P7_mem_P0 _

theorem phiK_mem_R0 (s r : ZMod 4) {σ : Perm (ZMod 8)} (hσ : σ ∈ R8) : phiK s r σ ∈ R0 := by
  obtain ⟨u, c, hu, rfl⟩ := hσ
  obtain ⟨c', hc'⟩ := two_mul_eq_two_mul_val c
  rw [hc', phiK, coordK_aff8]
  have hv : coordP s r u c' = ((coordP s r u c').1, (coordP s r u c').2.1,
      ((coordP s r u c').1.val : ZMod 2) + (coordP s r u c').2.1) := by
    rw [← coordP_inner s r u c' hu]
  rw [hv, P7_inner]
  exact mul_mem (pow_mem (mul_mem a0_b0_mem_R0 c0_b0_mem_R0) _) (pow_mem c0_b0_mem_R0 _)

theorem phiK_x {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) :
    phiK s r (aff8 1 (2 * (s.val : ZMod 8))) = rho0 := by
  rw [phiK, coordK_aff8, (coordP_gens s r hs).1]
  decide

theorem phiK_y {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) :
    phiK s r (aff8 (-1) (2 * (r.val : ZMod 8))) = c0 * b0 := by
  rw [phiK, coordK_aff8, (coordP_gens s r hs).2.1]
  decide

theorem phiK_k8 {s : ZMod 4} (r : ZMod 4) (hs : s = 1 ∨ s = 3) : phiK s r k8 = c0 := by
  have h := coordK_aff8 s r u5 0
  rw [ZMod.val_zero, Nat.cast_zero, mul_zero] at h
  rw [phiK, h, (coordP_gens s r hs).2.2]
  decide

@[expose] def PairParam (u : (ZMod 8)ˣ) (c : ZMod 8) (u' : (ZMod 8)ˣ) (c' : ZMod 8) : Prop :=
  (u = 1 ∨ u = -1) → (u' = 1 ∨ u' = -1) → aff8 u (2 * c) * aff8 u (2 * c) ≠ 1 →
    aff8 u' (2 * c') * aff8 u (2 * c) = (aff8 u (2 * c))⁻¹ * aff8 u' (2 * c') →
      u = 1 ∧ (half8 (2 * c) = 1 ∨ half8 (2 * c) = 3) ∧ u' = -1

instance (u c u' c') : Decidable (PairParam u c u' c') := by unfold PairParam; infer_instance

theorem pairParam : ∀ u c u' c', PairParam u c u' c' := by decide +kernel

theorem two_mul_half8 : ∀ c : ZMod 8, 2 * c = 2 * ((half8 (2 * c)).val : ZMod 8) := by decide

theorem exists_pair_param {σx σy : Perm (ZMod 8)} (hx : σx ∈ R8) (hy : σy ∈ R8)
    (hx2 : σx * σx ≠ 1) (hyx : σy * σx = σx⁻¹ * σy) :
    ∃ s r : ZMod 4, (s = 1 ∨ s = 3) ∧ σx = aff8 1 (2 * (s.val : ZMod 8)) ∧
      σy = aff8 (-1) (2 * (r.val : ZMod 8)) := by
  obtain ⟨u, c, hu, rfl⟩ := hx
  obtain ⟨u', c', hu', rfl⟩ := hy
  obtain ⟨rfl, hs, rfl⟩ := pairParam u c u' c' hu hu' hx2 hyx
  exact ⟨half8 (2 * c), half8 (2 * c'), hs, by rw [← two_mul_half8], by rw [← two_mul_half8]⟩

end CFSG.ComponentClassification.HSFLit
