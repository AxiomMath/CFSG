module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K]

structure UCtx (ι ρ : K ≃+* K) : Prop where
  ιinv : ∀ x, ι (ι x) = x
  ρ3 : ∀ x, ρ (ρ (ρ x)) = x
  comm : ∀ x, ρ (ι x) = ι (ρ x)
  c₀ : ∃ c : K, c ≠ 0 ∧ ρ c = c ∧ ι c = -c
  r₂ : ∃ r : K, r ≠ 0 ∧ r ≠ 1 ∧ ρ r = r ∧ ι r = r

variable (ρ : K ≃+* K) in
@[expose] def Ratv {n : ℕ} (v : Fin n → K) : Prop := ∀ i, ρ (v i) = v i

variable {ι ρ : K ≃+* K}

theorem ratv_add {n : ℕ} {a b : Fin n → K} (ha : Ratv ρ a) (hb : Ratv ρ b) : Ratv ρ (a + b) :=
  fun i => by simp [map_add, ha i, hb i]

theorem ratv_smul {n : ℕ} {c : K} {a : Fin n → K} (hc : ρ c = c) (ha : Ratv ρ a) :
    Ratv ρ (c • a) :=
  fun i => by simp [map_mul, hc, ha i]

namespace UCtx

variable (C : UCtx ι ρ)
include C

theorem ρ_herm {n : ℕ} {a b : Fin n → K} (ha : Ratv ρ a) (hb : Ratv ρ b) :
    ρ (herm ι a b) = herm ι a b := by
  rw [herm, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, C.comm, ha i, hb i]

end UCtx

@[expose] def Bf (ι : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K) (a b : Fin 3 → K) : K :=
  herm ι a (M *ᵥ b)

@[expose] def rowv (ι : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K) (a : Fin 3 → K) : Fin 3 → K :=
  fun j => Bf ι M a (Pi.single j 1)

variable (ρ) in
@[expose] def OnLine {n : ℕ} (c : K) (v : Fin n → K) : Prop :=
  ∃ μ : Fin n → K, Ratv ρ μ ∧ v = c • μ

section Bf

variable (M : Matrix (Fin 3) (Fin 3) K)

theorem Bf_add_right (a b b' : Fin 3 → K) : Bf ι M a (b + b') = Bf ι M a b + Bf ι M a b' := by
  simp [Bf, Matrix.mulVec_add, herm_add_right]

theorem Bf_smul_right (a b : Fin 3 → K) (c : K) : Bf ι M a (c • b) = c * Bf ι M a b := by
  simp [Bf, Matrix.mulVec_smul, herm_smul_right]

theorem Bf_add_left (a a' b : Fin 3 → K) : Bf ι M (a + a') b = Bf ι M a b + Bf ι M a' b := by
  simp [Bf, herm_add_left]

theorem Bf_smul_left (a b : Fin 3 → K) (c : K) : Bf ι M (c • a) b = ι c * Bf ι M a b := by
  simp [Bf, herm_smul_left]

theorem Bf_eq_sum (a b : Fin 3 → K) : Bf ι M a b = ∑ j, b j * rowv ι M a j := by
  have hb : b = ∑ j, b j • (Pi.single j 1 : Fin 3 → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hb]
  simp only [Bf, Matrix.mulVec_sum, Matrix.mulVec_smul, herm]
  simp only [rowv, Bf, herm, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem rowv_add (a a' : Fin 3 → K) : rowv ι M (a + a') = rowv ι M a + rowv ι M a' := by
  funext j
  simp [rowv, Bf_add_left]

theorem rowv_smul (a : Fin 3 → K) (c : K) : rowv ι M (c • a) = ι c • rowv ι M a := by
  funext j
  simp [rowv, Bf_smul_left]

theorem rowv_eq_zero_iff (hsurj : ∀ z, ∃ y, M *ᵥ y = z) (a : Fin 3 → K) :
    rowv ι M a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply eq_zero_of_herm ι
    intro z
    obtain ⟨y, rfl⟩ := hsurj z
    have : Bf ι M a y = 0 := by
      rw [Bf_eq_sum]
      simp [h]
    exact this
  · rintro rfl
    funext j
    simp [rowv, Bf]

end Bf

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
