module

public import CFSG.LieType.Multipliers.U43Field
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.LieType.Multipliers.U43 Matrix

@[expose] def anticommW1 : Matrix (Fin 2) (Fin 2) F9 := !![0, ⟨0, 1⟩; ⟨0, 1⟩, 0]

@[expose] def anticommW2 : Matrix (Fin 2) (Fin 2) F9 := !![⟨1, 1⟩, ⟨1, 1⟩; ⟨2, 1⟩, ⟨1, 2⟩]

@[expose] def anticommW3 : Matrix (Fin 2) (Fin 2) F9 := !![0, 1; ⟨2, 0⟩, 0]

theorem anticommW1_unitary : (anticommW1.map (· ^ 3))ᵀ * anticommW1 = 1 := by decide +kernel

theorem anticommW2_unitary : (anticommW2.map (· ^ 3))ᵀ * anticommW2 = 1 := by decide +kernel

theorem anticommW3_unitary : (anticommW3.map (· ^ 3))ᵀ * anticommW3 = 1 := by decide +kernel

theorem anticommW1_det : anticommW1.det = 1 := by decide +kernel

theorem anticommW2_det : anticommW2.det = 1 := by decide +kernel

theorem anticommW3_det : anticommW3.det = 1 := by decide +kernel

theorem anticomm_entries_F9 : ∀ a b c d : F9,
    ((!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F9).map (· ^ 3))ᵀ * !![a, b; c, d] = 1 →
    (∀ x : F9, (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F9) ≠
      x • (1 : Matrix (Fin 2) (Fin 2) F9)) →
    (∃ ζ : F9, (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F9) * !![a, b; c, d] =
      ζ • (1 : Matrix (Fin 2) (Fin 2) F9)) →
    ∃ w ∈ [anticommW1, anticommW2, anticommW3],
      (w * !![a, b; c, d] * (w.map (· ^ 3))ᵀ) * !![a, b; c, d] =
        -(!![a, b; c, d] * (w * !![a, b; c, d] * (w.map (· ^ 3))ᵀ)) := by
  decide +kernel

theorem anticomm_F9 (P : Matrix (Fin 2) (Fin 2) F9) (hP : (P.map (· ^ 3))ᵀ * P = 1)
    (hns : ∀ x : F9, P ≠ x • (1 : Matrix (Fin 2) (Fin 2) F9))
    (hsq : ∃ ζ : F9, P * P = ζ • (1 : Matrix (Fin 2) (Fin 2) F9)) :
    ∃ w ∈ [anticommW1, anticommW2, anticommW3],
      (w * P * (w.map (· ^ 3))ᵀ) * P = -(P * (w * P * (w.map (· ^ 3))ᵀ)) := by
  have hP' := Matrix.eta_fin_two P
  rw [hP'] at hP hns hsq ⊢
  exact anticomm_entries_F9 _ _ _ _ hP hns hsq

theorem map_conjTranspose_cube {K : Type} [Field K] (ρ : K ≃+* F9)
    (X : Matrix (Fin 2) (Fin 2) K) :
    ρ.toRingHom.mapMatrix ((X.map (· ^ 3))ᵀ) = ((ρ.toRingHom.mapMatrix X).map (· ^ 3))ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, map_pow]

theorem exists_anticommuting_conjugate {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9)
    (P : Matrix (Fin 2) (Fin 2) K) (hP : (P.map (· ^ 3))ᵀ * P = 1)
    (hns : ∀ x : K, P ≠ x • (1 : Matrix (Fin 2) (Fin 2) K))
    (hsq : ∃ ζ : K, P * P = ζ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ w : Matrix (Fin 2) (Fin 2) K, w.det = 1 ∧ (w.map (· ^ 3))ᵀ * w = 1 ∧
      (w * P * (w.map (· ^ 3))ᵀ) * P = -(P * (w * P * (w.map (· ^ 3))ᵀ)) := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, hK, F9.card_eq]
  let ρ : K ≃+* F9 := FiniteField.ringEquivOfCardEq hc
  let Φ : Matrix (Fin 2) (Fin 2) K →+* Matrix (Fin 2) (Fin 2) F9 := ρ.toRingHom.mapMatrix
  let Ψ : Matrix (Fin 2) (Fin 2) F9 →+* Matrix (Fin 2) (Fin 2) K := ρ.symm.toRingHom.mapMatrix
  have hΦΨ : ∀ X, Φ (Ψ X) = X := fun X => by
    refine Matrix.ext fun i j => ?_
    simp [Φ, Ψ, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hΦinj : Function.Injective Φ := fun X Y h => by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h i) j
    simpa [Φ, RingHom.mapMatrix_apply, Matrix.map_apply] using this
  have hΦsmul : ∀ x : K, Φ (x • (1 : Matrix (Fin 2) (Fin 2) K)) =
      ρ x • (1 : Matrix (Fin 2) (Fin 2) F9) := fun x => by
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j <;> simp [Φ, h, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hP' : ((Φ P).map (· ^ 3))ᵀ * Φ P = 1 := by
    rw [← map_conjTranspose_cube ρ, ← map_mul, hP, map_one]
  have hns' : ∀ x : F9, Φ P ≠ x • (1 : Matrix (Fin 2) (Fin 2) F9) := by
    intro x hx
    apply hns (ρ.symm x)
    apply hΦinj
    rw [hΦsmul, hx]
    simp
  have hsq' : ∃ ζ : F9, Φ P * Φ P = ζ • (1 : Matrix (Fin 2) (Fin 2) F9) := by
    obtain ⟨ζ, hζ⟩ := hsq
    exact ⟨ρ ζ, by rw [← map_mul, hζ, hΦsmul]⟩
  obtain ⟨w₀, hw₀, hw⟩ := anticomm_F9 (Φ P) hP' hns' hsq'
  have hw₀det : w₀.det = 1 ∧ (w₀.map (· ^ 3))ᵀ * w₀ = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw₀
    rcases hw₀ with rfl | rfl | rfl
    · exact ⟨anticommW1_det, anticommW1_unitary⟩
    · exact ⟨anticommW2_det, anticommW2_unitary⟩
    · exact ⟨anticommW3_det, anticommW3_unitary⟩
  have hcc : ∀ X : Matrix (Fin 2) (Fin 2) K, Φ ((X.map (· ^ 3))ᵀ) = ((Φ X).map (· ^ 3))ᵀ :=
    fun X => map_conjTranspose_cube ρ X
  refine ⟨Ψ w₀, ?_, ?_, ?_⟩
  · have := RingHom.map_det ρ.symm.toRingHom w₀
    rw [hw₀det.1, map_one] at this
    exact this.symm
  · apply hΦinj
    rw [map_mul, hcc, hΦΨ, map_one]
    exact hw₀det.2
  · apply hΦinj
    simp only [map_mul, map_neg, hcc, hΦΨ]
    exact hw

end CFSG.CGT.PushingUpLit.SolKNA
