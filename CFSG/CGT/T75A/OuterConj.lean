module

public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity

public section

namespace CFSG.CGT.T75A

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

theorem outer_involution_bar_conj_P {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K)
    (α : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
    (hα : orderOf α = 2) (hout : ∀ y, α ≠ MulAut.conj y) :
    ∃ θ : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≃*
        primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      ∀ x, α (θ x) =
        θ (primeFormFieldAut h isPrimeFormGram_one (fieldDataHermitianForm h).conj x) := by
  have hq : ¬(3 = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hlift := even_unitary_involution_matrix_lifts h isPrimeFormGram_one (by norm_num) hq α hα
  rcases hlift.1 with hφ | hφ
  · obtain ⟨s, -, -, hs⟩ := hlift.2.1 hφ
    exact absurd (hs.trans (primeFormConjHom_eq_conj h _ s)) (hout _)
  obtain ⟨-, -, C₀, hC₀, hC₀1, -, -, -, -, ⟨θ, -, hθα⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h isPrimeFormGram_one (by norm_num) hq α hα hφ
  obtain rfl : C₀ = 1 := by
    rcases hC₀1 with h1 | ⟨r, hr, -⟩
    · exact Units.ext h1
    · omega
  have hφJ : primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq α =
      (fieldDataHermitianForm h).conj := RingEquiv.ext fun x => (hφ x).trans rfl
  refine ⟨θ, fun x => ?_⟩
  have h1 := hθα (θ x)
  rw [MulEquiv.symm_apply_apply, hφJ] at h1
  exact h1

theorem transport_outer {D P : Type} [Group D] [Group P] (Φ : D ≃* P) {α : MulAut D}
    (hα : orderOf α = 2) (hout : α ∉ (MulAut.conj : D →* MulAut D).range) :
    orderOf (MulAut.congr Φ α) = 2 ∧ ∀ y : P, MulAut.congr Φ α ≠ MulAut.conj y := by
  refine ⟨by rw [MulEquiv.orderOf_eq, hα], fun y hy => hout ⟨Φ.symm y, ?_⟩⟩
  apply (MulAut.congr Φ).injective
  rw [hy]
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem outer_involutions_conj {D : Type} [Group D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) {α β : MulAut D} (hα : orderOf α = 2)
    (hβ : orderOf β = 2) (hαout : α ∉ (MulAut.conj : D →* MulAut D).range)
    (hβout : β ∉ (MulAut.conj : D →* MulAut D).range) : IsConj α β := by
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨eD⟩⟩ := hD
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  let Φ : D ≃* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    eD.trans ((unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm.trans
      (unitaryPSUEquivPrimeFormOne h 3))
  obtain ⟨hα2, hαo⟩ := transport_outer Φ hα hαout
  obtain ⟨hβ2, hβo⟩ := transport_outer Φ hβ hβout
  obtain ⟨θa, hθa⟩ := outer_involution_bar_conj_P hf h _ hα2 hαo
  obtain ⟨θb, hθb⟩ := outer_involution_bar_conj_P hf h _ hβ2 hβo
  let γ' : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := θa.symm.trans θb
  have hγ' : γ' * MulAut.congr Φ α * γ'⁻¹ = MulAut.congr Φ β := by
    ext y
    obtain ⟨x, rfl⟩ := θb.surjective y
    have h1 : γ'⁻¹ (θb x) = θa x := by
      change θa (θb.symm (θb x)) = θa x
      rw [MulEquiv.symm_apply_apply]
    rw [MulAut.mul_apply, MulAut.mul_apply, h1, hθa x]
    change θb (θa.symm (θa _)) = _
    rw [MulEquiv.symm_apply_apply, hθb x]
  refine isConj_iff.2 ⟨(MulAut.congr Φ).symm γ', ?_⟩
  apply (MulAut.congr Φ).injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hγ'

end CFSG.CGT.T75A
