module

public import CFSG.CharacterTheory.Wreathed.FourPointCentralFourierSupport

public noncomputable section

namespace CFSG.Wreathed.FourPointCentralFourier

open scoped BigOperators Classical

theorem evalRow_gram_block {ι : Type*} (B : Finset ι) (P Q P' Q' : ι → ℂ) (c₀ c₁ : ℂ)
    (h₀₀ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * P' χ = c₀)
    (h₀₁ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * Q' χ = 0)
    (h₁₀ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * P' χ = 0)
    (h₁₁ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * Q' χ = c₁) (ℓ t : Fin 2) :
    ∑ χ ∈ B, starRingEnd ℂ (evalRow (P χ) (Q χ) ℓ) * evalRow (P' χ) (Q' χ) t =
      ![![(c₀ + 4 * c₁) / 9, (c₀ - 2 * c₁) / 9], ![(c₀ - 2 * c₁) / 9, (c₀ + c₁) / 9]] ℓ t := by
  rw [evalRow_gram B P Q P' Q' c₀ 0 0 c₁ h₀₀ h₀₁ h₁₀ h₁₁ ℓ t]
  fin_cases ℓ <;> fin_cases t <;> simp

theorem evalRow_gram_M {ι : Type*} (B : Finset ι) (P Q P' Q' : ι → ℂ)
    (h₀₀ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * P' χ = 96)
    (h₀₁ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * Q' χ = 0)
    (h₁₀ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * P' χ = 0)
    (h₁₁ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * Q' χ = 12) (ℓ t : Fin 2) :
    ∑ χ ∈ B, starRingEnd ℂ (evalRow (P χ) (Q χ) ℓ) * evalRow (P' χ) (Q' χ) t =
      (((!![16, 8; 8, 12] : Matrix (Fin 2) (Fin 2) ℤ) ℓ t : ℤ) : ℂ) := by
  rw [evalRow_gram_block B P Q P' Q' 96 12 h₀₀ h₀₁ h₁₀ h₁₁ ℓ t]
  fin_cases ℓ <;> fin_cases t <;> norm_num

theorem evalRow_gram_zero {ι : Type*} (B : Finset ι) (P Q P' Q' : ι → ℂ)
    (h₀₀ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * P' χ = 0)
    (h₀₁ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * Q' χ = 0)
    (h₁₀ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * P' χ = 0)
    (h₁₁ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * Q' χ = 0) (ℓ t : Fin 2) :
    ∑ χ ∈ B, starRingEnd ℂ (evalRow (P χ) (Q χ) ℓ) * evalRow (P' χ) (Q' χ) t = 0 := by
  rw [evalRow_gram_block B P Q P' Q' 0 0 h₀₀ h₀₁ h₁₀ h₁₁ ℓ t]
  fin_cases ℓ <;> fin_cases t <;> simp

theorem conj_evalRow (P Q : ℂ) (ℓ : Fin 2) :
    starRingEnd ℂ (evalRow P Q ℓ) = evalRow (starRingEnd ℂ P) (starRingEnd ℂ Q) ℓ := by
  fin_cases ℓ <;> simp [evalRow, map_div₀, map_ofNat]

theorem sum_conj_mul_eq_conj {ι : Type*} (B : Finset ι) (f g : ι → ℂ) :
    ∑ χ ∈ B, starRingEnd ℂ (f χ) * g χ = starRingEnd ℂ (∑ χ ∈ B, f χ * starRingEnd ℂ (g χ)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [map_mul, Complex.conj_conj]

theorem sum_conj_conj_mul {ι : Type*} (B : Finset ι) (f g : ι → ℂ) :
    ∑ χ ∈ B, starRingEnd ℂ (starRingEnd ℂ (f χ)) * g χ = ∑ χ ∈ B, f χ * g χ :=
  Finset.sum_congr rfl fun _ _ => by rw [Complex.conj_conj]

theorem sum_conj_mul_conj {ι : Type*} (B : Finset ι) (f g : ι → ℂ) :
    ∑ χ ∈ B, starRingEnd ℂ (f χ) * starRingEnd ℂ (g χ) = starRingEnd ℂ (∑ χ ∈ B, f χ * g χ) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun χ _ => (map_mul _ _ _).symm

theorem sum_conj_real_mul {ι : Type*} (B : Finset ι) (f g : ι → ℂ)
    (hg : ∀ χ ∈ B, starRingEnd ℂ (g χ) = g χ) :
    ∑ χ ∈ B, starRingEnd ℂ (g χ) * f χ = ∑ χ ∈ B, f χ * g χ :=
  Finset.sum_congr rfl fun χ hχ => by rw [hg χ hχ, mul_comm]

theorem sum_conj_mul_real {ι : Type*} (B : Finset ι) (f g : ι → ℂ)
    (hg : ∀ χ ∈ B, starRingEnd ℂ (g χ) = g χ) :
    ∑ χ ∈ B, starRingEnd ℂ (f χ) * g χ = starRingEnd ℂ (∑ χ ∈ B, f χ * g χ) := by
  rw [← sum_conj_mul_conj]
  exact Finset.sum_congr rfl fun χ hχ => by rw [hg χ hχ]

theorem sum_mul_comm {ι : Type*} (B : Finset ι) (f g : ι → ℂ) :
    ∑ χ ∈ B, f χ * g χ = ∑ χ ∈ B, g χ * f χ :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem central_rows_gram {ι : Type*} (B : Finset ι) (T U A Bv : ι → ℂ)
    (hA : ∀ χ ∈ B, starRingEnd ℂ (A χ) = A χ) (hB : ∀ χ ∈ B, starRingEnd ℂ (Bv χ) = Bv χ)
    (hTT : ∑ χ ∈ B, Complex.normSq (T χ) = 96) (hUU : ∑ χ ∈ B, Complex.normSq (U χ) = 12)
    (hTcU : ∑ χ ∈ B, T χ * starRingEnd ℂ (U χ) = 0)
    (hAA : ∑ χ ∈ B, A χ ^ 2 = 96) (hBB : ∑ χ ∈ B, Bv χ ^ 2 = 12)
    (hAB : ∑ χ ∈ B, A χ * Bv χ = 0)
    (hT2 : ∑ χ ∈ B, T χ ^ 2 = 0) (hU2 : ∑ χ ∈ B, U χ ^ 2 = 0) (hTU : ∑ χ ∈ B, T χ * U χ = 0)
    (hTA : ∑ χ ∈ B, T χ * A χ = 0) (hTB : ∑ χ ∈ B, T χ * Bv χ = 0)
    (hUA : ∑ χ ∈ B, U χ * A χ = 0) (hUB : ∑ χ ∈ B, U χ * Bv χ = 0)
    (row : ℕ → ι → Fin 2 → ℂ) (hrow1 : ∀ χ, row 1 χ = evalRow (T χ) (U χ))
    (hrow2 : ∀ χ, row 2 χ = evalRow (A χ) (Bv χ))
    (hrow3 : ∀ χ, row 3 χ = evalRow (starRingEnd ℂ (T χ)) (starRingEnd ℂ (U χ))) :
    ∀ k ∈ Finset.Ico 1 4, ∀ h ∈ Finset.Ico 1 4, ∀ ℓ t : Fin 2,
      ∑ χ ∈ B, starRingEnd ℂ (row k χ ℓ) * row h χ t =
        if k = h then (((!![16, 8; 8, 12] : Matrix (Fin 2) (Fin 2) ℤ) ℓ t : ℤ) : ℂ) else 0 := by
  have hsq : ∀ f : ι → ℂ, ∑ χ ∈ B, f χ * f χ = ∑ χ ∈ B, f χ ^ 2 := fun f =>
    Finset.sum_congr rfl fun χ _ => (sq _).symm
  have hn : ∀ f : ι → ℂ, ∑ χ ∈ B, starRingEnd ℂ (f χ) * f χ =
      ((∑ χ ∈ B, Complex.normSq (f χ) : ℝ) : ℂ) := fun f => by
    push_cast
    exact Finset.sum_congr rfl fun χ _ => Complex.normSq_eq_conj_mul_self.symm
  have hn' : ∀ f : ι → ℂ, ∑ χ ∈ B, starRingEnd ℂ (starRingEnd ℂ (f χ)) * starRingEnd ℂ (f χ) =
      ((∑ χ ∈ B, Complex.normSq (f χ) : ℝ) : ℂ) := fun f => by
    push_cast
    exact Finset.sum_congr rfl fun χ _ => by rw [Complex.conj_conj, Complex.mul_conj]
  have hcTU : ∑ χ ∈ B, starRingEnd ℂ (T χ) * U χ = 0 := by
    rw [sum_conj_mul_eq_conj, hTcU, map_zero]
  have hUcT : ∑ χ ∈ B, U χ * starRingEnd ℂ (T χ) = 0 := by
    rw [sum_mul_comm]
    exact hcTU
  have hcUT : ∑ χ ∈ B, starRingEnd ℂ (U χ) * T χ = 0 := by
    rw [sum_mul_comm, hTcU]
  have hTT' : ∑ χ ∈ B, T χ * T χ = 0 := by rw [hsq, hT2]
  have hUU' : ∑ χ ∈ B, U χ * U χ = 0 := by rw [hsq, hU2]
  have hAA' : ∑ χ ∈ B, A χ * A χ = 96 := by rw [hsq, hAA]
  have hBB' : ∑ χ ∈ B, Bv χ * Bv χ = 12 := by rw [hsq, hBB]
  have hUT : ∑ χ ∈ B, U χ * T χ = 0 := by rw [sum_mul_comm, hTU]
  have hBA : ∑ χ ∈ B, Bv χ * A χ = 0 := by rw [sum_mul_comm, hAB]
  have hAT : ∑ χ ∈ B, A χ * T χ = 0 := by rw [sum_mul_comm, hTA]
  have hAU : ∑ χ ∈ B, A χ * U χ = 0 := by rw [sum_mul_comm, hUA]
  have hBT : ∑ χ ∈ B, Bv χ * T χ = 0 := by rw [sum_mul_comm, hTB]
  have hBU : ∑ χ ∈ B, Bv χ * U χ = 0 := by rw [sum_mul_comm, hUB]
  have b11 := evalRow_gram_M B T U T U (by rw [hn, hTT]; norm_num) hcTU hcUT
    (by rw [hn, hUU]; norm_num)
  have b22 := evalRow_gram_M B A Bv A Bv (by rw [sum_conj_real_mul _ _ _ hA, hAA'])
    (by rw [sum_conj_real_mul _ _ _ hA, hBA]) (by rw [sum_conj_real_mul _ _ _ hB, hAB])
    (by rw [sum_conj_real_mul _ _ _ hB, hBB'])
  have b33 := evalRow_gram_M B (fun χ => starRingEnd ℂ (T χ)) (fun χ => starRingEnd ℂ (U χ))
    (fun χ => starRingEnd ℂ (T χ)) (fun χ => starRingEnd ℂ (U χ)) (by rw [hn', hTT]; norm_num)
    (by rw [sum_conj_conj_mul, hTcU]) (by rw [sum_conj_conj_mul, hUcT])
    (by rw [hn', hUU]; norm_num)
  have b12 := evalRow_gram_zero B T U A Bv (by rw [sum_conj_mul_real _ _ _ hA, hTA, map_zero])
    (by rw [sum_conj_mul_real _ _ _ hB, hTB, map_zero])
    (by rw [sum_conj_mul_real _ _ _ hA, hUA, map_zero])
    (by rw [sum_conj_mul_real _ _ _ hB, hUB, map_zero])
  have b21 := evalRow_gram_zero B A Bv T U (by rw [sum_conj_real_mul _ _ _ hA, hTA])
    (by rw [sum_conj_real_mul _ _ _ hA, hUA]) (by rw [sum_conj_real_mul _ _ _ hB, hTB])
    (by rw [sum_conj_real_mul _ _ _ hB, hUB])
  have b13 := evalRow_gram_zero B T U (fun χ => starRingEnd ℂ (T χ))
    (fun χ => starRingEnd ℂ (U χ)) (by rw [sum_conj_mul_conj, hTT', map_zero])
    (by rw [sum_conj_mul_conj, hTU, map_zero]) (by rw [sum_conj_mul_conj, hUT, map_zero])
    (by rw [sum_conj_mul_conj, hUU', map_zero])
  have b31 := evalRow_gram_zero B (fun χ => starRingEnd ℂ (T χ))
    (fun χ => starRingEnd ℂ (U χ)) T U (by rw [sum_conj_conj_mul, hTT'])
    (by rw [sum_conj_conj_mul, hTU]) (by rw [sum_conj_conj_mul, hUT])
    (by rw [sum_conj_conj_mul, hUU'])
  have b23 := evalRow_gram_zero B A Bv (fun χ => starRingEnd ℂ (T χ))
    (fun χ => starRingEnd ℂ (U χ)) (by rw [sum_conj_mul_conj, hAT, map_zero])
    (by rw [sum_conj_mul_conj, hAU, map_zero]) (by rw [sum_conj_mul_conj, hBT, map_zero])
    (by rw [sum_conj_mul_conj, hBU, map_zero])
  have b32 := evalRow_gram_zero B (fun χ => starRingEnd ℂ (T χ))
    (fun χ => starRingEnd ℂ (U χ)) A Bv (by rw [sum_conj_conj_mul, hTA])
    (by rw [sum_conj_conj_mul, hTB]) (by rw [sum_conj_conj_mul, hUA])
    (by rw [sum_conj_conj_mul, hUB])
  intro k hk h hh ℓ t
  rw [Finset.mem_Ico] at hk hh
  obtain ⟨hk1, hk4⟩ := hk
  obtain ⟨hh1, hh4⟩ := hh
  interval_cases k <;> interval_cases h <;> simp only [hrow1, hrow2, hrow3, ↓reduceIte,
    OfNat.ofNat_ne_one, Nat.succ_ne_self]
  · exact b11 ℓ t
  · exact b12 ℓ t
  · exact b13 ℓ t
  · exact b21 ℓ t
  · exact b22 ℓ t
  · exact b23 ℓ t
  · exact b31 ℓ t
  · exact b32 ℓ t
  · exact b33 ℓ t

end CFSG.Wreathed.FourPointCentralFourier
