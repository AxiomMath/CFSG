module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFrame

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG

variable {K : Type} [Field K] {d : ℕ}

theorem norm_smul (R : Matrix (Fin d) (Fin d) K) (r : K) (v : Fin d → K) :
    (r • v) ⬝ᵥ R *ᵥ (r • v) = r ^ 2 * (v ⬝ᵥ R *ᵥ v) := by
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

variable [Finite K]

theorem exists_slice_nf (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {A : Matrix (Fin d) (Fin d) K}
    (hAR : Aᵀ * (R : Matrix (Fin d) (Fin d) K) * A = R) (hA2 : A * A = 1)
    (hM2 : Module.finrank K (eigM A) = 2) (hP5 : 5 ≤ Module.finrank K (eigP A))
    (hPodd : Odd (Module.finrank K (eigP A))) :
    ∃ (hab : 2 + Module.finrank K (eigP A) = d)
      (c : Fin 2 ⊕ Fin (Module.finrank K (eigP A)) → Fin d → K),
      (∀ x, A *ᵥ c x = (if x.isLeft then (-1 : K) else 1) • c x) ∧
      (∀ x y, x ≠ y → c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c y = 0) ∧
      (∀ x, c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c x ≠ 0) ∧
      ∃ α β : K, α ≠ 0 ∧ β ≠ 0 ∧
        c (.inl 0) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inl 0) = α ∧
        c (.inl 1) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inl 1) = β ∧
        c (.inr ⟨0, by omega⟩) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inr ⟨0, by omega⟩) =
          -α ∧
        c (.inr ⟨1, by omega⟩) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inr ⟨1, by omega⟩) =
          -β ∧
        ∀ j : Fin (Module.finrank K (eigP A)), 2 ≤ (j : ℕ) →
          c (.inr j) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inr j) = -α := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set b := Module.finrank K (eigP A) with hb
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hab : 2 + b = d := by rw [← hM2]; exact finrank_eig_add h2 hA2
  set uM := Module.finBasisOfFinrankEq K (eigM A) hM2 with huM
  set uP := Module.finBasisOfFinrankEq K (eigP A) hb.symm with huP
  have hnP := nondeg_eig h2 hR hAR hA2 (Or.inl rfl)
  have hnM := nondeg_eig h2 hR hAR hA2 (Or.inr rfl)
  obtain ⟨c₁, -, -, -, hlast₁, s₁, hs₁, hdet₁⟩ := exists_frame_of_basis hK hR hnP uP
    (by omega) one_ne_zero
  set γ₁ := c₁ ⟨b - 1, by omega⟩ ⬝ᵥ Rm *ᵥ c₁ ⟨b - 1, by omega⟩ with hγ₁
  set β := -γ₁ with hβ
  have hβ0 : β ≠ 0 := neg_ne_zero.2 hlast₁
  obtain ⟨c₃, hc₃, horth₃, hval₃, hlast₃, -⟩ := exists_frame_of_basis hK hR hnM uM
    (le_refl 2) hβ0
  set α := c₃ ⟨2 - 1, by omega⟩ ⬝ᵥ Rm *ᵥ c₃ ⟨2 - 1, by omega⟩ with hα
  have hα0 : α ≠ 0 := hlast₃
  obtain ⟨c₂, hc₂, horth₂, hval₂, hlast₂, s₂, hs₂, hdet₂⟩ := exists_frame_of_basis hK hR hnP uP
    (by omega) (neg_ne_zero.2 hα0)
  set γ₂ := c₂ ⟨b - 1, by omega⟩ ⬝ᵥ Rm *ᵥ c₂ ⟨b - 1, by omega⟩ with hγ₂
  obtain ⟨k, hk⟩ := hPodd
  have hb1 : b - 1 = 2 * k := by omega
  have hαk : (-α) ^ k ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 hα0)
  set r := s₂ / (s₁ * (-α) ^ k) with hr
  have hr0 : r ≠ 0 := div_ne_zero hs₂ (mul_ne_zero hs₁ hαk)
  have hγ : γ₂ = -β * r ^ 2 := by
    have e1 : γ₁ = s₁ ^ 2 * (gramMat Rm uP).det := by
      rw [← hdet₁, one_pow, one_mul]
    have e2 : ((-α) ^ k) ^ 2 * γ₂ = s₂ ^ 2 * (gramMat Rm uP).det := by
      rw [← pow_mul, mul_comm k 2, ← hb1]
      exact hdet₂
    have hX2 : ((-α) ^ k) ^ 2 ≠ 0 := pow_ne_zero _ hαk
    have hs2 : s₁ ^ 2 ≠ 0 := pow_ne_zero _ hs₁
    have hγ₂' : γ₂ = s₂ ^ 2 * (gramMat Rm uP).det / ((-α) ^ k) ^ 2 := by
      rw [eq_div_iff hX2, mul_comm]
      exact e2
    rw [hβ, neg_neg, hr, e1, hγ₂', div_pow, mul_pow, mul_div_assoc',
      div_eq_div_iff hX2 (mul_ne_zero hs2 hX2)]
    ring
  set σ : Equiv.Perm (Fin b) := Equiv.swap ⟨1, by omega⟩ ⟨b - 1, by omega⟩ with hσ
  set cM : Fin 2 → Fin d → K := fun i => c₃ (Fin.rev i) with hcM
  set cP : Fin b → Fin d → K := fun j =>
    (if (j : ℕ) = 1 then r⁻¹ else 1) • c₂ (σ j) with hcP
  set c : Fin 2 ⊕ Fin b → Fin d → K := Sum.elim cM cP with hc
  have hnormP : ∀ j : Fin b, cP j ⬝ᵥ Rm *ᵥ cP j =
      (if (j : ℕ) = 1 then r⁻¹ else 1) ^ 2 * (c₂ (σ j) ⬝ᵥ Rm *ᵥ c₂ (σ j)) :=
    fun j => norm_smul _ _ _
  have hσ0 : σ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    rw [hσ, Equiv.swap_apply_of_ne_of_ne] <;> simp only [ne_eq, Fin.ext_iff] <;> omega
  have hσ1 : σ ⟨1, by omega⟩ = ⟨b - 1, by omega⟩ := by
    rw [hσ, Equiv.swap_apply_left]
  have hσj : ∀ j : Fin b, 2 ≤ (j : ℕ) → ((σ j : Fin b) : ℕ) + 1 < b := by
    intro j hj
    by_cases hjl : (j : ℕ) = b - 1
    · have : j = ⟨b - 1, by omega⟩ := Fin.ext hjl
      rw [this, hσ, Equiv.swap_apply_right]
      simp only
      omega
    · rw [hσ, Equiv.swap_apply_of_ne_of_ne]
      · have := j.2
        omega
      · intro h
        rw [Fin.ext_iff] at h
        simp only at h
        omega
      · intro h
        rw [Fin.ext_iff] at h
        exact hjl h
  refine ⟨hab, c, ?_, ?_, ?_, α, β, hα0, hβ0, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (i | j)
    · simp only [hc, Sum.elim_inl, Sum.isLeft_inl, ↓reduceIte, neg_smul, one_smul, hcM]
      exact mem_eigM.1 (hc₃ _)
    · simp only [hc, Sum.elim_inr, Sum.isLeft_inr, Bool.false_eq_true, ↓reduceIte, one_smul,
        hcP]
      rw [mulVec_smul, mem_eigP.1 (hc₂ _)]
  · rintro (i | j) (i' | j') hxy
    · simp only [hc, Sum.elim_inl, hcM]
      exact horth₃ _ _ fun h => hxy (by rw [Fin.rev_injective h])
    · simp only [hc, Sum.elim_inl, Sum.elim_inr]
      rw [dot_symm hR]
      exact orth_eig h2 hAR (Submodule.smul_mem _ _ (hc₂ _)) (hc₃ _)
    · simp only [hc, Sum.elim_inl, Sum.elim_inr]
      exact orth_eig h2 hAR (Submodule.smul_mem _ _ (hc₂ _)) (hc₃ _)
    · simp only [hc, Sum.elim_inr, hcP]
      rw [mulVec_smul, dotProduct_smul, smul_dotProduct,
        horth₂ _ _ fun h => hxy (by rw [σ.injective h]), smul_zero, smul_zero]
  · have hval3 : c₃ 0 ⬝ᵥ Rm *ᵥ c₃ 0 = β := hval₃ 0 (by simp)
    rintro (i | j)
    · simp only [hc, Sum.elim_inl, hcM]
      fin_cases i
      · exact hα0
      · have e : Fin.rev (⟨1, by omega⟩ : Fin 2) = 0 := rfl
        simp only [Fin.mk_one] at e ⊢
        rw [e, hval3]
        exact hβ0
    · simp only [hc, Sum.elim_inr]
      rw [hnormP]
      refine mul_ne_zero (pow_ne_zero _ (by split_ifs <;> simp [hr0])) ?_
      by_cases hl : ((σ j : Fin b) : ℕ) + 1 < b
      · rw [hval₂ _ hl]
        exact neg_ne_zero.2 hα0
      · have : σ j = ⟨b - 1, by omega⟩ := Fin.ext (by have := (σ j).2; simp only; omega)
        rw [this]
        exact hlast₂
  · rfl
  · simp only [hc, Sum.elim_inl, hcM, Fin.isValue]
    exact hval₃ 0 (by simp)
  · simp only [hc, Sum.elim_inr]
    rw [hnormP, hσ0, hval₂ _ (by simp only; omega)]
    simp
  · simp only [hc, Sum.elim_inr]
    rw [hnormP, hσ1]
    simp only [↓reduceIte]
    change r⁻¹ ^ 2 * γ₂ = -β
    rw [hγ]
    field_simp
  · intro j hj
    simp only [hc, Sum.elim_inr]
    rw [hnormP, hval₂ _ (hσj j hj)]
    have : (j : ℕ) ≠ 1 := by omega
    simp [this]

end CFSG.ComponentClassification.Burgoyne.O
