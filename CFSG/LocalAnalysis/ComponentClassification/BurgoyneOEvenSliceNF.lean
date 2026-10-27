module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceNF

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG

variable {K : Type} [Field K] {d : ℕ}

theorem dot_comb {R : Matrix (Fin d) (Fin d) K} (hR : Rᵀ = R) {f g : Fin d → K}
    (hfg : f ⬝ᵥ R *ᵥ g = 0) (s t s' t' : K) :
    (s • f + t • g) ⬝ᵥ R *ᵥ (s' • f + t' • g) =
      s * s' * (f ⬝ᵥ R *ᵥ f) + t * t' * (g ⬝ᵥ R *ᵥ g) := by
  have hgf : g ⬝ᵥ R *ᵥ f = 0 := by rw [dot_symm hR]; exact hfg
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hfg, hgf]
  ring

theorem dot_comb_right {R : Matrix (Fin d) (Fin d) K} {f g z : Fin d → K}
    (hf : z ⬝ᵥ R *ᵥ f = 0) (hg : z ⬝ᵥ R *ᵥ g = 0) (s t : K) :
    z ⬝ᵥ R *ᵥ (s • f + t • g) = 0 := by
  simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hf, hg,
    mul_zero, add_zero]

variable [Finite K]

theorem exists_slice_nf_gen (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {A : Matrix (Fin d) (Fin d) K}
    (hAR : Aᵀ * (R : Matrix (Fin d) (Fin d) K) * A = R) (hA2 : A * A = 1)
    (hM2 : Module.finrank K (eigM A) = 2) (hP5 : 5 ≤ Module.finrank K (eigP A)) :
    ∃ (hab : 2 + Module.finrank K (eigP A) = d)
      (c : Fin 2 ⊕ Fin (Module.finrank K (eigP A)) → Fin d → K),
      (∀ x, A *ᵥ c x = (if x.isLeft then (-1 : K) else 1) • c x) ∧
      (∀ x y, x ≠ y → c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c y = 0) ∧
      (∀ x, c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c x ≠ 0) ∧
      ∃ β γ : K, β ≠ 0 ∧ γ ≠ 0 ∧ (β = 1 ∨ ¬ IsSquare β) ∧ (γ = -β ∨ ¬ IsSquare (γ / -β)) ∧
        c (.inl 0) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inl 0) = 1 ∧
        c (.inl 1) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inl 1) = β ∧
        c (.inr ⟨0, by omega⟩) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inr ⟨0, by omega⟩) =
          -1 ∧
        (∀ j : Fin (Module.finrank K (eigP A)), 1 ≤ (j : ℕ) →
          (j : ℕ) + 1 < Module.finrank K (eigP A) →
          c (.inr j) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c (.inr j) = -β) ∧
        c (.inr ⟨Module.finrank K (eigP A) - 1, by omega⟩) ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ
          c (.inr ⟨Module.finrank K (eigP A) - 1, by omega⟩) = γ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  have hodd : Fintype.card K % 2 = 1 := by
    have := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
    rw [Nat.card_eq_fintype_card] at this
    exact Nat.odd_iff.1 this
  set b := Module.finrank K (eigP A) with hb
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hab : 2 + b = d := by rw [← hM2]; exact finrank_eig_add h2 hA2
  set uM := Module.finBasisOfFinrankEq K (eigM A) hM2 with huM
  set uP := Module.finBasisOfFinrankEq K (eigP A) hb.symm with huP
  have hnP := nondeg_eig h2 hR hAR hA2 (Or.inl rfl)
  have hnM := nondeg_eig h2 hR hAR hA2 (Or.inr rfl)
  obtain ⟨c₁, hc₁, horth₁, hval₁, hlast₁, -⟩ := exists_frame_of_basis hK hR hnM uM
    (le_refl 2) one_ne_zero
  set β₁ := c₁ ⟨2 - 1, by omega⟩ ⬝ᵥ Rm *ᵥ c₁ ⟨2 - 1, by omega⟩ with hβ₁
  have hv0 : c₁ 0 ⬝ᵥ Rm *ᵥ c₁ 0 = 1 := hval₁ 0 (by simp)
  obtain ⟨β, r₁, hβ0, hr₁, hβ1, hβr⟩ : ∃ β r₁ : K, β ≠ 0 ∧ r₁ ≠ 0 ∧ (β = 1 ∨ ¬ IsSquare β) ∧
      r₁ ^ 2 * β₁ = β := by
    by_cases hsq : IsSquare β₁
    · obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hs
        exact hlast₁ hs
      exact ⟨1, s⁻¹, one_ne_zero, inv_ne_zero hs0, Or.inl rfl, by rw [hs]; field_simp⟩
    · exact ⟨β₁, 1, hlast₁, one_ne_zero, Or.inr hsq, by ring⟩
  set cM : Fin 2 → Fin d → K := fun i => if (i : ℕ) = 0 then c₁ 0 else r₁ • c₁ 1 with hcM
  obtain ⟨c₂, hc₂, horth₂, hval₂, hlast₂, -⟩ := exists_frame_of_basis hK hR hnP uP
    (by omega) (neg_ne_zero.2 hβ0)
  set i₀ : Fin b := ⟨0, by omega⟩ with hi₀
  set iL : Fin b := ⟨b - 1, by omega⟩ with hiL
  have hi0L : i₀ ≠ iL := by simp [hi₀, hiL, Fin.ext_iff]; omega
  set γ₀ := c₂ iL ⬝ᵥ Rm *ᵥ c₂ iL with hγ₀
  have hf0 : c₂ i₀ ⬝ᵥ Rm *ᵥ c₂ i₀ = -β := hval₂ i₀ (by simp [hi₀]; omega)
  obtain ⟨s, t, hst⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hodd
    (neg_ne_zero.2 hβ0) hlast₂ (-1)
  set u := s • c₂ i₀ + t • c₂ iL with hu
  set w₁ := (t * γ₀) • c₂ i₀ + (s * β) • c₂ iL with hw₁
  have h0L := horth₂ i₀ iL hi0L
  have hQu : u ⬝ᵥ Rm *ᵥ u = -1 := by
    rw [hu, dot_comb hR h0L, hf0, ← hγ₀]
    linear_combination hst
  have hQw₁ : w₁ ⬝ᵥ Rm *ᵥ w₁ = β * γ₀ := by
    rw [hw₁, dot_comb hR h0L, hf0, ← hγ₀]
    linear_combination (-(β * γ₀)) * hst
  have huw₁ : u ⬝ᵥ Rm *ᵥ w₁ = 0 := by
    rw [hu, hw₁, dot_comb hR h0L, hf0, ← hγ₀]
    ring
  have hγ₁0 : β * γ₀ ≠ 0 := mul_ne_zero hβ0 hlast₂
  obtain ⟨γ, r₂, hγ0, hr₂, hγ1, hγr⟩ : ∃ γ r₂ : K, γ ≠ 0 ∧ r₂ ≠ 0 ∧
      (γ = -β ∨ ¬ IsSquare (γ / -β)) ∧ r₂ ^ 2 * (β * γ₀) = γ := by
    by_cases hsq : IsSquare (β * γ₀ / -β)
    · obtain ⟨s', hs'⟩ := hsq
      have hs0 : s' ≠ 0 := by
        rintro rfl
        rw [mul_zero, div_eq_zero_iff] at hs'
        rcases hs' with h | h
        · exact hγ₁0 h
        · exact neg_ne_zero.2 hβ0 h
      refine ⟨-β, s'⁻¹, neg_ne_zero.2 hβ0, inv_ne_zero hs0, Or.inl rfl, ?_⟩
      have e : β * γ₀ = s' * s' * -β := by rw [← hs']; field_simp
      rw [e]
      field_simp
    · exact ⟨β * γ₀, 1, hγ₁0, one_ne_zero, Or.inr hsq, by ring⟩
  set cP : Fin b → Fin d → K := fun j =>
    if j = i₀ then u else if j = iL then r₂ • w₁ else c₂ j with hcP
  set c : Fin 2 ⊕ Fin b → Fin d → K := Sum.elim cM cP with hc
  have huP : u ∈ eigP A := add_mem (Submodule.smul_mem _ _ (hc₂ _)) (Submodule.smul_mem _ _ (hc₂ _))
  have hwP : w₁ ∈ eigP A :=
    add_mem (Submodule.smul_mem _ _ (hc₂ _)) (Submodule.smul_mem _ _ (hc₂ _))
  have hcPmem : ∀ j, cP j ∈ eigP A := by
    intro j
    simp only [hcP]
    split_ifs
    · exact huP
    · exact Submodule.smul_mem _ _ hwP
    · exact hc₂ j
  have hcMmem : ∀ i, cM i ∈ eigM A := by
    intro i
    simp only [hcM]
    split_ifs
    · exact hc₁ 0
    · exact Submodule.smul_mem _ _ (hc₁ 1)
  have hothers : ∀ j, j ≠ i₀ → j ≠ iL → u ⬝ᵥ Rm *ᵥ c₂ j = 0 ∧ w₁ ⬝ᵥ Rm *ᵥ c₂ j = 0 := by
    intro j hj0 hjL
    refine ⟨?_, ?_⟩
    · rw [dot_symm hR]
      exact dot_comb_right (horth₂ j i₀ hj0) (horth₂ j iL hjL) s t
    · rw [dot_symm hR]
      exact dot_comb_right (horth₂ j i₀ hj0) (horth₂ j iL hjL) _ _
  have horthP : ∀ j k, j ≠ k → cP j ⬝ᵥ Rm *ᵥ cP k = 0 := by
    intro j k hjk
    simp only [hcP]
    by_cases hj0 : j = i₀
    · subst hj0
      by_cases hkL : k = iL
      · subst hkL
        simp only [↓reduceIte, Ne.symm hi0L]
        rw [mulVec_smul, dotProduct_smul, huw₁, smul_zero]
      · simp only [↓reduceIte, Ne.symm hjk, hkL]
        exact (hothers k (Ne.symm hjk) hkL).1
    by_cases hjL : j = iL
    · subst hjL
      by_cases hk0 : k = i₀
      · subst hk0
        simp only [↓reduceIte, Ne.symm hi0L]
        rw [smul_dotProduct, dot_symm hR, huw₁, smul_zero]
      · simp only [↓reduceIte, hj0, hk0, Ne.symm hjk]
        rw [smul_dotProduct, (hothers k hk0 (Ne.symm hjk)).2, smul_zero]
    simp only [hj0, hjL, ↓reduceIte]
    by_cases hk0 : k = i₀
    · subst hk0
      simp only [↓reduceIte]
      rw [dot_symm hR]
      exact (hothers j hj0 hjL).1
    by_cases hkL : k = iL
    · subst hkL
      simp only [hk0, ↓reduceIte]
      rw [mulVec_smul, dotProduct_smul, dot_symm hR, (hothers j hj0 hjL).2, smul_zero]
    simp only [hk0, hkL, ↓reduceIte]
    exact horth₂ j k hjk
  have hnormP : ∀ j, cP j ⬝ᵥ Rm *ᵥ cP j =
      if j = i₀ then -1 else if j = iL then γ else c₂ j ⬝ᵥ Rm *ᵥ c₂ j := by
    intro j
    simp only [hcP]
    split_ifs with h0 hL
    · exact hQu
    · rw [norm_smul, hQw₁, hγr]
    · rfl
  have hnormM : ∀ i, cM i ⬝ᵥ Rm *ᵥ cM i = if (i : ℕ) = 0 then 1 else β := by
    intro i
    simp only [hcM]
    split_ifs
    · exact hv0
    · rw [norm_smul]
      have : c₁ 1 = c₁ ⟨2 - 1, by omega⟩ := rfl
      rw [this, ← hβ₁, hβr]
  refine ⟨hab, c, ?_, ?_, ?_, β, γ, hβ0, hγ0, hβ1, hγ1, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (i | j)
    · simp only [hc, Sum.elim_inl, Sum.isLeft_inl, ↓reduceIte, neg_smul, one_smul]
      exact mem_eigM.1 (hcMmem i)
    · simp only [hc, Sum.elim_inr, Sum.isLeft_inr, Bool.false_eq_true, ↓reduceIte, one_smul]
      exact mem_eigP.1 (hcPmem j)
  · rintro (i | j) (i' | j') hxy
    · simp only [hc, Sum.elim_inl]
      have hii : i ≠ i' := fun h => hxy (by rw [h])
      simp only [hcM]
      fin_cases i <;> fin_cases i' <;> simp at hii <;> simp only [Fin.isValue,
        ↓reduceIte, one_ne_zero, mulVec_smul, dotProduct_smul, smul_dotProduct] <;>
        simp [horth₁ 0 1 (by decide), horth₁ 1 0 (by decide)]
    · simp only [hc, Sum.elim_inl, Sum.elim_inr]
      rw [dot_symm hR]
      exact orth_eig h2 hAR (hcPmem j') (hcMmem i)
    · simp only [hc, Sum.elim_inl, Sum.elim_inr]
      exact orth_eig h2 hAR (hcPmem j) (hcMmem i')
    · exact horthP j j' fun h => hxy (by rw [h])
  · rintro (i | j)
    · simp only [hc, Sum.elim_inl]
      rw [hnormM]
      split_ifs
      · exact one_ne_zero
      · exact hβ0
    · simp only [hc, Sum.elim_inr]
      rw [hnormP]
      split_ifs with h0 hL
      · exact neg_ne_zero.2 one_ne_zero
      · exact hγ0
      · by_cases hj : (j : ℕ) + 1 < b
        · rw [hval₂ j hj]
          exact neg_ne_zero.2 hβ0
        · have : j = iL := Fin.ext (by simp [hiL]; omega)
          exact absurd this hL
  · simp only [hc, Sum.elim_inl]
    rw [hnormM]
    simp
  · simp only [hc, Sum.elim_inl]
    rw [hnormM]
    simp
  · simp only [hc, Sum.elim_inr]
    rw [hnormP]
    simp [hi₀]
  · intro j hj1 hjL
    simp only [hc, Sum.elim_inr]
    rw [hnormP]
    have h0 : j ≠ i₀ := fun h => by rw [h] at hj1; simp [hi₀] at hj1
    have hL : j ≠ iL := fun h => by rw [h] at hjL; simp [hiL] at hjL; omega
    simp only [h0, hL, ↓reduceIte]
    exact hval₂ j hjL
  · simp only [hc, Sum.elim_inr]
    rw [hnormP]
    have : (⟨b - 1, by omega⟩ : Fin b) = iL := rfl
    rw [this]
    simp [Ne.symm hi0L]

end CFSG.ComponentClassification.Burgoyne.O
