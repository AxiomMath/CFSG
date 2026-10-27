module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def IsEig (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (u : Fin n → K) : Prop :=
  ∀ T ∈ 𝒯, ∃ l : K, T *ᵥ u = l • u

@[expose] def EigSep (σ : K ≃+* K) (T : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ (u u' : Fin n → K) (l l' : K), u ≠ 0 → u' ≠ 0 → T *ᵥ u = l • u → T *ᵥ u' = l' • u' →
    σ l * l' = 1 → l = l'

theorem herm_mulVec_isometry {A : Matrix (Fin n) (Fin n) K} (hA : conjTr σ A * A = 1)
    (x y : Fin n → K) : herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y := by
  rw [herm_mulVec, hA, one_mulVec]

section Eig

variable {𝒯 : Set (Matrix (Fin n) (Fin n) K)}

theorem isEig_smul {u : Fin n → K} (hu : IsEig 𝒯 u) (c : K) : IsEig 𝒯 (c • u) := by
  intro T hT
  obtain ⟨l, hl⟩ := hu T hT
  exact ⟨l, by rw [mulVec_smul, hl, smul_comm]⟩

theorem isEig_add_smul {u u' : Fin n → K}
    (hC : ∀ T ∈ 𝒯, ∃ l : K, T *ᵥ u = l • u ∧ T *ᵥ u' = l • u') (c : K) :
    IsEig 𝒯 (u + c • u') := by
  intro T hT
  obtain ⟨l, h1, h2⟩ := hC T hT
  exact ⟨l, by rw [mulVec_add, mulVec_smul, h1, h2, smul_add, smul_comm]⟩

theorem common_eigen_of_herm_ne_zero (hiso : ∀ T ∈ 𝒯, conjTr σ T * T = 1)
    (hsep : ∀ T ∈ 𝒯, EigSep σ T) {u u' : Fin n → K} (hu : IsEig 𝒯 u) (hu' : IsEig 𝒯 u')
    (h : herm σ u u' ≠ 0) : ∀ T ∈ 𝒯, ∃ l : K, T *ᵥ u = l • u ∧ T *ᵥ u' = l • u' := by
  intro T hT
  obtain ⟨l, hl⟩ := hu T hT
  obtain ⟨l', hl'⟩ := hu' T hT
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact h (herm_zero_left σ _)
  have hu0' : u' ≠ 0 := by
    rintro rfl
    exact h (herm_zero_right σ _)
  have h1 := herm_mulVec_isometry (hiso T hT) u u'
  rw [hl, hl', herm_smul_left, herm_smul_right, ← mul_assoc] at h1
  have h2 : σ l * l' = 1 := mul_right_cancel₀ h (h1.trans (one_mul _).symm)
  have h3 := hsep T hT u u' l l' hu0 hu0' hl hl' h2
  exact ⟨l, hl, h3 ▸ hl'⟩

theorem herm_eq_zero_of_pair (hσ : IsUnitaryInvolution σ) {a b : Fin n → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (h1 : herm σ (a + b) (a + b) = 0) {c : K}
    (hc : σ c ≠ c) (h2 : herm σ (a + c • b) (a + c • b) = 0) : herm σ a b = 0 := by
  have hab := herm_conj σ hσ.invol a b
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb] at h1 h2
  rw [hab] at h1 h2
  have h3 : (c - σ c) * herm σ a b = 0 := by linear_combination h2 - σ c * h1
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

variable {k : ℕ} {s : Fin k → Fin n → K}

theorem isEig_proj (hiso : ∀ T ∈ 𝒯, conjTr σ T * T = 1) (hsep : ∀ T ∈ 𝒯, EigSep σ T)
    (hs : ∀ j, IsEig 𝒯 (s j)) {w : Fin n → K} (hw : IsEig 𝒯 w) :
    IsEig 𝒯 (w - ∑ j, herm σ (s j) w • s j) := by
  intro T hT
  obtain ⟨l, hl⟩ := hw T hT
  refine ⟨l, ?_⟩
  have key : ∀ j, herm σ (s j) w • (T *ᵥ s j) = herm σ (s j) w • (l • s j) := by
    intro j
    by_cases hj : herm σ (s j) w = 0
    · rw [hj, zero_smul, zero_smul]
    · obtain ⟨l', h1, h2⟩ := common_eigen_of_herm_ne_zero hiso hsep (hs j) hw hj T hT
      have hw0 : w ≠ 0 := by
        rintro rfl
        exact hj (herm_zero_right σ _)
      have : l' = l := by
        have h3 : l' • w = l • w := h2.symm.trans hl
        exact smul_left_injective K hw0 h3
      rw [h1, this]
  rw [mulVec_sub, hl, mulVec_sum]
  simp only [mulVec_smul, key, smul_sub, Finset.smul_sum, smul_comm l]

theorem exists_eig_norm_one_perp (hσ : IsUnitaryInvolution σ)
    (hiso : ∀ T ∈ 𝒯, conjTr σ T * T = 1) (hsep : ∀ T ∈ 𝒯, EigSep σ T)
    {S : Set (Fin n → K)} (hS : Submodule.span K S = ⊤) (hSe : ∀ w ∈ S, IsEig 𝒯 w)
    (hk : k < n) (hs : ∀ i j, herm σ (s i) (s j) = if i = j then 1 else 0)
    (hse : ∀ j, IsEig 𝒯 (s j)) :
    ∃ x, IsEig 𝒯 x ∧ (∀ j, herm σ (s j) x = 0) ∧ herm σ x x = 1 := by
  by_contra hne
  push Not at hne
  have hall : ∀ z, IsEig 𝒯 z → (∀ j, herm σ (s j) z = 0) → herm σ z z = 0 := by
    intro z hz hzs
    by_contra hz0
    obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hz0
    exact hne (c • z) (isEig_smul hz c) (fun j => by rw [herm_smul_right, hzs j, mul_zero]) hc
  set P : (Fin n → K) →ₗ[K] (Fin n → K) :=
    LinearMap.id - ∑ j, (hermL σ (s j)).smulRight (s j) with hPdef
  have hPy : ∀ y, P y = y - ∑ j, herm σ (s j) y • s j := by
    intro y
    simp [hPdef]
  have hPs : ∀ y j, herm σ (s j) (P y) = 0 := by
    intro y j
    rw [hPy, herm_sub_right]
    have : herm σ (s j) (∑ i, herm σ (s i) y • s i) = herm σ (s j) y := by
      have := map_sum (hermL σ (s j)) (fun i => herm σ (s i) y • s i) Finset.univ
      simp only [hermL_apply, map_smul, smul_eq_mul, hs] at this
      rw [this]
      simp [mul_ite]
    rw [this, sub_self]
  have hPe : ∀ w ∈ S, IsEig 𝒯 (P w) := fun w hw => by
    rw [hPy]
    exact isEig_proj hiso hsep hse (hSe w hw)
  have hpair : ∀ w ∈ S, ∀ w' ∈ S, herm σ (P w) (P w') = 0 := by
    intro w hw w' hw'
    by_contra hne0
    have hC := common_eigen_of_herm_ne_zero hiso hsep (hPe w hw) (hPe w' hw') hne0
    obtain ⟨c, hc⟩ := hσ.exists_ne
    have e1 : herm σ (P w + (1 : K) • P w') (P w + (1 : K) • P w') = 0 :=
      hall _ (isEig_add_smul hC 1) (fun j => by
        rw [herm_add_right, herm_smul_right, hPs, hPs, mul_zero, add_zero])
    have e2 : herm σ (P w + c • P w') (P w + c • P w') = 0 :=
      hall _ (isEig_add_smul hC c) (fun j => by
        rw [herm_add_right, herm_smul_right, hPs, hPs, mul_zero, add_zero])
    rw [one_smul] at e1
    exact hne0 (herm_eq_zero_of_pair hσ (hall _ (hPe w hw) (hPs w))
      (hall _ (hPe w' hw') (hPs w')) e1 hc e2)
  have hall2 : ∀ y y', herm σ (P y) (P y') = 0 := by
    intro y y'
    have hy : y ∈ Submodule.span K S := by rw [hS]; trivial
    have hy' : y' ∈ Submodule.span K S := by rw [hS]; trivial
    have step : ∀ w' ∈ S, ∀ y ∈ Submodule.span K S, herm σ (P y) (P w') = 0 := by
      intro w' hw' y hy
      induction hy using Submodule.span_induction with
      | mem w hw => exact hpair w hw w' hw'
      | zero => rw [map_zero, herm_zero_left]
      | add a b _ _ h1 h2 => rw [map_add, herm_add_left, h1, h2, add_zero]
      | smul c a _ h1 => rw [map_smul, herm_smul_left, h1, mul_zero]
    induction hy' using Submodule.span_induction with
    | mem w hw => exact step w hw y hy
    | zero => rw [map_zero, herm_zero_right]
    | add a b _ _ h1 h2 => rw [map_add, herm_add_right, h1, h2, add_zero]
    | smul c a _ h1 => rw [map_smul, herm_smul_right, h1, mul_zero]
  obtain ⟨y, hy⟩ := exists_aniso_of_lt hσ hk s P
    (fun y => by
      rw [hPy, sub_sub_cancel]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    hPs
  exact hy (hall2 y y)

theorem exists_orthonormal_eig_family (hσ : IsUnitaryInvolution σ)
    (hiso : ∀ T ∈ 𝒯, conjTr σ T * T = 1) (hsep : ∀ T ∈ 𝒯, EigSep σ T)
    {S : Set (Fin n → K)} (hS : Submodule.span K S = ⊤) (hSe : ∀ w ∈ S, IsEig 𝒯 w) :
    ∀ k ≤ n, ∃ s : Fin k → Fin n → K,
      (∀ i j, herm σ (s i) (s j) = if i = j then 1 else 0) ∧ ∀ j, IsEig 𝒯 (s j) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, fun i => Fin.elim0 i, fun j => Fin.elim0 j⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hb, hbe⟩ := ih (by omega)
    obtain ⟨x, hxe, hxb, hxx⟩ := exists_eig_norm_one_perp hσ hiso hsep hS hSe (by omega) hb hbe
    refine ⟨Fin.snoc b x, fun i j => ?_, fun j => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [hxx]
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          rw [herm_conj σ hσ.invol, hxb j, map_zero,
            ite_eq_right_iff.mpr fun h => absurd h (Fin.castSucc_lt_last j).ne']
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          rw [hxb i, ite_eq_right_iff.mpr fun h => absurd h (Fin.castSucc_lt_last i).ne]
        | cast j => simp only [Fin.snoc_castSucc, hb i j, Fin.castSucc_inj]
    · induction j using Fin.lastCases with
      | last => simpa using hxe
      | cast j => simpa using hbe j

end Eig

theorem exists_unitary_eig_matrix (hσ : IsUnitaryInvolution σ)
    {𝒯 : Set (Matrix (Fin n) (Fin n) K)} (hiso : ∀ T ∈ 𝒯, conjTr σ T * T = 1)
    (hsep : ∀ T ∈ 𝒯, EigSep σ T) {S : Set (Fin n → K)} (hS : Submodule.span K S = ⊤)
    (hSe : ∀ w ∈ S, IsEig 𝒯 w) :
    ∃ M : Matrix (Fin n) (Fin n) K, conjTr σ M * M = 1 ∧
      ∀ T ∈ 𝒯, ∃ D : Fin n → K, T * M = M * Matrix.diagonal D := by
  obtain ⟨s, hs, hse⟩ := exists_orthonormal_eig_family hσ hiso hsep hS hSe n le_rfl
  refine ⟨Matrix.of fun i j => s j i, ?_, ?_⟩
  · ext i j
    have := hs i j
    rw [herm_def] at this
    simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
      this]
    rw [Matrix.one_apply]
  · intro T hT
    choose l hl using fun j => hse j T hT
    refine ⟨l, ?_⟩
    ext i j
    have := congrFun (hl j) i
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU
