module

public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix

public section

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.AGLEmbedding.LeviBlock

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section Antidiag

variable {F : Type} [Field F] {n : ℕ}

theorem mul_antidiag_apply (M : Matrix (Fin n) (Fin n) F) (x y : Fin n) :
    (M * (antidiag n : Matrix (Fin n) (Fin n) F)) x y = M x (Fin.rev y) := by
  simp only [mul_apply, antidiag, of_apply]
  rw [Finset.sum_eq_single (Fin.rev y)]
  · simp
  · intro t _ ht
    have : y ≠ Fin.rev t := fun e => ht (by rw [e, Fin.rev_rev])
    simp [this]
  · simp

theorem antidiag_mul_apply (M : Matrix (Fin n) (Fin n) F) (x y : Fin n) :
    ((antidiag n : Matrix (Fin n) (Fin n) F) * M) x y = M (Fin.rev x) y := by
  simp only [mul_apply, antidiag, of_apply]
  rw [Finset.sum_eq_single (Fin.rev x)]
  · simp
  · intro t _ ht
    have : t ≠ Fin.rev x := ht
    simp [this]
  · simp

end Antidiag


section Extend

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {τ : ι → Fin n} (hτ : Function.Injective τ)

theorem conjTr_extendMat (B : Matrix ι ι F) :
    conjTr σ (extendMat hτ B) = extendMat hτ ((B.map σ)ᵀ) := by
  unfold conjTr
  rw [← extendMat_transpose hτ]
  exact congrArg Matrix.transpose (extendMat_map hτ σ.toRingHom B)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_range_rev_iff {r : ι → ι} (hr : ∀ i, τ (r i) = Fin.rev (τ i)) (x : Fin n) :
    Fin.rev x ∈ Set.range τ ↔ x ∈ Set.range τ := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨r i, by rw [hr, hi, Fin.rev_rev]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨r i, hr i⟩

theorem extendMat_mul_antidiag {r : ι → ι} (hr : ∀ i, τ (r i) = Fin.rev (τ i))
    (A : Matrix ι ι F) :
    extendMat hτ A * (antidiag n : Matrix (Fin n) (Fin n) F) =
      (antidiag n : Matrix (Fin n) (Fin n) F) * extendMat hτ (A.submatrix r r) := by
  ext x y
  rw [mul_antidiag_apply, antidiag_mul_apply]
  have hrr : ∀ i, r (r i) = i := fun i => hτ (by rw [hr, hr, Fin.rev_rev])
  have hiff : (x = Fin.rev y) ↔ (Fin.rev x = y) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
  by_cases hx : x ∈ Set.range τ
  · by_cases hy : Fin.rev y ∈ Set.range τ
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, hj⟩ := hy
      have hy' : y = τ (r j) := by rw [hr, hj, Fin.rev_rev]
      rw [← hj, ← hr i, hy', extendMat_apply_map, extendMat_apply_map, Matrix.submatrix_apply,
        hrr, hrr]
    · have hy2 : y ∉ Set.range τ := fun h => hy ((mem_range_rev_iff hr y).2 h)
      rw [extendMat_apply_of_not_mem hτ A (Or.inr hy),
        extendMat_apply_of_not_mem hτ _ (Or.inr hy2)]
      simp only [Matrix.one_apply, hiff]
  · have hx2 : Fin.rev x ∉ Set.range τ := fun h => hx ((mem_range_rev_iff hr x).1 h)
    rw [extendMat_apply_of_not_mem hτ A (Or.inl hx),
      extendMat_apply_of_not_mem hτ _ (Or.inl hx2)]
    simp only [Matrix.one_apply, hiff]

end Extend


section SUEmb

variable {F : Type} [Field F] {σ : F ≃+* F} {n' n : ℕ} {τ : Fin n' → Fin n}
  (hτ : Function.Injective τ) (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i))

theorem antidiag_mul_self : (antidiag n : Matrix (Fin n) (Fin n) F) * antidiag n = 1 := by
  ext x y
  rw [antidiag_mul_apply]
  simp [antidiag, Matrix.one_apply, Fin.rev_eq_iff, eq_comm]

theorem antidiag_conj (M : Matrix (Fin n) (Fin n) F) :
    (antidiag n : Matrix (Fin n) (Fin n) F) * M * antidiag n = M.submatrix Fin.rev Fin.rev := by
  ext x y
  rw [mul_antidiag_apply, antidiag_mul_apply]
  rfl

include hr in
theorem extendMat_unitary {M : Matrix (Fin n') (Fin n') F}
    (hM : conjTr σ M * antidiag n' * M = antidiag n') :
    conjTr σ (extendMat hτ M) * antidiag n * extendMat hτ M = antidiag n := by
  have hrr : ∀ i : Fin n', Fin.rev (Fin.rev i) = i := Fin.rev_rev
  have h1 : (antidiag n : Matrix (Fin n) (Fin n) F) * extendMat hτ M =
      extendMat hτ (M.submatrix Fin.rev Fin.rev) * antidiag n := by
    have := extendMat_mul_antidiag hτ hr (M.submatrix Fin.rev Fin.rev)
    rw [Matrix.submatrix_submatrix] at this
    simp only [Function.comp_def, Fin.rev_rev] at this
    exact this.symm
  have h2 : conjTr σ M * M.submatrix Fin.rev Fin.rev = 1 := by
    rw [← antidiag_conj M, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, antidiag_mul_self]
  rw [conjTr_extendMat hτ M, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, ← extendMat_mul]
  have : ((M.map σ)ᵀ) * M.submatrix Fin.rev Fin.rev = 1 := h2
  rw [this, extendMat_one, Matrix.one_mul]


variable (σ)

@[expose] noncomputable def extendHom : Matrix (Fin n') (Fin n') F →* Matrix (Fin n) (Fin n) F where
  toFun := extendMat hτ
  map_one' := extendMat_one hτ
  map_mul' := extendMat_mul hτ

include hr in
@[expose] noncomputable def suEmbed : SU σ n' →* SU σ n :=
  ((extendHom hτ).comp (mat σ n')).toHomUnits.codRestrict (SU σ n) (fun M => by
    refine ⟨?_, ?_⟩
    · show ((extendHom hτ).comp (mat σ n') M).det = 1
      simp only [MonoidHom.comp_apply, extendHom, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [det_extendMat]
      exact M.2.1
    · show conjTr σ ((extendHom hτ).comp (mat σ n') M) * antidiag n *
        ((extendHom hτ).comp (mat σ n') M) = antidiag n
      simp only [MonoidHom.comp_apply, extendHom, MonoidHom.coe_mk, OneHom.coe_mk]
      exact extendMat_unitary hτ hr M.2.2)

include hr in
theorem mat_suEmbed (M : SU σ n') : mat σ n (suEmbed σ hτ hr M) = extendMat hτ (mat σ n' M) := rfl

include hr in
theorem suEmbed_injective : Function.Injective (suEmbed σ hτ hr) := by
  intro M M' h
  apply mat_injective
  have := congrArg (mat σ n) h
  rw [mat_suEmbed, mat_suEmbed] at this
  have h2 := congrArg (fun A => A.submatrix τ τ) this
  simp only [submatrix_extendMat] at h2
  exact h2

end SUEmb


section ExtSingle

variable {F : Type} [Field F] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {φ : ι → Fin n} (hφ : Function.Injective φ)

theorem extendMat_one_add_single (a b : ι) (c : F) :
    extendMat hφ (1 + Matrix.single a b c) = 1 + Matrix.single (φ a) (φ b) c := by
  ext x y
  by_cases hxy : x ∈ Set.range φ ∧ y ∈ Set.range φ
  · obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hxy
    rw [extendMat_apply_map]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hφ.eq_iff]
  · have h : x ∉ Set.range φ ∨ y ∉ Set.range φ := by
      by_contra hc
      push Not at hc
      exact hxy hc
    rw [extendMat_apply_of_not_mem hφ _ h]
    have h0 : (Matrix.single (φ a) (φ b) c) x y = 0 := by
      rw [Matrix.single_apply]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h ⟨a, rfl⟩
      · exact h ⟨b, rfl⟩
    rw [Matrix.add_apply, h0, add_zero]

end ExtSingle


section ImgRoot

variable {F : Type} [Field F] {σ : F ≃+* F} {n' n : ℕ} {τ : Fin n' → Fin n}
  (hτ : Function.Injective τ) (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i))

include hr in
theorem extendMat_rootMatrix (i j : Fin n') (c : F) :
    extendMat hτ (rootMatrix σ i j c) = rootMatrix σ (τ i) (τ j) c := by
  ext x y
  by_cases hxy : x ∈ Set.range τ ∧ y ∈ Set.range τ
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hxy
    rw [extendMat_apply_map]
    simp only [rootMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      hτ.eq_iff, ← hr]
  · have h : x ∉ Set.range τ ∨ y ∉ Set.range τ := by
      by_contra hc
      push Not at hc
      exact hxy hc
    rw [extendMat_apply_of_not_mem hτ _ h]
    have h1 : (Matrix.single (τ i) (τ j) c) x y = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h ⟨i, rfl⟩
      · exact h ⟨j, rfl⟩
    have h2 : (Matrix.single (Fin.rev (τ j)) (Fin.rev (τ i)) (σ c)) x y = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h ⟨Fin.rev j, hr j⟩
      · exact h ⟨Fin.rev i, hr i⟩
    simp only [rootMatrix, Matrix.sub_apply, Matrix.add_apply, h1, h2, add_zero, sub_zero]

include hr in
theorem extendMat_longRootMatrix (i : Fin n') (c : F) :
    extendMat hτ (longRootMatrix i c) = longRootMatrix (τ i) c := by
  ext x y
  by_cases hxy : x ∈ Set.range τ ∧ y ∈ Set.range τ
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hxy
    rw [extendMat_apply_map]
    simp only [longRootMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      hτ.eq_iff, ← hr]
  · have h : x ∉ Set.range τ ∨ y ∉ Set.range τ := by
      by_contra hc
      push Not at hc
      exact hxy hc
    rw [extendMat_apply_of_not_mem hτ _ h]
    have h1 : (Matrix.single (τ i) (Fin.rev (τ i)) c) x y = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h ⟨i, rfl⟩
      · exact h ⟨Fin.rev i, hr i⟩
    simp only [longRootMatrix, Matrix.add_apply, h1, add_zero]

include hr in
theorem extendMat_heisenbergMatrix (i k : Fin n') (hk : Fin.rev k = k) (a b : F) :
    extendMat hτ (heisenbergMatrix σ i k a b) =
      heisenbergMatrix σ (τ i) (τ k) a b := by
  have hk' : Fin.rev (τ k) = τ k := by rw [← hr, hk]
  ext x y
  by_cases hxy : x ∈ Set.range τ ∧ y ∈ Set.range τ
  · obtain ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩ := hxy
    rw [extendMat_apply_map]
    simp only [heisenbergMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, hτ.eq_iff, ← hr]
  · have h : x ∉ Set.range τ ∨ y ∉ Set.range τ := by
      by_contra hc
      push Not at hc
      exact hxy hc
    rw [extendMat_apply_of_not_mem hτ _ h]
    have h1 : (Matrix.single (τ i) (τ k) a) x y = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h ⟨i, rfl⟩
      · exact h ⟨k, rfl⟩
    have h2 : (Matrix.single (τ k) (Fin.rev (τ i)) (σ a)) x y = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h ⟨k, rfl⟩
      · exact h ⟨Fin.rev i, hr i⟩
    have h3 : (Matrix.single (τ i) (Fin.rev (τ i)) b) x y = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h ⟨i, rfl⟩
      · exact h ⟨Fin.rev i, hr i⟩
    simp only [heisenbergMatrix, Matrix.sub_apply, Matrix.add_apply, h1, h2, h3, add_zero, sub_zero]

end ImgRoot


section TwoRange

variable {F : Type} [Field F] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {φ : ι → Fin n} (hφ : Function.Injective φ)

omit [Fintype ι] [DecidableEq ι] in
include hφ in
theorem rev_comp_injective : Function.Injective (Fin.rev ∘ φ) :=
  Fin.rev_injective.comp hφ

theorem mem_range_of_sub_one_ne (A : Matrix ι ι F) {x y : Fin n}
    (h : (extendMat hφ A - 1) x y ≠ 0) : x ∈ Set.range φ ∧ y ∈ Set.range φ := by
  by_contra hc
  apply h
  have : x ∉ Set.range φ ∨ y ∉ Set.range φ := by
    by_contra hc'
    push Not at hc'
    exact hc hc'
  rw [Matrix.sub_apply, extendMat_apply_of_not_mem hφ A this, sub_self]

theorem sub_one_mul_sub_one_eq_zero {ψ : ι → Fin n} (hψ : Function.Injective ψ)
    (hd : ∀ i j, φ i ≠ ψ j) (A B : Matrix ι ι F) :
    (extendMat hφ A - 1) * (extendMat hψ B - 1) = 0 := by
  ext x y
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases h1 : (extendMat hφ A - 1) x t = 0
  · rw [h1, zero_mul]
  · by_cases h2 : (extendMat hψ B - 1) t y = 0
    · rw [h2, mul_zero]
    · obtain ⟨_, ⟨i, hi⟩⟩ := mem_range_of_sub_one_ne hφ A h1
      obtain ⟨⟨j, hj⟩, _⟩ := mem_range_of_sub_one_ne hψ B h2
      exact absurd (hi.trans hj.symm) (hd i j)

theorem extendMat_comm_of_disjoint {ψ : ι → Fin n} (hψ : Function.Injective ψ)
    (hd : ∀ i j, φ i ≠ ψ j) (A B : Matrix ι ι F) :
    extendMat hφ A * extendMat hψ B = extendMat hψ B * extendMat hφ A := by
  have h1 := sub_one_mul_sub_one_eq_zero hφ hψ hd A B
  have h2 := sub_one_mul_sub_one_eq_zero hψ hφ (fun i j => (hd j i).symm) B A
  have key : ∀ (P Q : Matrix (Fin n) (Fin n) F), P * Q = 0 → Q * P = 0 →
      (1 + P) * (1 + Q) = (1 + Q) * (1 + P) := by
    intro P Q hPQ hQP
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hPQ, hQP]
    abel
  have := key _ _ h1 h2
  simpa using this

end TwoRange


section Levi

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {a : ι → Fin n} (ha : Function.Injective a) (hd : ∀ i j, a i ≠ Fin.rev (a j))

include hd in
theorem extendMat_mul_antidiag_two (A : Matrix ι ι F) :
    extendMat ha A * (antidiag n : Matrix (Fin n) (Fin n) F) =
      (antidiag n : Matrix (Fin n) (Fin n) F) *
        extendMat (rev_comp_injective ha) A := by
  ext x y
  rw [mul_antidiag_apply, antidiag_mul_apply]
  have hiff : (x = Fin.rev y) ↔ (Fin.rev x = y) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
  by_cases h : x ∈ Set.range a ∧ Fin.rev y ∈ Set.range a
  · obtain ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩ := h
    have hy : y = (Fin.rev ∘ a) j := by simp [hj, Fin.rev_rev]
    have e1 : extendMat ha A (a i) (Fin.rev y) = A i j := by
      rw [← hj]; exact extendMat_apply_map ha A i j
    have e2 : extendMat (rev_comp_injective ha) A (Fin.rev (a i)) y = A i j := by
      rw [hy]; exact extendMat_apply_map (rev_comp_injective ha) A i j
    rw [e1, e2]
  · have h' : x ∉ Set.range a ∨ Fin.rev y ∉ Set.range a := by
      by_contra hc
      push Not at hc
      exact h hc
    have h2 : Fin.rev x ∉ Set.range (Fin.rev ∘ a) ∨ y ∉ Set.range (Fin.rev ∘ a) := by
      rcases h' with h' | h'
      · left
        rintro ⟨i, hi⟩
        exact h' ⟨i, by simpa [Function.comp_def] using Fin.rev_injective hi⟩
      · right
        rintro ⟨i, hi⟩
        exact h' ⟨i, by rw [← hi]; simp [Function.comp_def, Fin.rev_rev]⟩
    rw [extendMat_apply_of_not_mem ha A h', extendMat_apply_of_not_mem _ A h2]
    simp only [Matrix.one_apply, hiff]


variable (σ) in
@[expose] noncomputable def levMat (g : Matrix.SpecialLinearGroup ι F) : Matrix (Fin n) (Fin n) F :=
  extendMat ha (g : Matrix ι ι F) *
    extendMat (rev_comp_injective ha)
      ((((g⁻¹ : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F).map σ)ᵀ)

include hd in
theorem levMat_mul (g h : Matrix.SpecialLinearGroup ι F) :
    levMat σ ha (g * h) = levMat σ ha g * levMat σ ha h := by
  unfold levMat
  have hc : ∀ A B : Matrix ι ι F, extendMat ha A * extendMat (rev_comp_injective ha) B =
      extendMat (rev_comp_injective ha) B * extendMat ha A :=
    extendMat_comm_of_disjoint ha (rev_comp_injective ha) hd
  rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.map_mul, Matrix.transpose_mul, extendMat_mul ha, extendMat_mul (rev_comp_injective ha)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (extendMat (rev_comp_injective ha) _), ← hc, Matrix.mul_assoc]

theorem levMat_one : levMat σ ha (1 : Matrix.SpecialLinearGroup ι F) = 1 := by
  unfold levMat
  simp [extendMat_one]


include hd in
theorem levMat_unitary (hσ : ∀ c, σ (σ c) = c) (g : Matrix.SpecialLinearGroup ι F) :
    conjTr σ (levMat σ ha g) * antidiag n * levMat σ ha g = antidiag n := by
  set A : Matrix ι ι F := (g : Matrix ι ι F) with hA
  set X : Matrix ι ι F := ((g⁻¹ : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) with hX
  have hXA : X * A = 1 := by
    show ((g⁻¹ : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) * (g : Matrix ι ι F) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  set W : Matrix ι ι F := (X.map σ)ᵀ with hW
  set e₁ : Matrix ι ι F → Matrix (Fin n) (Fin n) F := extendMat ha with he₁
  set e₂ : Matrix ι ι F → Matrix (Fin n) (Fin n) F := extendMat (rev_comp_injective ha) with he₂
  set J : Matrix (Fin n) (Fin n) F := antidiag n with hJ
  have hc : ∀ P Q : Matrix ι ι F, e₁ P * e₂ Q = e₂ Q * e₁ P :=
    extendMat_comm_of_disjoint ha (rev_comp_injective ha) hd
  have hJ1 : ∀ B : Matrix ι ι F, e₁ B * J = J * e₂ B := extendMat_mul_antidiag_two ha hd
  have hJ2 : ∀ B : Matrix ι ι F, J * e₁ B = e₂ B * J := by
    intro B
    have h := hJ1 B
    have hJJ : J * J = 1 := antidiag_mul_self
    calc J * e₁ B = J * e₁ B * (J * J) := by rw [hJJ, Matrix.mul_one]
      _ = J * (e₁ B * J) * J := by simp only [Matrix.mul_assoc]
      _ = J * (J * e₂ B) * J := by rw [h]
      _ = e₂ B * J := by
        calc J * (J * e₂ B) * J = (J * J) * e₂ B * J := by simp only [Matrix.mul_assoc]
          _ = e₂ B * J := by rw [hJJ, Matrix.one_mul]
  have hM : conjTr σ (levMat σ ha g) = e₂ ((W.map σ)ᵀ) * e₁ ((A.map σ)ᵀ) := by
    unfold levMat
    rw [conjTr_mul, conjTr_extendMat ha A, conjTr_extendMat (rev_comp_injective ha)]
  have hWst : (W.map σ)ᵀ = X := by
    ext i j
    simp [hW, hσ]
  have hAW : (A.map σ)ᵀ * W = 1 := by
    rw [hW, ← Matrix.transpose_mul, ← Matrix.map_mul, hXA, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  have hJM : J * levMat σ ha g = e₂ A * (e₁ W * J) := by
    unfold levMat
    rw [← Matrix.mul_assoc, hJ2, Matrix.mul_assoc, ← hJ1 W]
  rw [hM, hWst, Matrix.mul_assoc, hJM]
  calc e₂ X * e₁ ((A.map σ)ᵀ) * (e₂ A * (e₁ W * J))
      = e₂ X * (e₁ ((A.map σ)ᵀ) * e₂ A) * (e₁ W * J) := by simp only [Matrix.mul_assoc]
    _ = e₂ X * (e₂ A * e₁ ((A.map σ)ᵀ)) * (e₁ W * J) := by rw [hc]
    _ = e₂ (X * A) * e₁ ((A.map σ)ᵀ * W) * J := by
        rw [he₂, he₁, extendMat_mul, extendMat_mul]
        simp only [Matrix.mul_assoc]
    _ = J := by
        rw [hXA, hAW]
        simp only [he₁, he₂, extendMat_one, Matrix.one_mul]


theorem det_levMat (g : Matrix.SpecialLinearGroup ι F) : (levMat σ ha g).det = 1 := by
  unfold levMat
  rw [Matrix.det_mul, det_extendMat, det_extendMat, Matrix.det_transpose]
  have h1 : (g : Matrix ι ι F).det = 1 := g.2
  have h2 : (((g⁻¹ : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)).det = 1 := (g⁻¹).2
  have h3 := RingHom.map_det σ.toRingHom ((g⁻¹ : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)
  rw [h1, one_mul]
  have : (((g⁻¹ : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F).map σ).det = 1 := by
    have h4 : (σ.toRingHom.mapMatrix ((g⁻¹ : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F)).det = 1 := by
      rw [← h3, h2, map_one]
    exact h4
  exact this

include hd in
@[expose] noncomputable def levSU (hσ : ∀ c, σ (σ c) = c) :
    Matrix.SpecialLinearGroup ι F →* SU σ n :=
  (({ toFun := levMat σ ha, map_one' := levMat_one ha, map_mul' := levMat_mul ha hd } :
    Matrix.SpecialLinearGroup ι F →* Matrix (Fin n) (Fin n) F).toHomUnits).codRestrict (SU σ n)
    (fun g => ⟨det_levMat ha g, levMat_unitary ha hd hσ g⟩)

include hd in
theorem mat_levSU (hσ : ∀ c, σ (σ c) = c) (g : Matrix.SpecialLinearGroup ι F) :
    mat σ n (levSU ha hd hσ g) = levMat σ ha g := rfl

include hd in
theorem levSU_injective (hσ : ∀ c, σ (σ c) = c) : Function.Injective (levSU ha hd hσ) := by
  intro g h hgh
  have := congrArg (mat σ n) hgh
  rw [mat_levSU, mat_levSU] at this
  have key : ∀ g : Matrix.SpecialLinearGroup ι F,
      (levMat σ ha g).submatrix a a = (g : Matrix ι ι F) := by
    intro g
    ext i j
    have haj : a j ∉ Set.range (Fin.rev ∘ a) := fun ⟨k, hk⟩ => hd j k hk.symm
    simp only [Matrix.submatrix_apply]
    unfold levMat
    rw [Matrix.mul_apply, Finset.sum_eq_single (a j)]
    · rw [extendMat_apply_map ha, extendMat_apply_of_not_mem _ _ (Or.inr haj)]
      simp
    · intro t _ ht
      rw [extendMat_apply_of_not_mem _ _ (Or.inr haj), Matrix.one_apply_ne ht, mul_zero]
    · simp
  have h2 := congrArg (fun A => A.submatrix a a) this
  simp only [key] at h2
  exact Subtype.ext h2


include hd in
theorem levMat_transvection {u v : ι} (hne : u ≠ v) (c : F) :
    levMat σ ha (Matrix.SpecialLinearGroup.transvection hne c) = rootMatrix σ (a u) (a v) c := by
  have hW : (((1 : Matrix ι ι F) + Matrix.single u v (-c)).map σ)ᵀ =
      1 + Matrix.single v u (-σ c) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    by_cases h : u = j ∧ v = i
    · obtain ⟨rfl, rfl⟩ := h
      have h1 : ¬ (u = v) := hne
      have h2 : ¬ (v = u) := Ne.symm hne
      simp [h1, h2, map_neg]
    · have h' : ¬ (v = i ∧ u = j) := fun ⟨a, b⟩ => h ⟨b, a⟩
      simp only [if_neg h, if_neg h', add_zero]
      by_cases h3 : j = i
      · simp [h3]
      · simp [h3, Ne.symm h3]
  unfold levMat
  rw [Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  rw [hW, extendMat_one_add_single ha, extendMat_one_add_single (rev_comp_injective ha)]
  have hXY : (Matrix.single (a u) (a v) c : Matrix (Fin n) (Fin n) F) *
      Matrix.single ((Fin.rev ∘ a) v) ((Fin.rev ∘ a) u) (-σ c) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ (hd v v) _
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hXY]
  simp only [rootMatrix, Function.comp_def, Matrix.single_neg, sub_eq_add_neg]
  abel

end Levi


section Images

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n' n : ℕ} {τ : Fin n' → Fin n}
  (hτ : Function.Injective τ) (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i))

include hτ hr in
theorem ne_rev_of_embed {i : Fin n'} (hi : i ≠ Fin.rev i) : τ i ≠ Fin.rev (τ i) := by
  intro h
  apply hi
  apply hτ
  rw [hr, ← h]

include hr in
theorem suEmbed_rootHom {i j : Fin n'} (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j)
    (c : Multiplicative F) :
    suEmbed σ hτ hr (rootHom σ hσ hij hi hj c) =
      rootHom σ hσ (hτ.ne hij) (ne_rev_of_embed hτ hr hi) (ne_rev_of_embed hτ hr hj) c := by
  apply mat_injective
  rw [mat_suEmbed]
  exact extendMat_rootMatrix hτ hr i j c.toAdd

include hr in
theorem suEmbed_longRootHom {i : Fin n'} (hi : i ≠ Fin.rev i) (c : Multiplicative (traceZero σ)) :
    suEmbed σ hτ hr (longRootHom σ hi c) = longRootHom σ (ne_rev_of_embed hτ hr hi) c := by
  apply mat_injective
  rw [mat_suEmbed]
  exact extendMat_longRootMatrix hτ hr i (c.toAdd : F)

include hr in
theorem suEmbed_mem_heisenbergSubgroup {i k : Fin n'} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) {x : SU σ n'} (hx : x ∈ heisenbergSubgroup σ hσ hi hik hk) :
    suEmbed σ hτ hr x ∈ heisenbergSubgroup σ hσ (ne_rev_of_embed hτ hr hi) (hτ.ne hik)
      (by rw [← hr, hk]) := by
  obtain ⟨a, b, hab, hmat⟩ := hx
  refine ⟨a, b, hab, ?_⟩
  have h1 : mat σ n' x = heisenbergMatrix σ i k a b := hmat
  show mat σ n (suEmbed σ hτ hr x) = _
  rw [mat_suEmbed, h1]
  exact extendMat_heisenbergMatrix hτ hr i k hk a b

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a : ι → Fin n} (ha : Function.Injective a)
  (hd : ∀ i j, a i ≠ Fin.rev (a j))

include hd in
theorem levSU_transvection {u v : ι} (hne : u ≠ v) (c : F) :
    levSU ha hd hσ (Matrix.SpecialLinearGroup.transvection hne c) =
      rootHom σ hσ (fun e => hne (ha e)) (fun e => hd u u e) (fun e => hd v v e)
        (Multiplicative.ofAdd c) := by
  apply mat_injective
  rw [mat_levSU]
  exact levMat_transvection ha hd hne c

end Images

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
