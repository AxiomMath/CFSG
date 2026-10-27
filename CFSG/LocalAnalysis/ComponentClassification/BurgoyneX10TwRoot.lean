module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Root
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem eq_of_proj_eq_unipotent (hn : 0 < n) {g g' : SpecialLinearGroup (Fin n) K}
    {N N' : Matrix (Fin n) (Fin n) K} (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + N)
    (hg' : (g' : Matrix (Fin n) (Fin n) K) = 1 + N') (hN : N * N = 0) (hN' : N' * N' = 0)
    (h : proj n K g = proj n K g') : g = g' := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h)
  have h1 : (g' : Matrix (Fin n) (Fin n) K) = (c : K) • (g : Matrix (Fin n) (Fin n) K) := by
    have h2 : g' = g * (g⁻¹ * g') := by group
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have h3 : (c : K) • (1 + N) = 1 + N' := by rw [← hg, ← hg', h1]
  have hc1 : (c : K) = 1 := eq_one_of_smul_unipotent hn hN' hN h3
  exact Subtype.ext (by rw [h1, hc1, one_smul])

theorem rootClass_injective_psl (hn : 0 < n) {N : Matrix (Fin n) (Fin n) K} (hN2 : N * N = 0)
    (hN : N ≠ 0) (r : K → SpecialLinearGroup (Fin n) K)
    (hr : ∀ c, ((r c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + c • N)
    {a b : K} (h : proj n K (r a) = proj n K (r b)) : a = b := by
  have hs : ∀ c : K, (c • N) * (c • N) = 0 := fun c => by
    rw [smul_mul_smul_comm, hN2, smul_zero]
  have h1 := eq_of_proj_eq_unipotent hn (hr a) (hr b) (hs a) (hs b) h
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h1
  simp only [hr] at h2
  have h3 : (a - b) • N = 0 := by
    rw [sub_smul, add_left_cancel h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hN)

theorem coe_inv_of_unipotent {g : SpecialLinearGroup (Fin n) K} {N : Matrix (Fin n) (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + N) (hN : N * N = 0) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - N := by
  have h1 : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (1 - N) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [hg, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hN]
    abel
  calc ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (1 - N) * (g : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [h2, Matrix.one_mul]
    _ = 1 - N := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exists_linear_root_image {N : Matrix (Fin n) (Fin n) K} (hN2 : N * N = 0)
    (A : GL (Fin n) K) (ε : ℕ) (hε : ε ≤ 1) :
    ∃ M : Matrix (Fin n) (Fin n) K, M * M = 0 ∧ ∀ (c : K) (g : SpecialLinearGroup (Fin n) K),
      (g : Matrix (Fin n) (Fin n) K) = 1 + c • N → ∃ g' : SpecialLinearGroup (Fin n) K,
        (g' : Matrix (Fin n) (Fin n) K) = 1 + c • M ∧
          (conjAut n K A * dualAut n K ^ ε) (proj n K g) = proj n K g' := by
  set Am := (A : Matrix (Fin n) (Fin n) K) with hAm
  set Ai := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAi
  have hAAi : Am * Ai = 1 := by rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : Ai * Am = 1 := by rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  interval_cases ε
  · refine ⟨Am * N * Ai, ?_, fun c g hg => ⟨CatalogueBHigherLinearAction.slConjugation n K A g,
      ?_, ?_⟩⟩
    · calc Am * N * Ai * (Am * N * Ai) = Am * (N * (Ai * Am) * N) * Ai := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hAiA, Matrix.mul_one, hN2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [coe_slConjugation, hg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAAi,
        Matrix.mul_smul, Matrix.smul_mul]
    · rw [pow_zero, mul_one, conjAut_proj]
  · refine ⟨-(Am * Nᵀ * Ai), ?_, fun c g hg =>
      ⟨CatalogueBHigherLinearAction.slConjugation n K A (g⁻¹).transpose, ?_, ?_⟩⟩
    · have hT : Nᵀ * Nᵀ = 0 := by rw [← Matrix.transpose_mul, hN2, Matrix.transpose_zero]
      calc -(Am * Nᵀ * Ai) * -(Am * Nᵀ * Ai) = Am * (Nᵀ * (Ai * Am) * Nᵀ) * Ai := by
            simp only [neg_mul_neg, Matrix.mul_assoc]
        _ = 0 := by rw [hAiA, Matrix.mul_one, hT, Matrix.mul_zero, Matrix.zero_mul]
    · have hs : (c • N) * (c • N) = 0 := by rw [smul_mul_smul_comm, hN2, smul_zero]
      have hinv := coe_inv_of_unipotent hg hs
      have htr : (((g⁻¹).transpose : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          1 - c • Nᵀ := by
        change ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = _
        rw [hinv, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]
      rw [coe_slConjugation, htr, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAAi,
        Matrix.mul_smul, Matrix.smul_mul, smul_neg, sub_eq_add_neg]
    · rw [pow_one, MulAut.mul_apply, dualAut_proj, conjAut_proj]

theorem card_fixed_root_of_linear_psl (hn : 0 < n) {N : Matrix (Fin n) (Fin n) K}
    (hN2 : N * N = 0) (hN : N ≠ 0) (r : K → SpecialLinearGroup (Fin n) K)
    (hr : ∀ c, ((r c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + c • N)
    (A : GL (Fin n) K) (ε : ℕ) (hε : ε ≤ 1)
    (hnorm : ∀ c, ∃ c', (conjAut n K A * dualAut n K ^ ε) (proj n K (r c)) = proj n K (r c')) :
    Nat.card {c : K // (conjAut n K A * dualAut n K ^ ε) (proj n K (r c)) = proj n K (r c)} =
        1 ∨
      Nat.card {c : K // (conjAut n K A * dualAut n K ^ ε) (proj n K (r c)) = proj n K (r c)} =
        Nat.card K := by
  set α := conjAut n K A * dualAut n K ^ ε with hα
  obtain ⟨M, hM2, hM⟩ := exists_linear_root_image hN2 A ε hε
  have hsM : ∀ c : K, (c • M) * (c • M) = 0 := fun c => by
    rw [smul_mul_smul_comm, hM2, smul_zero]
  have hsN : ∀ c : K, (c • N) * (c • N) = 0 := fun c => by
    rw [smul_mul_smul_comm, hN2, smul_zero]
  obtain ⟨c₁, hc₁⟩ := hnorm 1
  obtain ⟨g₁, hg₁, hα₁⟩ := hM 1 (r 1) (hr 1)
  have h1 : g₁ = r c₁ :=
    eq_of_proj_eq_unipotent hn hg₁ (hr c₁) (hsM 1) (hsN c₁) (hα₁.symm.trans hc₁)
  have hMN : M = c₁ • N := by
    have h2 := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h1
    simp only [hg₁, hr, one_smul] at h2
    exact add_left_cancel h2
  have hl : ∀ c, α (proj n K (r c)) = proj n K (r (c₁ * c)) := by
    intro c
    obtain ⟨g', hg', hα'⟩ := hM c (r c) (hr c)
    rw [hα']
    congr 1
    apply Subtype.ext
    rw [hg', hr, hMN, smul_smul, mul_comm]
  have hfix : ∀ c, α (proj n K (r c)) = proj n K (r c) ↔ c₁ * c = c := by
    intro c
    rw [hl c]
    exact ⟨rootClass_injective_psl hn hN2 hN r hr, fun h => by rw [h]⟩
  by_cases hl1 : c₁ = 1
  · right
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun c => (hfix c).mpr (by rw [hl1, one_mul]))]
  · left
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, (hfix 0).mpr (by rw [mul_zero])⟩, fun x => Subtype.ext ?_⟩
    have h2 := (hfix x.1).mp x.2
    have h3 : (c₁ - 1) * x.1 = 0 := by rw [sub_mul, h2, one_mul, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hl1)

variable [Finite K]

theorem ringEquiv_ne_one_of_root_action (hn : 0 < n) {N : Matrix (Fin n) (Fin n) K}
    (hN2 : N * N = 0) (hN : N ≠ 0) (r : K → SpecialLinearGroup (Fin n) K)
    (hr : ∀ c, ((r c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + c • N)
    (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1) (w : K → projectiveSL n K)
    (φ₀ : K → K) (hinto : ∀ c, ∃ c', w c = proj n K (r c'))
    (honto : ∀ c', ∃ c, w c = proj n K (r c'))
    (hact : ∀ c, (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) (w c) = w (φ₀ c))
    (h1 : Nat.card {c : K // φ₀ c = c} ≠ 1) (hK : Nat.card {c : K // φ₀ c = c} ≠ Nat.card K) :
    σ ≠ 1 := by
  intro hσ
  subst hσ
  simp only [map_one, mul_one] at hact
  choose φ hφ using hinto
  have hφs : Function.Surjective φ := fun c' => by
    obtain ⟨c, hc⟩ := honto c'
    exact ⟨c, rootClass_injective_psl hn hN2 hN r hr (by rw [← hφ c, hc])⟩
  have hφi : Function.Injective φ := Finite.injective_iff_surjective.mpr hφs
  have hnorm : ∀ c, ∃ c', (conjAut n K A * dualAut n K ^ ε) (proj n K (r c)) =
      proj n K (r c') := by
    intro c'
    obtain ⟨c, rfl⟩ := hφs c'
    exact ⟨φ (φ₀ c), by rw [← hφ c, hact, hφ]⟩
  have hfix : ∀ c, (conjAut n K A * dualAut n K ^ ε) (proj n K (r (φ c))) =
      proj n K (r (φ c)) ↔ φ₀ c = c := by
    intro c
    rw [← hφ c, hact, hφ, hφ]
    constructor
    · exact fun h => hφi (rootClass_injective_psl hn hN2 hN r hr h)
    · intro h
      rw [h]
  have hcard : Nat.card {c : K // (conjAut n K A * dualAut n K ^ ε) (proj n K (r c)) =
      proj n K (r c)} = Nat.card {c : K // φ₀ c = c} :=
    Nat.card_congr ((Equiv.ofBijective φ ⟨hφi, hφs⟩).subtypeEquiv fun c => (hfix c).symm).symm
  rcases card_fixed_root_of_linear_psl hn hN2 hN r hr A ε hε hnorm with h | h
  · exact h1 (hcard ▸ h)
  · exact hK (hcard ▸ h)

end CFSG.ComponentClassification.Burgoyne.X10
