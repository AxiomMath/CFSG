module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TBlocks
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks PSpL UnitaryOut
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem ringEquiv_eq_refl_or_bar_of_fixes' {τ : K ≃+* K} (hτ : ∀ c, h.bar c = c → τ c = c) :
    τ = RingEquiv.refl K ∨ ∀ c, τ c = h.bar c := by
  have hσσ : ∀ c, h.bar (h.bar c) = c := h.bar_bar
  have key : ∀ c : K, τ c = c ∨ τ c = h.bar c := by
    intro c
    have h1 : (τ c - c) * (τ c - h.bar c) = 0 := by
      have e1 : h.bar (c + h.bar c) = c + h.bar c := by rw [map_add, hσσ, add_comm]
      have e2 : h.bar (c * h.bar c) = c * h.bar c := by rw [map_mul, hσσ, mul_comm]
      have h2 := hτ _ e1
      have h3 := hτ _ e2
      have h4 : c ^ 2 - (c + h.bar c) * c + c * h.bar c = 0 := by ring
      have h5 := congrArg τ h4
      rw [map_add, map_sub, map_mul, map_pow, map_zero, h2, h3] at h5
      linear_combination h5
    rcases mul_eq_zero.mp h1 with h6 | h6
    · exact Or.inl (sub_eq_zero.mp h6)
    · exact Or.inr (sub_eq_zero.mp h6)
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hn₁, hn₂⟩ := hcon
  obtain ⟨c₁, hc₁⟩ : ∃ c, τ c ≠ c := by
    by_contra h0
    exact hn₁ (RingEquiv.ext fun c => by_contra fun hc => h0 ⟨c, hc⟩)
  obtain ⟨c₂, hc₂⟩ : ∃ c, τ c ≠ h.bar c := by
    by_contra h0
    exact hn₂ fun c => by_contra fun hc => h0 ⟨c, hc⟩
  have h1 : τ c₁ = h.bar c₁ := (key c₁).resolve_left hc₁
  have h2 : τ c₂ = c₂ := (key c₂).resolve_right hc₂
  rcases key (c₁ + c₂) with h3 | h3
  · rw [map_add, h1, h2] at h3
    exact hc₁ (by rw [h1]; exact add_right_cancel h3)
  · rw [map_add, h1, h2, map_add] at h3
    exact hc₂ (by rw [h2]; exact add_left_cancel h3)

theorem comm_cP_of_fix_map (P : GL (Fin 4) K) (φ : K ≃+* K) {A : GL (Fin 4) K}
    {g : unitarySU p f K 4}
    (hg : (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map φ) *
        (cP P g).map φ =
      cP P g * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map φ) := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPb : (P : Matrix (Fin 4) (Fin 4) K).map φ *
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map φ = 1 := by
    rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAA : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg' : (A : Matrix (Fin 4) (Fin 4) K) *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A := by
    conv_rhs => rw [← hg]
    rw [Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K), hAA, Matrix.mul_one]
  simp only [cP, Matrix.map_mul]
  calc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (P : Matrix (Fin 4) (Fin 4) K).map φ *
        ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).map φ *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *
          (P : Matrix (Fin 4) (Fin 4) K).map φ) =
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((A : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ) *
        (P : Matrix (Fin 4) (Fin 4) K).map φ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ((P : Matrix (Fin 4) (Fin 4) K).map φ), hPb, Matrix.one_mul]
    _ = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        A) * (P : Matrix (Fin 4) (Fin 4) K).map φ := by rw [hg']
    _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P : Matrix (Fin 4) (Fin 4) K) (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K),
          hPP, Matrix.one_mul]

variable (p f) in
@[expose] def blkConjU (R : GL (Fin 4) K) : Set (MulAut (StatedProj (StatedSU 4 (p ^ f) K))) :=
  {α | ∃ A : GL (Fin 4) K, (∃ x y : K, (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
      (A : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = bd (x • 1) (y • 1)) ∧
    ∀ g : unitarySU p f K 4, ∃ g' : unitarySU p f K 4,
      ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (A : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) ∧
      α (QuotientGroup.mk g) = QuotientGroup.mk g'}

theorem blkConjU_comm (R : GL (Fin 4) K) :
    ∀ α ∈ blkConjU p f R, ∀ β ∈ blkConjU p f R, α * β = β * α := by
  rintro α ⟨A, ⟨x, y, hA⟩, hα⟩ β ⟨B, ⟨x', y', hB⟩, hβ⟩
  have hRR : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRR' : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have eA : (A : Matrix (Fin 4) (Fin 4) K) = (R : Matrix (Fin 4) (Fin 4) K) * bd (x • 1) (y • 1) *
      (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hA]
    simp only [← Matrix.mul_assoc, hRR', Matrix.one_mul]
    rw [Matrix.mul_assoc, hRR', Matrix.mul_one]
  have eB : (B : Matrix (Fin 4) (Fin 4) K) = (R : Matrix (Fin 4) (Fin 4) K) *
      bd (x' • 1) (y' • 1) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    rw [← hB]
    simp only [← Matrix.mul_assoc, hRR', Matrix.one_mul]
    rw [Matrix.mul_assoc, hRR', Matrix.mul_one]
  have hDD : bd (x • (1 : Matrix (Fin 2) (Fin 2) K)) (y • 1) * bd (x' • 1) (y' • 1) =
      bd (x' • (1 : Matrix (Fin 2) (Fin 2) K)) (y' • 1) * bd (x • 1) (y • 1) := by
    rw [bd_mul, bd_mul, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm x',
      smul_mul_smul_comm y', mul_comm x, mul_comm y]
  have hAB : A * B = B * A := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, eA, eB]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) (R : Matrix (Fin 4) (Fin 4) K), hRR,
      Matrix.one_mul, ← Matrix.mul_assoc (bd (x • 1) (y • 1)), hDD]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) (R : Matrix (Fin 4) (Fin 4) K), hRR,
      Matrix.one_mul]
  refine MulEquiv.ext fun z => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨g₁, hg₁, hβg⟩ := hβ g
  obtain ⟨g₂, hg₂, hαg₁⟩ := hα g₁
  obtain ⟨g₃, hg₃, hαg⟩ := hα g
  obtain ⟨g₄, hg₄, hβg₃⟩ := hβ g₃
  rw [MulAut.mul_apply, MulAut.mul_apply, hβg, hαg₁, hαg, hβg₃]
  congr 1
  apply ext_val
  rw [hg₂, hg₁, hg₄, hg₃]
  have e : A * (B * (g : GL (Fin 4) K) * B⁻¹) * A⁻¹ = B * (A * (g : GL (Fin 4) K) * A⁻¹) * B⁻¹ :=
    calc A * (B * (g : GL (Fin 4) K) * B⁻¹) * A⁻¹ = (A * B) * (g : GL (Fin 4) K) * (A * B)⁻¹ := by
          group
      _ = (B * A) * (g : GL (Fin 4) K) * (B * A)⁻¹ := by rw [hAB]
      _ = B * (A * (g : GL (Fin 4) K) * A⁻¹) * B⁻¹ := by group
  have e' := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) e
  simpa only [Units.val_mul, Matrix.mul_assoc] using e'

end CFSG.ClassicalInvolution.Q3.TA3.Q5U4
