module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] (Q : QuadraticForm K (ι → K))

theorem polar_map_of_linearIsometry {ι' : Type*}
    {Q' : QuadraticForm K (ι' → K)} (φ : (ι → K) ≃ₗ[K] (ι' → K))
    (hφ : ∀ x, Q' (φ x) = Q x) (x y : ι → K) :
    polar Q' (φ x) (φ y) = polar Q x y := by
  simp only [polar, ← map_add, hφ]

theorem isometry_inv {g : GL ι K}
    (hg : ∀ x, Q ((g : Matrix ι ι K) *ᵥ x) = Q x) :
    ∀ x, Q (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) = Q x := by
  intro x
  have h := hg (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at h
  exact h.symm

def lineStabilizer (e : ι → K) : Subgroup (GL ι K) where
  carrier := {g | (∀ x, Q ((g : Matrix ι ι K) *ᵥ x) = Q x) ∧
    ∃ c : K, (g : Matrix ι ι K) *ᵥ e = c • e}
  mul_mem' := by
    rintro g h ⟨hgiso, c, hge⟩ ⟨hhiso, d, hhe⟩
    refine ⟨?_, d * c, ?_⟩
    · intro x
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hgiso ((h : Matrix ι ι K) *ᵥ x), hhiso x]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hhe, Matrix.mulVec_smul, hge, smul_smul]
  one_mem' := ⟨fun x => by simp, 1, by simp⟩
  inv_mem' := by
    rintro g ⟨hgiso, c, hge⟩
    refine ⟨isometry_inv Q hgiso, ?_⟩
    by_cases hc : c = 0
    · have he : e = 0 := by
        have h0 : (g : Matrix ι ι K) *ᵥ e = 0 := by rw [hge, hc, zero_smul]
        have h : ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ e) = 0 := by
          rw [h0, Matrix.mulVec_zero]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec] at h
        exact h
      refine ⟨0, ?_⟩
      rw [he, Matrix.mulVec_zero, zero_smul]
    · refine ⟨c⁻¹, ?_⟩
      set y : ι → K := ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ e with hy
      have h : e = c • y := by
        have h' := congrArg (fun z => ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ z) hge
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec, Matrix.mulVec_smul] at h'
        exact h'
      rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]

@[simp]
theorem mem_lineStabilizer_iff {e : ι → K} {g : GL ι K} :
    g ∈ lineStabilizer Q e ↔ (∀ x, Q ((g : Matrix ι ι K) *ᵥ x) = Q x) ∧
      ∃ c : K, (g : Matrix ι ι K) *ᵥ e = c • e := Iff.rfl

theorem mem_lineStabilizer_of_intertwine {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    {Q' : QuadraticForm K (ι' → K)} (φ : (ι → K) ≃ₗ[K] (ι' → K)) (hφ : ∀ x, Q' (φ x) = Q x)
    {g : GL ι K} {g' : GL ι' K}
    (hgg' : ∀ x, (g' : Matrix ι' ι' K) *ᵥ φ x = φ ((g : Matrix ι ι K) *ᵥ x)) {e : ι → K}
    (hg : g ∈ lineStabilizer Q e) : g' ∈ lineStabilizer Q' (φ e) := by
  obtain ⟨hgiso, c, hge⟩ := (mem_lineStabilizer_iff Q).mp hg
  refine (mem_lineStabilizer_iff Q').mpr ⟨?_, c, ?_⟩
  · intro x'
    obtain ⟨x, rfl⟩ := φ.surjective x'
    rw [hgg', hφ, hφ, hgiso]
  · rw [hgg', hge, map_smul]

end CFSG.ClassicalGroups.Orthogonal
