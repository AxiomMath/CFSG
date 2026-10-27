module

public import CFSG.ClassicalInvolution.Asc77.AscT7L22
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuStd

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
  CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

namespace T7L

section Transport

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def Pmat (ω : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 2⁻¹; ω, 0, 0, -(ω * 2⁻¹); 0, 1, 2⁻¹, 0; 0, ω, -(ω * 2⁻¹), 0]

theorem conjTr_Pmat_mul (h2 : (2 : K) ≠ 0) {ω : K} (hω : ω * ω = -1) (hσω : σ ω = ω) :
    conjTr σ (Pmat ω) * Pmat ω = antidiag 4 := by
  rw [antidiag_four]
  have hh : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, Pmat, Matrix.mul_apply, Fin.sum_univ_four, hσω, map_inv₀, map_ofNat]
  all_goals first
    | linear_combination hω
    | linear_combination (-2⁻¹ : K) * hω + hh
    | linear_combination (2⁻¹ * 2⁻¹ : K) * hω

end Transport

section Transport2

variable {K : Type} [Field K]

theorem antidiag_four_mul : (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * antidiag 4 = 1 := by
  rw [antidiag_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

@[expose] noncomputable def Pgl {σ : K ≃+* K} (h2 : (2 : K) ≠ 0) {ω : K} (hω : ω * ω = -1)
    (hσω : σ ω = ω) : GL (Fin 4) K :=
  ⟨Pmat ω, antidiag 4 * conjTr σ (Pmat ω),
    mul_eq_one_comm.mp (by
      rw [Matrix.mul_assoc, conjTr_Pmat_mul h2 hω hσω, antidiag_four_mul]),
    by rw [Matrix.mul_assoc, conjTr_Pmat_mul h2 hω hσω, antidiag_four_mul]⟩

theorem Pgl_val {σ : K ≃+* K} (h2 : (2 : K) ≠ 0) {ω : K} (hω : ω * ω = -1) (hσω : σ ω = ω) :
    ((Pgl (σ := σ) h2 hω hσω : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Pmat ω := rfl

theorem Pgl_isom {σ : K ≃+* K} (h2 : (2 : K) ≠ 0) {ω : K} (hω : ω * ω = -1) (hσω : σ ω = ω) :
    conjTr σ ((Pgl (σ := σ) h2 hω hσω : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((Pgl (σ := σ) h2 hω hσω : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = antidiag 4 := by
  rw [Pgl_val]
  exact conjTr_Pmat_mul h2 hω hσω

theorem Pmat_mul_diag_X (ω : K) :
    Pmat ω * Matrix.diagonal ![-1, 1, 1, -1] =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * Pmat ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pmat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

theorem Pmat_mul_diag_D {ω : K} (hω : ω * ω = -1) :
    Pmat ω * Matrix.diagonal ![ω, ω, -ω, -ω] =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] * Pmat ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pmat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
  all_goals first
    | ring1
    | linear_combination hω
    | linear_combination (2⁻¹ : K) * hω

end Transport2

section Transport3

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjEquiv_x0 (h2 : (2 : K) ≠ 0) {ω : K} (hω : ω * ω = -1)
    (hσω : unitaryInvolution K p f ω = ω) :
    conjEquiv (Pgl (σ := unitaryInvolution K p f) h2 hω hσω) (Pgl_isom h2 hω hσω)
      (XelU (unitaryInvolution K p f)) = x0 K p f := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_conjEquiv, Units.val_mul, Units.val_mul]
  change ((Pgl (σ := unitaryInvolution K p f) h2 hω hσω : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) * smat (XelU (unitaryInvolution K p f)) *
    (((Pgl (σ := unitaryInvolution K p f) h2 hω hσω)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = suMat (x0 K p f)
  rw [Pgl_val, smat_XelU, Pmat_mul_diag_X, suMat_x0, Matrix.mul_assoc]
  have : Pmat ω * (((Pgl (σ := unitaryInvolution K p f) h2 hω hσω)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Pgl_val h2 hω hσω (σ := unitaryInvolution K p f), ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  rw [this, Matrix.mul_one]

theorem conjEquiv_u0 (h2 : (2 : K) ≠ 0) {ω : K} (hω : ω * ω = -1)
    (hσω : unitaryInvolution K p f ω = ω) :
    conjEquiv (Pgl (σ := unitaryInvolution K p f) h2 hω hσω) (Pgl_isom h2 hω hσω)
      (DelU (unitaryInvolution K p f) hω hσω) = u0 K p f := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_conjEquiv, Units.val_mul, Units.val_mul]
  change ((Pgl (σ := unitaryInvolution K p f) h2 hω hσω : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) * smat (DelU (unitaryInvolution K p f) hω hσω) *
    (((Pgl (σ := unitaryInvolution K p f) h2 hω hσω)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = suMat (u0 K p f)
  rw [Pgl_val, smat_DelU, Pmat_mul_diag_D hω, suMat_u0, Matrix.mul_assoc]
  have : Pmat ω * (((Pgl (σ := unitaryInvolution K p f) h2 hω hσω)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Pgl_val h2 hω hσω (σ := unitaryInvolution K p f), ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  rw [this, Matrix.mul_one]

theorem top_le_sup_of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {x y : G}
    {x' y' : G'} (hx : e x = x') (hy : e y = y')
    (h : (⊤ : Subgroup G) ≤
      Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.centralizer ({y} : Set G)) :
    (⊤ : Subgroup G') ≤
      Subgroup.centralizer ({x'} : Set G') ⊔ Subgroup.centralizer ({y'} : Set G') := by
  have hmap : ∀ {k : G} {k' : G'}, e k = k' →
      (Subgroup.centralizer ({k} : Set G)).map e.toMonoidHom ≤
        Subgroup.centralizer ({k'} : Set G') := by
    intro k k' hk
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ Subgroup.centralizer ({k} : Set G) := hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hw'
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    show e w * e k = e k * e w
    rw [← map_mul, ← map_mul, hw']
  intro z _
  have hz : e.symm z ∈ Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.centralizer ({y} : Set G) :=
    h trivial
  have h2 : (Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.centralizer ({y} : Set G)).map
      e.toMonoidHom ≤ Subgroup.centralizer ({x'} : Set G') ⊔
        Subgroup.centralizer ({y'} : Set G') := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (hmap hx) (hmap hy)
  have := h2 ⟨_, hz, rfl⟩
  simpa using this

theorem top_le_x0_sup_u0_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {ω : K}
    (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = ω) :
    (⊤ : Subgroup (Su K p f 4)) ≤ Subgroup.centralizer ({x0 K p f} : Set (Su K p f 4)) ⊔
      Subgroup.centralizer ({u0 K p f} : Set (Su K p f 4)) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨ζ, hζ0, hζt⟩ := hσ.exists_traceZero
  have hnorm : ∀ x, unitaryInvolution K p f x = x → ∃ a, unitaryInvolution K p f a * a = x := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    · exact hσ.norm_surj x hx hx0
  have key := top_le_XD hσ.invol ⟨ζ, hζ0, hζt⟩ hσ.trace_surj hnorm hω hσω
  exact top_le_sup_of_equiv (conjEquiv (Pgl (σ := unitaryInvolution K p f) h2 hω hσω)
    (Pgl_isom h2 hω hσω)) (conjEquiv_x0 h2 hω hσω) (conjEquiv_u0 h2 hω hσω) key

end Transport3

end T7L

end CFSG.ClassicalInvolution.Asc77
