module

public import CFSG.LieType.ChevTwo.OppCl.AutLiftsNorm
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration

public section

namespace CFSG.LieType.ChevTwo.OppCl

open Matrix CFSG.Open CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Sp

variable {r : ℕ} {F : Type} [Field F]

theorem semiIso_semilinMap_sp (A : GL (Fin r ⊕ Fin r) F) (σ : F ≃+* F)
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ * formJ r F *
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = formJ r F) :
    SemiIso (spForm r F) (semilinMap A σ) := by
  refine ⟨σ, fun u v => ?_⟩
  have h1 : ∀ (x y : Fin r ⊕ Fin r → F),
      ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ x) ⬝ᵥ
        (formJ r F *ᵥ ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ y)) =
      x ⬝ᵥ (formJ r F *ᵥ y) := by
    intro x y
    rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc,
      hA, ← dotProduct_mulVec]
  have h2 : σ (u ⬝ᵥ (formJ r F *ᵥ v)) =
      (fun i => σ (u i)) ⬝ᵥ (formJ r F *ᵥ (fun i => σ (v i))) := by
    have := map_mulVec_ringEquiv σ (formJ r F) v
    rw [formJ_map] at this
    rw [← this]
    simp [dotProduct, map_sum, map_mul]
  rw [spForm_β, spForm_β, semilinMap_apply, semilinMap_apply]
  show ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ _) ⬝ᵥ
    (formJ r F *ᵥ ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ _)) = _
  rw [h1, h2]

end Sp

section SpAux

variable {r : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sp_semilin_aux (A : gsp r F) (σ : F ≃+* F) (α : MulAut (StatedProj (StatedSp r F)))
    (hα : α = conjAut r F A * fieldAut r F σ) :
    ∃ s : Equiv.Perm (Fin r ⊕ Fin r → F), s ∈ semilinGroup F (Fin r ⊕ Fin r → F) ∧
      SemiIso (spForm r F) s ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) F).subgroupOf (StatedSp r F)))
        (natRep (StatedSp r F)) s α := by
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  obtain ⟨c, hc⟩ := exists_unit_sq_mul_eq_one μ
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c * (A : GL (Fin r ⊕ Fin r) F) :
      GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      (c : F) • ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  refine ⟨semilinMap (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c *
      (A : GL (Fin r ⊕ Fin r) F)) σ, semilinMap_mem _ _, semiIso_semilinMap_sp _ σ ?_,
    induces_of_conj_scalar _ (A : GL (Fin r ⊕ Fin r) F) c σ α fun h => ?_⟩
  · rw [hs, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ,
      smul_smul, smul_smul, hc, one_smul]
  · refine ⟨conjSp r F A (fieldSp r F σ h), ?_, ?_⟩
    · rw [coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]
    · rw [hα]
      rfl

theorem induced_PSp_aux (hr : 3 ≤ r) (α : MulAut (StatedProj (StatedSp r F))) :
    ∃ s : Equiv.Perm (Fin r ⊕ Fin r → F), s ∈ semilinGroup F (Fin r ⊕ Fin r → F) ∧
      SemiIso (spForm r F) s ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) F).subgroupOf (StatedSp r F)))
        (natRep (StatedSp r F)) s α := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) hr
  obtain ⟨A, σ, hα⟩ := hform α
  exact sp_semilin_aux A σ α hα

theorem mem_of_odd_pow_of_index_le_two {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    [E.Normal] (hE : E.index ≤ 2) {g : G} {m : ℕ} (hm : Odd m) (hg : g ^ m = 1) : g ∈ E := by
  have hpos : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : g ^ E.index ∈ E := Subgroup.pow_index_mem E g
  rcases (by omega : E.index = 1 ∨ E.index = 2) with h | h
  · rwa [h, pow_one] at h1
  · rw [h] at h1
    obtain ⟨j, hj⟩ := hm
    have : g = (g ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = m + 1 by omega, pow_succ, hg, one_mul]
    rw [this]
    exact pow_mem h1 _

theorem induced_PSp_two_aux {m : ℕ} (hm : Odd m) (α : MulAut (StatedProj (StatedSp 2 F)))
    (hα : α ^ m = 1) :
    ∃ s : Equiv.Perm (Fin 2 ⊕ Fin 2 → F), s ∈ semilinGroup F (Fin 2 ⊕ Fin 2 → F) ∧
      SemiIso (spForm 2 F) s ∧
      Induces (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)))
        (natRep (StatedSp 2 F)) s α := by
  obtain ⟨hHE, hall, hnormal, hindex⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := F)
  have hmem : α ∈ spSemilinearAutGroup 2 F :=
    mem_of_odd_pow_of_index_le_two _ hindex hm hα
  obtain ⟨A, σ, hAσ⟩ := hall α (by rw [hHE]; exact hmem)
  exact sp_semilin_aux A σ α hAσ

end SpAux

end CFSG.LieType.ChevTwo.OppCl
