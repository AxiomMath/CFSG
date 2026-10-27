module

public import CFSG.ClassicalInvolution.Asc77.AscCHN4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace CHN

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  (aut_fix_blocks_zero aut_fix_blocks_one)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem aut_fix_blocks_z [Finite F] (h2 : (2 : F) ≠ 0) (α : MulAut (projectiveSL 4 F))
    (hfix0 : ∀ r ∈ (blk F 0).range, α (proj 4 F r) = proj 4 F r)
    (hfix2 : ∀ r ∈ (blk F 2).range, α (proj 4 F r) = proj 4 F r) :
    α (proj 4 F (blk F 1 (-1))) = proj 4 F (blk F 1 (-1)) := by
  obtain ⟨-, hform⟩ := LinearFlag.automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  have hAAi : (A : Matrix (Fin 4) (Fin 4) F) *
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    subst hαeq
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 A σ hfix0 hfix2
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one, conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation]
    have hcomm : (A : Matrix (Fin 4) (Fin 4) F) *
        ((blk F 1 (-1) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        ((blk F 1 (-1) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
          (A : Matrix (Fin 4) (Fin 4) F) := by
      rw [hM, coe_blk_neg_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [negBlock_eq_diagonal, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [hcomm, Matrix.mul_assoc, hAAi, Matrix.mul_one]
  · rw [pow_one] at hαeq
    subst hαeq
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := aut_fix_blocks_one h2 A σ hfix0 hfix2
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one]
    show conjAut 4 F A (dualAut 4 F (proj 4 F (blk F 1 (-1)))) = _
    rw [dualAut_proj, conjAut_proj]
    have hinv : (blk F 1 (-1))⁻¹ = blk F 1 (-1) := by
      rw [← map_inv]
      congr 1
      simp
    have hz : ((blk F 1 (-1))⁻¹).transpose = blk F 1 (-1) := by
      rw [hinv]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_transpose, coe_blk_neg_one, negBlock_eq_diagonal,
        Matrix.diagonal_transpose]
    rw [hz]
    have hc : slConjugation 4 F A (blk F 1 (-1)) =
        blk F 1 (-1) * (blk F 0 (-1) * blk F 2 (-1)) := by
      apply Subtype.ext
      rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        coe_blk_neg_one, coe_blk_neg_one, coe_blk_neg_one]
      have hanti : (A : Matrix (Fin 4) (Fin 4) F) * negBlock F 4 1 =
          -(negBlock F 4 1 * (A : Matrix (Fin 4) (Fin 4) F)) := by
        rw [hM, negBlock_eq_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.diagonal_apply]
      show (A : Matrix (Fin 4) (Fin 4) F) * negBlock F 4 1 *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
      rw [hanti, Matrix.neg_mul, Matrix.mul_assoc, hAAi, Matrix.mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [negBlock_eq_diagonal, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [hc, map_mul]
    have hcen : proj 4 F (blk F 0 (-1) * blk F 2 (-1)) = 1 := by
      rw [← MonoidHom.mem_ker, ker_proj, scalars_eq_center]
      exact blk0_mul_blk2_mem_center
    rw [hcen, mul_one]


@[expose] def conjRange {G : Type} [Group G] (R : Subgroup G) (a : G)
    (h : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (h' : ∀ r ∈ R, a⁻¹ * r * a ∈ R) : R ≃* R where
  toFun r := ⟨a * r * a⁻¹, h r r.2⟩
  invFun r := ⟨a⁻¹ * r * a, h' r r.2⟩
  left_inv r := Subtype.ext (by simp [mul_assoc])
  right_inv r := Subtype.ext (by simp [mul_assoc])
  map_mul' r s := Subtype.ext (by simp [mul_assoc])

theorem exists_aut_of_normalizes {G : Type} [Group G] (ψ : SL(4, F) →* G)
    (hker : ψ.ker = Subgroup.center SL(4, F)) (a : G)
    (hn : ∀ x : SL(4, F), ∃ y, ψ y = a * ψ x * a⁻¹)
    (hn' : ∀ x : SL(4, F), ∃ y, ψ y = a⁻¹ * ψ x * a) :
    ∃ ρ : MulAut (projectiveSL 4 F), ∀ x : SL(4, F), ∃ y : SL(4, F),
      ρ (proj 4 F x) = proj 4 F y ∧ ψ y = a * ψ x * a⁻¹ := by
  classical
  have hle : scalars 4 F ≤ ψ.ker := by
    rw [hker, scalars_eq_center]
  let ι : projectiveSL 4 F →* G := QuotientGroup.lift (scalars 4 F) ψ hle
  have hι : ∀ x, ι (proj 4 F x) = ψ x := fun x => rfl
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := proj_surjective 4 F q
    rw [MonoidHom.mem_ker, hι, ← MonoidHom.mem_ker, hker, ← scalars_eq_center,
      ← ker_proj] at hq
    rw [Subgroup.mem_bot]
    exact hq
  have hnorm : ∀ r ∈ ι.range, a * r * a⁻¹ ∈ ι.range := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := proj_surjective 4 F q
    obtain ⟨y, hy⟩ := hn x
    exact ⟨proj 4 F y, by rw [hι, hy, hι]⟩
  have hnorm' : ∀ r ∈ ι.range, a⁻¹ * r * a ∈ ι.range := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := proj_surjective 4 F q
    obtain ⟨y, hy⟩ := hn' x
    exact ⟨proj 4 F y, by rw [hι, hy, hι]⟩
  let e : projectiveSL 4 F ≃* ι.range := MonoidHom.ofInjective hιinj
  let ρ : MulAut (projectiveSL 4 F) := e.trans ((conjRange ι.range a hnorm hnorm').trans e.symm)
  have hρ : ∀ q, ι (ρ q) = a * ι q * a⁻¹ := by
    intro q
    have h1 : e (ρ q) = conjRange ι.range a hnorm hnorm' (e q) := by
      simp [ρ]
    have h2 := congrArg (fun r : ι.range => (r : G)) h1
    exact h2
  refine ⟨ρ, fun x => ?_⟩
  obtain ⟨y, hy⟩ := hn x
  refine ⟨y, hιinj ?_, hy⟩
  rw [hρ, hι, hι, hy]


theorem proj_eq_iff {G : Type} [Group G] (ψ : SL(4, F) →* G)
    (hker : ψ.ker = Subgroup.center SL(4, F)) (x y : SL(4, F)) :
    proj 4 F x = proj 4 F y ↔ ψ x = ψ y := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, ker_proj, scalars_eq_center,
    ← hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

theorem fix_z_of_centralizes [Finite F] (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F))
    {G : Type} [Group G] (ψ : SL(4, F) →* G) (hker : ψ.ker ≤ Subgroup.center SL(4, F))
    (hψ : ψ (blk F 0 (-1) * blk F 2 (-1)) = 1) (a : G)
    (hn : ∀ x : SL(4, F), ∃ y, ψ y = a * ψ x * a⁻¹)
    (hn' : ∀ x : SL(4, F), ∃ y, ψ y = a⁻¹ * ψ x * a)
    (hc0 : ∀ r ∈ (blk F 0).range, a * ψ r = ψ r * a)
    (hc2 : ∀ r ∈ (blk F 2).range, a * ψ r = ψ r * a) :
    a * ψ (blk F 1 (-1)) = ψ (blk F 1 (-1)) * a := by
  have hker' : ψ.ker = Subgroup.center SL(4, F) :=
    le_antisymm hker (center_le_ker_of_neg_one hneg ψ hψ)
  obtain ⟨ρ, hρ⟩ := exists_aut_of_normalizes ψ hker' a hn hn'
  have hfix : ∀ i : Fin 3, (i = 0 ∨ i = 2) → ∀ r ∈ (blk F i).range,
      ρ (proj 4 F r) = proj 4 F r := by
    intro i hi r hr
    obtain ⟨y, hy1, hy2⟩ := hρ r
    rw [hy1, proj_eq_iff ψ hker', hy2]
    have : a * ψ r = ψ r * a := by
      rcases hi with rfl | rfl
      · exact hc0 r hr
      · exact hc2 r hr
    rw [this]
    group
  have hz := aut_fix_blocks_z h2 ρ (hfix 0 (Or.inl rfl)) (hfix 2 (Or.inr rfl))
  obtain ⟨y, hy1, hy2⟩ := hρ (blk F 1 (-1))
  rw [hy1, proj_eq_iff ψ hker'] at hz
  have h := hy2.symm.trans hz
  rwa [mul_inv_eq_iff_eq_mul] at h

end CHN

end CFSG.ClassicalInvolution.Asc77
