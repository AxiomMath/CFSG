module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth

open CFSG.Assembly

@[expose] def RawOddInnField (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I ∨ ∃ i ∈ I, ∃ f ∈ F, φ = i * f

variable {K : Type} [Field K] [Finite K] [CharP K 2]

namespace CLA

open CFSG.StandardType CFSG.StandardType.RecipeFieldOmega
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem exists_innSet_mul_of_congr {R Γ : Type*} [Group R] [Group Γ] (Θ : R ≃* Γ)
    {F : Set (MulAut R)} {φ f : MulAut R} {ι : MulAut Γ} (hι : ι ∈ inner Γ) (hf : f ∈ F)
    (h : MulAut.congr Θ φ = ι * MulAut.congr Θ f) :
    ∃ i ∈ LargeEvenInnSet R, ∃ f ∈ F, φ = i * f := by
  refine ⟨(MulAut.congr Θ).symm ι, (mem_innSet_iff_congr Θ _).2 ?_, f, hf, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact hι
  · apply (MulAut.congr Θ).injective
    rw [map_mul, MulEquiv.apply_symm_apply, h]

theorem rawOddInnField_omegaPlus_of {m : ℕ} (hm : 1 ≤ m) {p M : ℕ} (hpM : Nat.Coprime M p)
    (hdec : ∀ α : MulAut (matrixDerived (coordinateQuadPlus m K)),
      ∃ ι ∈ inner (matrixDerived (coordinateQuadPlus m K)),
        ∃ (y : MulAut (matrixDerived (coordinateQuadPlus m K))) (σ : K ≃+* K),
          y * AutOm.fieldAutP m σ = AutOm.fieldAutP m σ * y ∧ y ^ M = 1 ∧
            α = ι * y * AutOm.fieldAutP m σ) :
    RawOddInnField p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  intro φ hφ
  right
  have hS : MulAut.congr (plusEquiv hm) φ ∈
      inner (matrixDerived (coordinateQuadPlus m K)) ⊔ (AutOm.fieldAutP m).range := by
    obtain ⟨ι, hι, y, σ, hyσ, hyM, hα⟩ := hdec (MulAut.congr (plusEquiv hm) φ)
    refine RecipeFieldOmega.mem_of_pow_mem_of_coprime _ (a := M) (N := p) ?_ ?_ hpM
    · obtain ⟨ι', hι', h⟩ := RecipeFieldOmega.exists_pow_eq_mul_pow (inner _) hι hyσ M
      rw [hα, h, hyM, mul_one, ← map_pow]
      exact Subgroup.mul_mem_sup hι' ⟨_, rfl⟩
    · rw [← map_pow, hφ, map_one]
  obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hs⟩ := Subgroup.mem_sup_of_normal_left.1 hS
  obtain ⟨g, hg, hgσ⟩ := exists_mem_field_congr_plusEquiv hm σ
  refine exists_innSet_mul_of_congr (plusEquiv hm) hι hg ?_
  rw [hgσ]
  exact hs.symm

end CLA

open CFSG.StandardType CFSG.StandardType.RecipeFieldOmega

theorem rawOddInnField_omegaPlus {m : ℕ} (hm5 : 5 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    RawOddInnField p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  have hm : 1 ≤ m := by omega
  refine CLA.rawOddInnField_omegaPlus_of hm (M := 2)
    (Nat.coprime_two_left.2 (hp.odd_of_ne_two hp2)) fun α => ?_
  obtain ⟨ι, hι, c, hc, hα⟩ := AutOm.exists_inner_mul_plusCompl hm5 α
  obtain ⟨y, hy, σ, rfl⟩ := exists_eq_mul_fieldAutP_of_mem_plusCompl hm hc
  refine ⟨ι, hι, y, σ, ?_, ?_, by rw [hα, mul_assoc]⟩
  · rcases hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP hm σ
  · rcases hy with rfl | rfl
    · exact one_pow 2
    · rw [sq]
      exact AutOm.plusRefl_mul_self hm

theorem rawOddInnField_omegaPlusFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    RawOddInnField p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  have h14 : 1 ≤ 4 := by norm_num
  have hcop : Nat.Coprime 6 p := by
    rw [show 6 = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
    exact ⟨(Nat.coprime_primes Nat.prime_two hp).2 hp2.symm,
      (Nat.coprime_primes Nat.prime_three hp).2 hp3.symm⟩
  obtain ⟨θ, h3, hρθ, hφθ, hgen, -, -⟩ := plusFourTrialityInput_holds K
  refine CLA.rawOddInnField_omegaPlus_of h14 hcop fun α => ?_
  obtain ⟨ι, hι, k, c, hc, hα⟩ := hgen α
  obtain ⟨y, hy, σ, rfl⟩ := exists_eq_mul_fieldAutP_of_mem_plusCompl h14 hc
  have hyc : y * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * y := by
    rcases hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP h14 σ
  refine ⟨ι, hι, θ ^ k * y, σ, ?_, ?_, by rw [hα]; simp only [mul_assoc]⟩
  · rw [mul_assoc, hyc, ← mul_assoc, ← AutOm.fieldAutP_mul_pow hφθ σ k, mul_assoc]
  · rcases hy with rfl | rfl
    · rw [mul_one, ← pow_mul, show k * 6 = 3 * (2 * k) by ring, pow_mul, h3, one_pow]
    · have h2 : (θ ^ k * AutOm.plusRefl h14) ^ 2 = 1 := by
        rw [sq, mul_assoc, ← mul_assoc (AutOm.plusRefl h14),
          AutOm.plusRefl_mul_pow le_rfl h3 hρθ k, mul_assoc, AutOm.plusRefl_mul_self,
          mul_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, h3, one_pow]
      rw [show 6 = 2 * 3 by norm_num, pow_mul, h2, one_pow]

theorem rawOddInnField_omegaMinus {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f) (p : ℕ) :
    RawOddInnField p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))
      (LargeEvenInnSet _)
      (LargeEvenPhiQ (n - 1) b c
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))) := by
  intro φ _
  right
  obtain ⟨ι, hι, k, hk⟩ :=
    AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf (MulAut.congr (minusEquiv hn4 b c) φ)
  obtain ⟨g, hg, hgk⟩ := exists_mem_phi_congr_minusEquiv hn4 hirr k
  refine CLA.exists_innSet_mul_of_congr (minusEquiv hn4 b c) hι hg ?_
  rw [hgk]
  exact hk

end CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth
