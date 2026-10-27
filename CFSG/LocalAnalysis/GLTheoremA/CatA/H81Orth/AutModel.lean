module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Aut
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Matrix Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.RankThree.PartOne QuadraticMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] noncomputable def semilinMap (A : GL ι F) (φ : F ≃+* F) : (ι → F) ≃+ (ι → F) where
  toFun v := (A : Matrix ι ι F) *ᵥ fun i => φ (v i)
  invFun w := fun i => φ.symm ((((A⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ w) i)
  left_inv v := by
    funext i
    simp [Matrix.mulVec_mulVec]
  right_inv w := by
    simp [Matrix.mulVec_mulVec]
  map_add' v w := by
    simp only [Pi.add_apply, map_add]
    exact Matrix.mulVec_add _ _ _

theorem semilinMap_apply (A : GL ι F) (φ : F ≃+* F) (v : ι → F) :
    semilinMap A φ v = (A : Matrix ι ι F) *ᵥ fun i => φ (v i) := rfl

theorem semilinMap_smul (A : GL ι F) (φ : F ≃+* F) (c : F) (v : ι → F) :
    semilinMap A φ (c • v) = φ c • semilinMap A φ v := by
  rw [semilinMap_apply, semilinMap_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem statedProjOrthEquiv_symm_projT {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F}
    (hQ : ⇑Q = Q₀) (g : ↥(orthDerived Q)) :
    (statedProjOrthEquiv hQ).symm (projT Q g) =
      QuotientGroup.mk ((statedOmegaOrthEquiv hQ).symm g) := by
  apply (statedProjOrthEquiv hQ).injective
  rw [MulEquiv.apply_symm_apply, statedProjOrthEquiv, QuotientGroup.congr_mk,
    MulEquiv.apply_symm_apply]
  rfl

theorem toLinEquiv_statedOmegaOrthEquiv_symm {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F}
    (hQ : ⇑Q = Q₀) (g : ↥(orthDerived Q)) :
    toLinEquiv ι F ((statedOmegaOrthEquiv hQ).symm g : GL ι F) = (g : (ι → F) ≃ₗ[F] (ι → F)) := by
  rw [← coe_statedOmegaOrthEquiv hQ, MulEquiv.apply_symm_apply]

theorem induced_of_similarity {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ : ⇑Q = Q₀)
    (β : MulAut (StatedProj (StatedOmega Q₀))) (A : GL ι F) (φ : F ≃+* F)
    (hβ : ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
      (y : GL ι F) = A * glFieldEquiv ι φ (x : GL ι F) * A⁻¹ ∧
        β (QuotientGroup.mk x) = QuotientGroup.mk y) (g : ↥(orthDerived Q)) :
    ∃ g' : ↥(orthDerived Q), (∀ v, (g' : (ι → F) ≃ₗ[F] (ι → F)) (semilinMap A φ v) =
        semilinMap A φ ((g : (ι → F) ≃ₗ[F] (ι → F)) v)) ∧
      MulAut.congr (statedProjOrthEquiv hQ) β (projT Q g) = projT Q g' := by
  set e := statedProjOrthEquiv hQ with he
  set x := (statedOmegaOrthEquiv hQ).symm g with hx
  obtain ⟨y, hy, hβy⟩ := hβ x
  have hg : (g : (ι → F) ≃ₗ[F] (ι → F)) = toLinEquiv ι F (x : GL ι F) := by
    rw [← coe_statedOmegaOrthEquiv hQ, hx, MulEquiv.apply_symm_apply]
  refine ⟨statedOmegaOrthEquiv hQ y, fun v => ?_, ?_⟩
  · rw [coe_statedOmegaOrthEquiv, toLinEquiv_apply, hy, hg, toLinEquiv_apply, semilinMap_apply,
      semilinMap_apply, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, mul_assoc,
      Units.inv_mul, mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec φ.toRingHom _ _ i).symm
  · have h1 : e.symm (projT Q g) = QuotientGroup.mk x := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, he, statedProjOrthEquiv, QuotientGroup.congr_mk, hx,
        MulEquiv.apply_symm_apply]
      rfl
    show e (β (e.symm (projT Q g))) = _
    rw [h1, hβy, he, statedProjOrthEquiv, QuotientGroup.congr_mk]
    rfl

variable [Finite F]

theorem exists_eq_conj_of_stated {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F}
    (hQ : ⇑Q = Q₀) (hnd : (polarBilin Q).Nondegenerate) (hF : ringChar F ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {y : ↥(orthDerived Q)}
    (hy : OddOrderIsometry Q p (y : (ι → F) ≃ₗ[F] (ι → F)))
    (hR : finrank F (othersSpace (y : (ι → F) ≃ₗ[F] (ι → F)).toLinearMap (X - 1)) = 2)
    (hW : 5 ≤ finrank F (fixedSpace (y : (ι → F) ≃ₗ[F] (ι → F))))
    (α : MulAut (ProjOrthDerived Q)) (hα : α ^ p = 1)
    (hαJ : ∀ j ∈ fixedComponentImage Q (y : (ι → F) ≃ₗ[F] (ι → F)), α j = j)
    (hsim : ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v : ι → F, Q ((A : Matrix ι ι F) *ᵥ fun i => φ (v i)) = μ * φ (Q v)) ∧
      ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
        (y : GL ι F) = A * glFieldEquiv ι φ (x : GL ι F) * A⁻¹ ∧
          MulAut.congr (statedProjOrthEquiv hQ).symm α (QuotientGroup.mk x) =
            QuotientGroup.mk y) :
    ∃ k : ℤ, α = MulAut.conj (projT Q y ^ k) := by
  obtain ⟨A, φ, μ, hQA, hβ⟩ := hsim
  refine exists_eq_conj_of_similitude hnd hF hp hp2 hy hR hW α hα hαJ (semilinMap A φ) φ μ
    (semilinMap_smul A φ) (fun v => hQA v) fun g => ?_
  obtain ⟨g', hg', hα'⟩ := induced_of_similarity hQ _ A φ hβ g
  refine ⟨g', hg', ?_⟩
  rw [← hα']
  simp

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
