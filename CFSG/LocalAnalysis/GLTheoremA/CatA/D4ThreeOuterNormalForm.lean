module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4GraphReduce
import all CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4GraphReduce


public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S2019
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.HardMathSupport.Dickson.Bal207.D4Graph
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped Pointwise


theorem exists_d4ThreeOuter_normalForm {K : Type} [Field K] [Finite K] {q f : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hK : Nat.card K = q ^ f)
    (t : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (ht3 : t ^ 3 = 1)
    (htE : t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ),
      ε < 3 ∧ ε ≠ 0 ∧ σ ^ 3 = 1 ∧
        MulAut.congr (coordinatePlusWitnessEquiv K (isoAdj K).symm).symm t =
          MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, hf0, pow_zero] at this
    omega
  set Φ : adjointGroup Tag.D4 K ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    coordinatePlusWitnessEquiv K (isoAdj K).symm with hΦ
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    Finite.of_equiv _ Φ.toEquiv
  set α := MulAut.congr Φ.symm t with hαdef
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, ht3, map_one]
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα3
  by_cases hε0 : ε = 0
  ·
    exfalso
    subst hε0
    have hEA : projectivePointFamilyAut (coordinateQuadPlus 4 K) =
        matrixProjectiveImage (coordinateQuadPlus 4 K) := by
      let e0 : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃*
          CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K)) :=
        (statedProjectiveReindexEquiv
          (plusIndexEquiv 4) (CFSG.LieType.Universal.Spin.quadPlus 4 K)
          (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)).symm
      have hm : CFSG.Open.StatedClassicalModel
          (matrixProjectiveDerived (coordinateQuadPlus 4 K)) .POmegaPlus 4 q f :=
        ⟨⟨hq, hf, le_refl 4⟩, K, inferInstance, inferInstance, hK, ⟨e0⟩⟩
      exact coordinate_plus_family_eq_matrixImage hm K hK e0
    set F := projectivePointFamily (coordinateQuadPlus 4 K) with hFdef
    have hE : ∀ γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
        γ ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) → γ • F = F := by
      intro γ hγ
      rw [← hEA, mem_projectivePointFamilyAut_iff] at hγ
      exact hγ
    have hO : ∀ γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
        γ • F = F ∨ γ • F = plusCX 4 K ∨ γ • F = plusCXstar 4 K (by norm_num) := by
      intro γ
      have h1 := coordinate_plus_pointFamily_orbit_subset (K := K) (n := 4) rfl
        (MulAction.mem_orbit F γ)
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
    have htF : t • F ≠ F := by
      intro h1
      apply htE
      rw [← hEA, mem_projectivePointFamilyAut_iff]
      exact h1
    have hinner : ∀ y : matrixProjectiveDerived (coordinateQuadPlus 4 K),
        ∀ γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
          MulAut.conj y • (γ • F) = γ • F := by
      intro y γ
      rw [← mul_smul, S2019.conj_mul_eq_mul_conj, mul_smul,
        hE _ (CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _)]
    have hcongr_conj : ∀ x : adjointGroup Tag.D4 K, MulAut.congr Φ (MulAut.conj x) =
        MulAut.conj (Φ x) := fun x =>
      MulEquiv.ext fun y => by simp [MulAut.congr_apply, MulAut.conj_apply]
    have hαdec : α = MulAut.conj g * exactNormalAut Tag.D4 K a 1 0 *
        entrywiseAdjointAut Tag.D4 σ := by
      rw [hαeq]
      have h0 : d4Graph K 0 = 1 :=
        MulEquiv.ext fun x => Subtype.ext (by rw [coe_d4Graph, pow_zero, one_mul, inv_one,
          mul_one, MulAut.one_apply])
      rw [h0, mul_one, S2019.exactNormalAut_eq_mul_entrywise, mul_assoc]
    have hts : t = MulAut.congr Φ (MulAut.conj g) *
        MulAut.congr Φ (exactNormalAut Tag.D4 K a 1 0) *
          MulAut.congr Φ (entrywiseAdjointAut Tag.D4 σ) := by
      have htα : t = MulAut.congr Φ α :=
        MulEquiv.ext fun x => by simp [hαdef, MulAut.congr_apply]
      rw [htα, hαdec, map_mul, map_mul]
    refine false_of_three_orbit hO ht3 htF (fun γ => ?_) (fun γ => ?_)
      (hE _ (congr_entrywiseAdjointAut_mem σ)) ?_ hts
    · rw [hcongr_conj]
      exact hinner _ γ
    · rw [← map_mul, S2019.normalAut_one_sq, hcongr_conj]
      exact hinner _ γ
    · rw [← map_pow, ← entrywiseAdjointAut_pow, hσ3, entrywiseAdjointAut_one, map_one]
  · exact ⟨g, a, σ, ε, hε, hε0, hσ3, hαeq⟩

end CFSG.LocalAnalysis.GLTheoremA

end
