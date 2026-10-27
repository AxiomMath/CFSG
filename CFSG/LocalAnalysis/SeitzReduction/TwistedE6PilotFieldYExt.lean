module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYModel
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Extension

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem coordinateQuadMinus_glIncl (hn : 1 ≤ n) (b c : k)
    {g : coordinateSemilinearGroup (2 * n) k} {μ : kˣ}
    (hμ : ∀ v, coordinateQuadMinus n k hn b c (coordinateSemilinearMap g v) =
      (μ : k) * g.right (coordinateQuadMinus n k hn b c v))
    {ρ' : K ≃+* K} (hρ' : ∀ x : k, ρ' (x : K) = ((g.right x : k) : K)) (w : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn (b : K) (c : K) ((glIncl k g.left).val *ᵥ w) =
      ((μ : k) : K) * coordinateQuadMinus n K hn (ρ' b) (ρ' c) w := by
  have h := eq_of_agree k
    ((coordinateQuadMinus n K hn (b : K) (c : K)).comp
      (matrixLinearEquiv (glIncl k g.left)).toLinearMap)
    (((μ : k) : K) • coordinateQuadMinus n K hn (ρ' b) (ρ' c)) (fun v => by
      rw [QuadraticMap.comp_apply, _root_.smul_apply]
      change coordinateQuadMinus n K hn (b : K) (c : K)
        (matrixLinearEquiv (glIncl k g.left) (vecIncl k v)) = _
      rw [matrixLinearEquiv_apply, mulVec_vecIncl, isExtension_coordinateQuadMinus k hn b c,
        hρ' b, hρ' c, isExtension_coordinateQuadMinus k hn (g.right b) (g.right c), smul_eq_mul,
        ← Subfield.coe_mul]
      congr 1
      have hv : coordinateFieldMap (2 * n) g.right
          (coordinateFieldMap (2 * n) g.right.symm v) = v := by
        funext i
        simp [coordinateFieldMap_apply]
      have h1 := hμ (coordinateFieldMap (2 * n) g.right.symm v)
      rw [coordinateSemilinearMap_apply] at h1
      change coordinateQuadMinus n k hn b c (g.left.val *ᵥ
        coordinateFieldMap (2 * n) g.right (coordinateFieldMap (2 * n) g.right.symm v)) = _ at h1
      rw [hv] at h1
      rw [h1]
      congr 1
      have h2 := coordinateQuadMinus_fieldMap hn g.right b c
        (coordinateFieldMap (2 * n) g.right.symm v)
      rw [hv] at h2
      exact h2.symm)
  have h1 := congrArg (fun F : QuadraticForm K (Fin (2 * n) → K) => F w) h
  simpa only [QuadraticMap.comp_apply, _root_.smul_apply, smul_eq_mul,
    LinearEquiv.coe_coe, matrixLinearEquiv_apply] using h1

theorem autExtensionComm_incl_minus (hn : 4 ≤ n) {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (hQσ : ∀ v, coordinateQuadMinus n K (by omega) (b : K) (c : K)
      (coordinateFieldMap (2 * n) σ v) = σ (coordinateQuadMinus n K (by omega) (b : K) (c : K) v)) :
    AutExtensionComm (incl k (isExtension_coordinateQuadMinus k (by omega) b c))
      (fieldAutT (coordinateQuadMinus n K (by omega) (b : K) (c : K)) σ hQσ) := by
  intro δ
  have hn1 : 1 ≤ n := by omega
  obtain ⟨f₀, hf₀, hk₀⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  have hst : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n k b c))) .POmegaMinus
      n 2 f₀ := ⟨⟨Nat.prime_two, hf₀, hn⟩, k, inferInstance, inferInstance, hk₀, b, c, hirr,
        ⟨MulEquiv.refl _⟩⟩
  have himage : matrixProjectiveImage (coordinateQuadMinus n k hn1 b c) = ⊤ :=
    semilinearImageEqTop _ .POmegaMinus (Or.inr rfl) hst hn1 k hk₀ b c hirr (MulEquiv.refl _)
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ δ).mp (himage ▸ Subgroup.mem_top δ)
  obtain ⟨ρ', hρ'⟩ := F4Pilot.exists_ringEquiv_comp_eq k.subtype g.val.right
  obtain ⟨μ, hμ⟩ := g.property
  let g' : coordinateSemilinearGroup (2 * n) K := ⟨glIncl k g.val.left, ρ'⟩
  have hg' : g' ∈ similarityPairs (coordinateQuadMinus n K hn1 (b : K) (c : K)) := by
    refine ⟨Units.map k.subtype.toMonoidHom μ, fun w => ?_⟩
    rw [coordinateSemilinearMap_apply]
    change coordinateQuadMinus n K hn1 (b : K) (c : K)
        ((glIncl k g.val.left).val *ᵥ fun i => ρ' (w i)) =
      ((μ : k) : K) * ρ' (coordinateQuadMinus n K hn1 (b : K) (c : K) w)
    rw [coordinateQuadMinus_glIncl hn1 b c hμ (fun x => hρ' x),
      ← coordinateQuadMinus_fieldMap hn1 ρ' (b : K) (c : K) w]
    rfl
  refine ⟨matrixProjectiveConjugation _ ⟨g', hg'⟩, fun x => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective _ x
    rw [← hg, matrixProjectiveConjugation_mk, incl_mk, incl_mk, matrixProjectiveConjugation_mk]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, inclHom_val, inclHom_val, matrixDerivedConjugation_val]
    have hent : glFieldAut (Fin (2 * n)) K ρ' (glIncl k y.val) =
        glIncl k (glFieldAut (Fin (2 * n)) k g.val.right y.val) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      change ρ' (k.subtype (y.val.val i j)) = k.subtype (g.val.right (y.val.val i j))
      exact hρ' _
    change glIncl k g.val.left * glFieldAut (Fin (2 * n)) K ρ' (glIncl k y.val) *
        (glIncl k g.val.left)⁻¹ = _
    rw [hent, map_mul, map_mul, map_inv]
  · have hpair : (⟨g', hg'⟩ : similarityPairs (coordinateQuadMinus n K hn1 (b : K) (c : K))) *
        fieldPair _ σ hQσ = fieldPair _ σ hQσ * ⟨g', hg'⟩ := by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · change glIncl k g.val.left * glFieldAut (Fin (2 * n)) K ρ' 1 =
          1 * glFieldAut (Fin (2 * n)) K σ (glIncl k g.val.left)
        rw [map_one, mul_one, one_mul, glFieldAut_glIncl k hσk]
      · change ρ' * σ = σ * ρ'
        exact ringAut_commute ρ' σ
    change matrixProjectiveConjugationHom _ ⟨g', hg'⟩ *
        matrixProjectiveConjugationHom _ (fieldPair _ σ hQσ) =
      matrixProjectiveConjugationHom _ (fieldPair _ σ hQσ) *
        matrixProjectiveConjugationHom _ ⟨g', hg'⟩
    rw [← map_mul, ← map_mul, hpair]

end Extension

end CFSG.SeitzReduction.TwistedE6Pilot
