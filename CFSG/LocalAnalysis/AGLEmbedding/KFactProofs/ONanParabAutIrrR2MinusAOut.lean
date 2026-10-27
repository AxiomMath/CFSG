module

public import CFSG.RankThree.PartOne.AUTSL.OmegaOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2MinusATail

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ComponentClassification
  CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.AUTSL Matrix

section Gen

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mn_aut_decomp (n : ℕ) (hn4 : 4 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    ∀ α : MulAut (matrixDerived (Qm n hn4 b c)),
    ∃ k : ℕ, (conjAct (Qm n hn4 b c) (frobPair n (by omega) b c
        (ne_zero_of_irreducible_tail b c hirr)) ^ k)⁻¹ * α ∈
      OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) := by
  have hn : 1 ≤ n := by omega
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hQ : ∃ v, Qm n hn4 b c v ≠ 0 := exists_ne_zero_of_polar_nondegenerate (by omega) _ hnd
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c
    hirr
  have hb : b ≠ 0 := ne_zero_of_irreducible_tail b c hirr
  obtain ⟨A, hA, hAΓ, hTf⟩ := frobPair_pow_f_eq_inclusion n hn b c hb hf hirr hnd hT
  set T := frobPair n hn b c hb with hTdef
  set Q := Qm n hn4 b c with hQdef
  have hτf : (conjAct Q T) ^ f = conjAct Q (matrixIsometryInclusion Q ⟨A, hA⟩) := by
    rw [← map_pow, hTf]
  have key4 : ∀ (w : Fin (2 * n) → K) (hw : Q w ≠ 0),
      ∃ ν ∈ OuterAutomorphisms.inner (matrixDerived Q), reflAut Q w hw = ν * (conjAct Q T) ^ f := by
    intro w hw
    have hR := reflMat_mem_isometries (Q := Q) w hw
    have hAR : A * reflMat Q w hw ∈ matrixDerived Q := by
      rcases mem_or_mul_reflMat_mem hnd hT hA w hw with h | h
      · exact absurd h hAΓ
      · exact h
    refine ⟨(conjAct Q (matrixIsometryInclusion Q ⟨A * reflMat Q w hw, mul_mem hA hR⟩))⁻¹,
      inv_mem (conjAct_inclusion_mem_inner _ hAR), ?_⟩
    have hιA : matrixIsometryInclusion Q ⟨A, hA⟩ =
        matrixIsometryInclusion Q ⟨A * reflMat Q w hw, mul_mem hA hR⟩ *
          matrixIsometryInclusion Q ⟨reflMat Q w hw, hR⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      change A = A * reflMat Q w hw * reflMat Q w hw
      rw [mul_assoc, reflMat_mul_self, mul_one]
    rw [hτf, hιA, map_mul, inv_mul_cancel_left]
    rfl
  have hgen : ∀ α : MulAut (matrixDerived Q), ∃ k : ℕ,
      ((conjAct Q T) ^ k)⁻¹ * α ∈ OuterAutomorphisms.inner (matrixDerived Q) := by
    intro α
    obtain ⟨g, rfl⟩ := exists_pair_of_aut hQ htop α
    obtain ⟨i, hi⟩ := exists_frob_pow g.val.right
    let ℓ : similarityPairs Q := (T ^ i)⁻¹ * g
    have hℓ : ℓ.val.right = 1 := by
      have hfT : fieldProjection Q T = frobeniusEquiv K 2 := rfl
      have : fieldProjection Q ℓ = 1 := by
        simp only [ℓ, map_mul, map_inv, map_pow, hfT, fieldProjection_apply, hi, inv_mul_cancel]
      exact this
    obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.OutStructure.exists_isometry_of_linear Q hQ
      ⟨ℓ, (mem_linearSimilarityPairs_iff Q ℓ).2 hℓ⟩
    have hℓB : conjAct Q ℓ = conjAct Q (matrixIsometryInclusion Q B) :=
      conjAct_eq_of_isometry hB
    have hg : g = T ^ i * ℓ := (mul_inv_cancel_left (T ^ i) g).symm
    have hα : conjAct Q g = (conjAct Q T) ^ i * conjAct Q (matrixIsometryInclusion Q B) := by
      rw [← hℓB, ← map_pow, ← map_mul, ← hg]
    obtain ⟨w₁, hw₁⟩ := hQ
    rcases mem_or_mul_reflMat_mem hnd hT B.2 w₁ hw₁ with hBΓ | hBΓ
    · refine ⟨i, ?_⟩
      rw [hα, inv_mul_cancel_left]
      exact conjAct_inclusion_mem_inner B hBΓ
    · refine ⟨i + f, ?_⟩
      have hR := reflMat_mem_isometries (Q := Q) w₁ hw₁
      obtain ⟨ν, hν, hrefl⟩ := key4 w₁ hw₁
      have hιB : matrixIsometryInclusion Q B =
          matrixIsometryInclusion Q ⟨B.val * reflMat Q w₁ hw₁, mul_mem B.2 hR⟩ *
            matrixIsometryInclusion Q ⟨reflMat Q w₁ hw₁, hR⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        change B.val = B.val * reflMat Q w₁ hw₁ * reflMat Q w₁ hw₁
        rw [mul_assoc, reflMat_mul_self, mul_one]
      have hn₁ := conjAct_inclusion_mem_inner
        (Q := Q) ⟨B.val * reflMat Q w₁ hw₁, mul_mem B.2 hR⟩ hBΓ
      have hcalc : ((conjAct Q T) ^ (i + f))⁻¹ * conjAct Q g =
          ((conjAct Q T) ^ f)⁻¹ *
            (conjAct Q (matrixIsometryInclusion Q ⟨B.val * reflMat Q w₁ hw₁, mul_mem B.2 hR⟩) *
              ν) * (((conjAct Q T) ^ f)⁻¹)⁻¹ := by
        rw [hα, hιB, map_mul]
        change _ = _ * (conjAct Q (matrixIsometryInclusion Q ⟨B.val * reflMat Q w₁ hw₁,
          mul_mem B.2 hR⟩) * _) * _
        have hr : conjAct Q (matrixIsometryInclusion Q ⟨reflMat Q w₁ hw₁, hR⟩) =
            ν * (conjAct Q T) ^ f := hrefl
        rw [hr, pow_add, _root_.mul_inv_rev, inv_inv]
        simp only [mul_assoc, inv_mul_cancel_left]
      rw [hcalc]
      exact (OuterAutomorphisms.inner_normal _).conj_mem _ (mul_mem hn₁ hν) _
  exact hgen

end Gen

section Transport

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def mnPhi (n : ℕ) (hn4 : 4 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    matrixDerived (Qm n hn4 b c) ≃*
      orthElementaryGroup (quadTail (n - 1) (minusTailForm K b c)) :=
  (MulEquiv.subgroupCongr (matrixDerived_eq_statedOmega (Qm n hn4 b c))).trans
    (tailOmegaEquiv (mnIso n (by omega) b c) rfl (commutator_coordinateQuadMinus n K b c hn4 hirr))

omit [CharP K 2] in
theorem mnPhi_apply (n : ℕ) (hn4 : 4 ≤ n) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (G : matrixDerived (Qm n hn4 b c)) (x : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) :
    (mnPhi n hn4 b c hirr G).val x =
      (mnIso n (by omega) b c).symm
        (((G.val : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *ᵥ
          (mnIso n (by omega) b c x)) := by
  unfold mnPhi
  rw [MulEquiv.trans_apply, tailOmegaEquiv_apply]
  rfl

theorem mnPhi_conjAct (n : ℕ) (hn4 : 4 ≤ n) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (G : matrixDerived (Qm n hn4 b c)) (y : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) :
    (mnPhi n hn4 b c hirr (conjAct (Qm n hn4 b c) (frobPair n (by omega) b c
        (ne_zero_of_irreducible_tail b c hirr)) G)).val
      (mnFrob n (by omega) b c (ne_zero_of_irreducible_tail b c hirr) y) =
    mnFrob n (by omega) b c (ne_zero_of_irreducible_tail b c hirr)
      ((mnPhi n hn4 b c hirr G).val y) := by
  have hn : 1 ≤ n := by omega
  have hb := ne_zero_of_irreducible_tail b c hirr
  set Tp := frobPair n hn b c hb with hTp
  rw [mnPhi_apply, mnPhi_apply]
  have hFr : ∀ w, mnFrob n hn b c hb ((mnIso n hn b c).symm w) =
      (mnIso n hn b c).symm (coordinateSemilinearMap (frobElt n hn b c hb) w) := by
    intro w
    have h1 := mnIso_mnFrob n hn b c hb ((mnIso n hn b c).symm w)
    simpa using congrArg (mnIso n hn b c).symm h1
  rw [hFr, mnIso_mnFrob]
  congr 1
  set w := mnIso n hn b c y with hw
  rw [conjAct_apply, matrixDerivedConjugation_val]
  have key := matrixConjugation_vector (frobElt n hn b c hb) G.val
    (coordinateSemilinearMap (frobElt n hn b c hb) w)
  rw [AddEquiv.symm_apply_apply] at key
  exact key

end Transport

end CFSG.AGLEmbedding.ParabAutIrr
