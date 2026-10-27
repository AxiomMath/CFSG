module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviCore
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace suzukiLetter suzukiLetter_eq_a_iff
  isConj_iff_suzukiLetter_eq even_finrank_commSpace_of_forall_eq_zero)

variable {K : Type} [Field K] {d : ℕ}

theorem matrixRank_sub_one_eq_finrank_sNil (s : GL (Fin d) K) :
    (((s : Matrix (Fin d) (Fin d) K)) - 1).rank = finrank K (LinearMap.range (sNil s)) := by
  have h : (((s : Matrix (Fin d) (Fin d) K)) - 1).mulVecLin = sNil s :=
    LinearMap.ext fun v => by
      rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sNil_apply,
        matrixLinearEquiv_apply]
  rw [Matrix.rank, h]

theorem matrixLinearEquiv_mul_self {s : GL (Fin d) K} (hss : s * s = 1) :
    matrixLinearEquiv s * matrixLinearEquiv s = 1 := by
  rw [← matrixLinearEquiv_mul, hss]
  refine LinearEquiv.ext fun v => ?_
  rw [matrixLinearEquiv_apply]
  simp

variable [CharP K 2]

theorem even_finrank_range_sNil_of_typeA {Q : QuadraticForm K (Fin d → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {s : matrixIsometries Q} (hss : s * s = 1)
    (hA : ∀ w ∈ LinearMap.range (sNil s.val), Q w = 0) :
    Even (finrank K (LinearMap.range (sNil s.val))) :=
  even_finrank_commSpace_of_forall_eq_zero hQ s.2
    (matrixLinearEquiv_mul_self (congrArg Subtype.val hss)) hA

omit [CharP K 2] in
theorem orderOf_matrixLinearEquiv_eq_two {s : GL (Fin d) K} (hss : s * s = 1)
    (hpos : finrank K (LinearMap.range (sNil s)) ≠ 0) : orderOf (matrixLinearEquiv s) = 2 := by
  refine orderOf_eq_prime (by rw [pow_two]; exact matrixLinearEquiv_mul_self hss) fun h1 => hpos ?_
  have h0 : sNil s = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [sNil_apply, h1]
    simp
  rw [h0, LinearMap.range_zero, finrank_bot]

variable [Finite K]

theorem exists_conj_eq_of_typeA {Q : QuadraticForm K (Fin d → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {s s₀ : matrixIsometries Q}
    (hss : s * s = 1) (hs₀ : s₀ * s₀ = 1)
    (hA : ∀ w ∈ LinearMap.range (sNil s.val), Q w = 0)
    (hA₀ : ∀ w ∈ LinearMap.range (sNil s₀.val), Q w = 0)
    (hdim : finrank K (LinearMap.range (sNil s.val)) = finrank K (LinearMap.range (sNil s₀.val)))
    (hpos : finrank K (LinearMap.range (sNil s₀.val)) ≠ 0) :
    ∃ a : matrixIsometries Q, s = a * s₀ * a⁻¹ := by
  have hss' := congrArg Subtype.val hss
  have hs₀' := congrArg Subtype.val hs₀
  have ht2 := orderOf_matrixLinearEquiv_eq_two hs₀' hpos
  have hs2 := orderOf_matrixLinearEquiv_eq_two hss' (hdim ▸ hpos)
  have hlet : suzukiLetter Q (matrixLinearEquiv s.val) =
      suzukiLetter Q (matrixLinearEquiv s₀.val) := by
    rw [suzukiLetter_eq_a_iff.mpr ⟨even_finrank_range_sNil_of_typeA hQ hss hA, hA⟩,
      suzukiLetter_eq_a_iff.mpr ⟨even_finrank_range_sNil_of_typeA hQ hs₀ hA₀, hA₀⟩]
  obtain ⟨g, hgO, hg⟩ := (isConj_iff_suzukiLetter_eq hQ s₀.2 ht2 s.2 hs2).mpr ⟨hlet, hdim⟩
  have ha : matrixLinearIso.symm g ∈ matrixIsometries Q := by
    change matrixLinearIso (matrixLinearIso.symm g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rwa [MulEquiv.apply_symm_apply]
  refine ⟨⟨_, ha⟩, Subtype.ext (matrixLinearIso.injective ?_)⟩
  change matrixLinearEquiv s.val =
    matrixLinearIso (matrixLinearIso.symm g * s₀.val * (matrixLinearIso.symm g)⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hg.symm

end CFSG.SeitzReduction.OmegaPilot
