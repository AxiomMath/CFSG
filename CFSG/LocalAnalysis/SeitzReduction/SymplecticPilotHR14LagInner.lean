module

public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueReduce

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace)

theorem lagRank_sub_one_eq_finrank_commSpace {K : Type} [Field K] {d : ℕ} (A : GL (Fin d) K) :
    (((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank =
      finrank K (commSpace (matrixLinearIso A)) := by
  have h : ((((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).mulVecLin) =
      ((matrixLinearIso A : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) -
        1 := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.sub_apply,
      LinearEquiv.coe_coe, CFSG.RankThree.PartOne.AUTSL.matrixLinearIso_apply,
      Module.End.one_apply]
  rw [Matrix.rank, h]

theorem matrixProjectiveConjugationHom_eq_conj {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (s : matrixIsometries Q)
    (hs : (s : GL (Fin d) K) ∈ matrixDerived Q) :
    matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
      MulAut.conj (matrixProjectiveProjection Q ⟨s, hs⟩) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q y
  change matrixProjectiveConjugation Q (matrixIsometryInclusion Q s)
    (matrixProjectiveProjection Q B) = _
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem lagMulAut_mul_conj_mul_inv {X : Type*} [Group X] (β : MulAut X) (x : X) :
    β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem lagMem_range_conj_of_congr {X Y : Type*} [Group X] [Group Y] (ε : X ≃* Y) (θ : MulAut X)
    {y : Y} (h : MulAut.congr ε θ = MulAut.conj y) :
    θ ∈ (MulAut.conj : X →* MulAut X).range := by
  refine ⟨ε.symm y, MulEquiv.ext fun x => ?_⟩
  have e := DFunLike.congr_fun h (ε x)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at e
  have e2 : θ x = ε.symm (y * ε x * y⁻¹) := by rw [← e, MulEquiv.symm_apply_apply]
  rw [MulAut.conj_apply, e2, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem false_of_linearClass_of_even {κ : Sp2mKind} (h1 : SpOmegaStepOneInput κ)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin n, RootKindSp e t f k κ) (hglob : SpOmegaRowGlobal e t f κ) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
    {K' : Type} [Field K'] [Finite K'] {Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')}
    (hK' : Nat.card K' = 2 ^ f) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (ε : spGlobal e ≃* matrixProjectiveDerived Q) (β : MulAut (matrixProjectiveDerived Q))
    (s : matrixIsometries Q)
    (hrank : Even (((s : GL (Fin (2 * (n + 1))) K') :
      Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') - 1).rank)
    (hβ : β⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) : False := by
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hsΩ : (s : GL (Fin (2 * (n + 1))) K') ∈ matrixDerived Q := by
    rw [CFSG.RankThree.PartOne.AUTSL.mem_matrixDerived_iff_even hQ hT s.2,
      ← lagRank_sub_one_eq_finrank_commSpace]
    exact hrank
  rw [matrixProjectiveConjugationHom_eq_conj Q s hsΩ] at hβ
  have hc : MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) =
      MulAut.conj (β (matrixProjectiveProjection Q ⟨s, hsΩ⟩)) := by
    rw [← lagMulAut_mul_conj_mul_inv, ← hβ]
    group
  exact h1 G L hset n f K hn hKc hf e t ht hKt hroot hglob g hg (lagMem_range_conj_of_congr ε _ hc)

end CFSG.SeitzReduction.SymplecticPilot
