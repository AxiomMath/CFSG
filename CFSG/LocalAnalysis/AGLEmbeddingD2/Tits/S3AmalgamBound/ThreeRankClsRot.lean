module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven Matrix

theorem two_le_pRank_three_of_rotGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {e : Fin 2 ⊕ Fin 2 → ι} (he : Function.Injective e)
    (hH : ∀ k, rotGL (e (.inl k)) (e (.inr k)) ∈ H) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ∀ a b : Fin 2 ⊕ Fin 2, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_statedProj (hH 0) (hH 1)
    (rotGL_pow_three _ _) (rotGL_pow_three _ _)
    (rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (fun hx => mul_scalar_ne (g := 1) (hne _ _ (by decide)) (one_mulVec _)
      (rotMatrix_mulVec_left _ _) hx (one_mul _))
    (fun n c hc => mul_scalar_ne (hne _ _ (by decide))
      (rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n)
      (rotMatrix_mulVec_left _ _) hc)

theorem psl_two_le_pRank_three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) :=
  two_le_pRank_three_of_rotGL
    ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
    fun _ => Subgroup.subset_closure (det_rotMatrix _ _)

theorem psp_two_le_pRank_three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n K))) :=
  two_le_pRank_three_of_rotGL
    ((Fin.castLE_injective hn).sumMap (Fin.castLE_injective hn))
    fun _ => Subgroup.subset_closure (rotMatrix_inl_inr_symplectic _)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls
