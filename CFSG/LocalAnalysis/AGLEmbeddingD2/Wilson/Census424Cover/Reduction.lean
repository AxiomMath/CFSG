module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Cover

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Item426

@[expose] def CoverCentX : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46 X → IsQuasisimple X →
    Subgroup.center X ≠ ⊥ → ¬ IsSLThreePi X →
    ∀ y : X, y ∉ Subgroup.center X → y ^ 3 ∈ Subgroup.center X →
      ∀ P ∈ thetaComponentsIn (fixSub (MulAut.conj y)),
        ¬ Sec11.IsType424 (P ⧸ aschbacherSolvableCore 3 P)

theorem k424CoverCent_of_coverCentX (h : CoverCentX) : K424CoverCent := by
  intro G _ _ L K c hlist hqs hZ hnsl hcN hc3 hout hcent hK
  have hKL : K ≤ L := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hin : thetaAut L hcN ∈
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
    by_contra hnot
    exact hout ⟨hcN, hnot⟩
  obtain ⟨y, hy⟩ := hin
  have hy3 : y ^ 3 ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    have h1 : MulAut.conj (y ^ 3) = 1 := by
      rw [map_pow, hy, thetaAut_pow_eq_one L hcN hc3]
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 : y ^ 3 * g * (y ^ 3)⁻¹ = g := by
      have := congrArg (fun φ : MulAut _ => φ g) h1
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h2]
      _ = y ^ 3 * g := by group
  have hyZ : y ∉ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    intro hyc
    apply hcent
    have h1 : thetaAut L hcN = 1 := by
      rw [← hy]
      ext g
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_center_iff.mp hyc g).symm
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    show (thetaQuotMulAut L).comp L.normalizerMonoidHom ⟨c, hcN⟩ = 1
    exact h1
  have hP := map_mem_thetaComponentsIn_fixSub L hcN hc3 hK
  rw [show thetaAut L hcN = MulAut.conj y from hy.symm] at hP
  have hnot := h _ hlist hqs hZ hnsl y hyZ hy3 _ hP
  intro hty
  obtain ⟨e⟩ := nonempty_quotTheta_map_equiv L hKL
  exact hnot (Sec11.isType424_of_mulEquiv e.symm hty)

end CFSG.AGLEmbeddingD2.Wilson.Census424Cover
