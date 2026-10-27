module

public import CFSG.LieType.Chevalley.CLSEvenE6GraphInvolutionFourGroup

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterRank

open CFSG

theorem two_le_pRank_of_psl2 {N : Type} [Group N] [Finite N] (hq : IsQuasisimple N) {k : Type}
    [Field k] (hk2 : Nat.card k ≠ 2) (hk3 : Nat.card k ≠ 3)
    (e : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) : 2 ≤ pRank 2 N := by
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 k le_rfl
      (Or.inr hk2) (Or.inr hk3)
  have : IsSimpleGroup N := e.isSimpleGroup
  have hnc : ∃ a b : N, a * b ≠ b * a := by
    obtain ⟨-, -, a', b', hab'⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    exact ⟨a, b, fun h' => hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h'])⟩
  exact CFSG.LieType.Chevalley.two_le_pRank_of_isSimpleGroup hnc

end S3OuterRank

end CFSG.GH74.Generic.BProg.B3
