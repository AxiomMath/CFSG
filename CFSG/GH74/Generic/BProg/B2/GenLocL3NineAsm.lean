module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineR2

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace GenLocL3Nine

@[expose] def Rank3 (K : Type) [Field K] : Prop :=
  ∀ D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K)), D ≤ frameStab 3 K → IsRank23 ↥D →
    Nat.card ↥D = 8 → gammaAct D.subtype = ⊤

section Assembly

variable {K : Type} [Field K] [Finite K]

theorem gammaAct_eq_top_of_le_frameStab_nine (hK : Nat.card K = 9)
    (h3 : Rank3 K) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut (LinearFlag.projectiveSL 3 K)) (hA : IsRank23 A)
    (hα : α.range ≤ frameStab 3 K) : gammaAct α = ⊤ := by
  by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hle⟩ := hker
    exact gammaAct_eq_top_of_le_ker α hE hle
  push Not at hker
  obtain ⟨hD, hγ, -⟩ := range_reduction α hA (fun E hE hle => hker E hE hle)
  rw [hγ]
  have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
  have hα' : α.range ≤ frameStab 3 K := hα
  rcases hD.2 with hr2 | hr3
  · have h4 : Nat.card α.range = 4 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr2]
      norm_num
    exact GenLocL3NineR2.gammaAct_subtype_rank2 hK α.range hα' hD h4
  · have h8 : Nat.card α.range = 8 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr3]
      norm_num
    exact h3 α.range hα' hD h8

theorem genProp_projectiveSL3_nine_of_rank3 (hK : Nat.card K = 9)
    (h3 : Rank3 K) : GenProp (LinearFlag.projectiveSL 3 K) := by
  intro A _ _ α hA
  have hD : CFSG.IsElementaryAbelian 2 ↥α.range :=
    GenLocBasic.isEA_of_surjective hA.1 α.rangeRestrict α.rangeRestrict_surjective
  obtain ⟨β, hβ⟩ := exists_conj_le_frameStab (p := 3) (f := 2) Nat.prime_three (by norm_num)
    (by simpa using hK) α.range hD
  refine GenLocL3Lin.gammaAct_eq_top_of_conj α β ?_
  refine gammaAct_eq_top_of_le_frameStab_nine hK h3 _ hA ?_
  rintro _ ⟨a, rfl⟩
  exact hβ ⟨α a, ⟨a, rfl⟩, rfl⟩

end Assembly

end GenLocL3Nine

section PSL3

theorem genProp_psl3_nine_of_rank3 {J : Type} [Group J] {p f : ℕ}
    (h9 : p ^ f = 9)
    (h3 : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 9 → GenLocL3Nine.Rank3 F)
    (hJ : LieModel J .PSL 3 p f) : GenProp J := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hJ
  let ψ : J ≃* LinearFlag.projectiveSL 3 F :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 F))
  have hF9 : Nat.card F = 9 := hF.trans h9
  exact GenLocL3Lin.genProp_of_mulEquiv ψ.symm
    (GenLocL3Nine.genProp_projectiveSL3_nine_of_rank3 hF9 (h3 F hF9))

end PSL3

end CFSG.GH74.Generic.BProg.B2
