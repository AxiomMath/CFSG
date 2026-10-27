module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QRank3

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ComponentClassification Subgroup

open GenLocL4Q

theorem gammaAct_sl4_quat {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A)
    (hinner : ∀ c : A, GenLocL4Q.IsInnerDiag4 (α c)) (hsect : SectionalTwoRankLE ↥(innJoin α) 4)
    (x y : GL (Fin 4) F) (a b : A) (hax : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hby : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α b g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (y : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((y⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hanti : (x * y : Matrix (Fin 4) (Fin 4) F) = -(y * x : Matrix (Fin 4) (Fin 4) F)) :
    gammaAct α = ⊤ := by
  have _ := hsect
  rcases hA.2 with hr | hr
  · exact gammaAct_quat_rank2 hF α hA hr x y a b hax hby hanti
  · by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
    · obtain ⟨E, hE, hEk⟩ := hker
      exact gammaAct_eq_top_of_le_ker α hE hEk
    · have hker' : ∀ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E → ¬ E ≤ α.ker :=
        fun E hE hEk => hker ⟨E, hE, hEk⟩
      obtain ⟨hr23, hgam, -⟩ := range_reduction α hA hker'
      rw [hgam]
      have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
      let a' : ↥α.range := ⟨α a, a, rfl⟩
      let b' : ↥α.range := ⟨α b, b, rfl⟩
      have hax' : IsLift α.range.subtype a' x := hax
      have hby' : IsLift α.range.subtype b' y := hby
      rcases hr23.2 with hr2 | hr3
      · exact gammaAct_quat_rank2 hF α.range.subtype hr23 hr2 x y a' b' hax hby hanti
      · refine gammaAct_quat_rank3 hF hF4 h7 α.range.subtype hr23 hr3 Subtype.val_injective ?_ hax' hby' hanti
        intro c'
        obtain ⟨c, hc⟩ := c'.2
        obtain ⟨u, hu⟩ := hinner c
        refine ⟨u, ?_⟩
        intro g
        have : (α.range.subtype c' : MulAut _) = α c := by
          show (c' : MulAut _) = α c
          exact hc.symm
        rw [this]
        exact hu g

end CFSG.GH74.Generic.BProg.B2
