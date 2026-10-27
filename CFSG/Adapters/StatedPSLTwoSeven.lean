module

public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

theorem nonempty_mulEquiv_sl_three_two_of_psl_two_seven {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 7 1) :
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have e' : S ≃* StatedProj (StatedSL 2 F) := e
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF]
    norm_num
  let φ : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let f₁ : StatedProj (StatedSL 2 F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  exact ⟨((e'.trans f₁).trans e₄.symm).trans e₃.symm⟩

theorem statedClassicalModel_psl_three_two_of_psl_two_seven {X : Type} [Group X]
    (hX : StatedClassicalModel X .PSL 2 7 1) : StatedClassicalModel X .PSL 3 2 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sl_three_two_of_psl_two_seven hX
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  have hadm : StatedLieAdmissible .PSL 3 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
  exact ⟨hadm, ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(e.trans e₂.symm).trans (projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))⟩⟩

theorem statedClassicalModel_psl_two_seven_of_psl_three_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 3 2 1) : StatedClassicalModel X .PSL 2 7 1 := by
  have hL : CFSG.Blueprint.LieModel X .PSL 3 2 1 := Or.inl ⟨by decide, h⟩
  have h7 := CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism X hL
  rcases h7 with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact hc
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.Open.StatedAPI
