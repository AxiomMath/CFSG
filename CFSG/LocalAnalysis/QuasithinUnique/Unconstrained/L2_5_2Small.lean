module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Walter.Cited.CentralSplit

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalModels CFSG.LocalAnalysis.ComponentInitial

theorem smallL2Facts : SmallL2Facts := by
  refine ⟨fun X _ hX => ?_, fun X _ hX => ?_⟩
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e
    obtain ⟨e5⟩ := nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inr (by rw [hK]; norm_num))
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    obtain ⟨e4⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 (X := alternatingGroup (Fin 5)) h60
    exact Or.inl ⟨2, le_rfl, ⟨(e'.trans e5).trans e4⟩⟩
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e
    have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
    let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
    let f₁ : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        (projectiveSpecialLinearFieldEquiv φ (Fin 2))
    obtain ⟨e₄⟩ := nonempty_GL_three_two_equiv_PSL_two_seven
    let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
      (QuotientGroup.quotientMulEquivOfEq center_SL_three_zmod_two_eq_bot).trans
        QuotientGroup.quotientBot
    let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
      MulEquiv.ofBijective _ bijective_toGL_three_zmod_two
    let e₆ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
        CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
      projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2)
    have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 2 1 :=
      ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
    exact ⟨hadm, ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
      ⟨((((e'.trans f₁).trans e₄.symm).trans e₃.symm).trans e₂.symm).trans e₆⟩⟩

end CFSG.QuasithinUnique
