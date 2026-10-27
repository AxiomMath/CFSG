module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenFam
public import CFSG.LieType.Steinberg.CentralExt.PSLAlternating

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabHub.ParabThreeInv

set_option linter.unusedSectionVars false


theorem hasBorelModel_psl {Y : Type} [Group Y] {m : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) :
    HasBorelModel Y :=
  ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_sl e,
    fun i => HasSL2Node.hasInvolThree (hasSL2Node_sl i)⟩

theorem hasBorelModel_alt_five {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) : HasBorelModel Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero 2 := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hK)
  exact hasBorelModel_psl (m := 1) (F := GaloisField 2 2)
    (((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 2)).trans e5).trans e.symm)

theorem hasBorelModel_alt_eight {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 8)) : HasBorelModel Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero 1 := ⟨by norm_num⟩
  obtain ⟨e8⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
    (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (GaloisField 2 1))).1
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_four_two_lieModel
  exact hasBorelModel_psl (m := 3) (F := GaloisField 2 1) (e8.trans e.symm)

theorem hasBorelModel_model_seven {Y : Type} [Group Y]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 7 1) : HasBorelModel Y := by
  obtain ⟨e7⟩ := CFSG.QuasithinUnique.Bridge.Over.nonempty_equiv_sl_three_two_of_model_seven h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hasBorelModel_psl (m := 2) (F := ZMod 2)
    (((QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
        QuotientGroup.quotientBot).trans e7.symm)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
