module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401OmegaBasic
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Omega2401

open CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (finrank_minusSpace_small exists_quadMinus_ne_zero_small nonempty_range_equiv_statedOmega)

theorem nonempty_twistedA_of_isOmegaTwo_false_three {L : Type} [Group L] [Finite L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo false 3 L) :
    Nonempty (L ≃* TauCeti.ValidLieTypeIndex.Group
      ⟨.twistedA 3 twoPP, valid_twistedA_three_two⟩) := by
  obtain ⟨e0⟩ := h
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction (quadMinus 3 (ZMod 2) 1 1)
      (nondegenerate_polarBilin_quadMinus_of_finite 3 (ZMod 2) hirr)
      (finrank_minusSpace_small
        (n := 3) (by norm_num))
      (fun U hU =>
        exists_quadMinus_ne_zero_small
          hirr (by norm_num) U hU)
  obtain ⟨eR⟩ :=
    nonempty_range_equiv_statedOmega
      (n := 3) ρ hcomm
  haveI : CharP E 2 := CFSG.RankThree.PartOne.KCOrthogonal.charP_two_of_algebra (K := ZMod 2)
  haveI := D.finite_E
  obtain ⟨f, hU, hK, hbar⟩ := D.exists_unitaryFieldData
  have hf : f = 1 := by
    rw [Nat.card_zmod] at hK
    exact Nat.pow_right_injective le_rfl (hK.symm.trans (pow_one 2).symm)
  subst hf
  obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv hU hbar
  have hF : Nat.card E = (2 ^ 1) ^ 2 := hU.card_eq_sq
  obtain ⟨eS⟩ := nonempty_statedProj_equiv_of_bot (StatedSU 4 (2 ^ 1) E)
    (CFSG.LocalAnalysis.RankThreeUC.statedScalars_subgroupOf_statedSU4_eq_bot E (2 ^ 1))
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 twoPP valid_twistedA_three_two
      (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hKK : Fintype.card E = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hF.trans hK₀.symm
  let eK : E ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK (3 + 1) (2 ^ 1)
  let LSU := e0.trans (eR.symm.trans ((MonoidHom.ofInjective hinj).symm.trans θ))
  exact ⟨LSU.trans (eS.symm.trans (eP.trans e₀.symm))⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Omega2401

end
