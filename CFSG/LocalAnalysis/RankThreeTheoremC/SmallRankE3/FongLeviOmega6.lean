module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSimple
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSmall
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (finrank_minusSpace_small exists_quadMinus_ne_zero_small nonempty_range_equiv_statedOmega)

theorem orthResDer_two_equiv_psu4 {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    Nonempty (↥(orthResDer F b c 2) ⧸ Subgroup.center ↥(orthResDer F b c 2) ≃*
      StatedProj (StatedSU 4 (2 ^ f) (GaloisField 2 (2 * f)))) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := F)
      rw [hF] at this
      norm_num at this
    · exact h
  obtain ⟨hs, ⟨_, _, hxy⟩, -⟩ := orthResDer_two_facts hirr
  have hZ : Subgroup.center ↥(orthResDer F b c 2) = ⊥ :=
    center_eq_bot_of_simple_of_not_comm hxy
  obtain ⟨E, _, _, D, -, ρ, -, -, hinj, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction
      (CFSG.LieType.Universal.Spin.quadMinus 3 F b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr)
      (finrank_minusSpace_small (n := 3) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_small hirr (by norm_num) U hU)
  obtain ⟨eR⟩ := nonempty_range_equiv_statedOmega (n := 3) ρ hcomm
  haveI := D.finite_E
  obtain ⟨g, hU, hK, hbar⟩ := D.exists_unitaryFieldData
  have hfg : f = g := Nat.pow_right_injective (le_refl 2) (hF.symm.trans hK)
  subst g
  obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv hU hbar
  haveI := Fintype.ofFinite E
  haveI := Fintype.ofFinite (GaloisField 2 (2 * f))
  have hGF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hKK : Fintype.card E = Fintype.card (GaloisField 2 (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hU.card_eq_sq, hGF]
  let eK : E ≃+* GaloisField 2 (2 * f) := FiniteField.ringEquivOfCardEq hKK
  let eΩ : ↥(orthResDer F b c 2) ≃* ↥(StatedSU 4 (2 ^ f) E) :=
    ((orthResDerEquivStatedOmega (b := b) (c := c) 2).trans eR.symm).trans
      ((MonoidHom.ofInjective hinj).symm.trans θ)
  let eGF : ↥(StatedSU 4 (2 ^ f) (GaloisField 2 (2 * f))) ≃*
      StatedProj (StatedSU 4 (2 ^ f) (GaloisField 2 (2 * f))) :=
    (CFSG.LocalAnalysis.RankThreeUC.statedProj_statedSU4_equiv (GaloisField 2 (2 * f)) (2 ^ f)).symm
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    (eΩ.trans ((CFSG.Open.StatedSUFieldChange.statedSUEquiv eK 4 (2 ^ f)).trans eGF))⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
