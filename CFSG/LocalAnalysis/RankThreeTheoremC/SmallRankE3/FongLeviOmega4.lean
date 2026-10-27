module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

noncomputable def fongSL2CongrField {S S' : Type} [Field S] [Field S'] (φ : S ≃+* S') :
    Matrix.SpecialLinearGroup (Fin 2) S ≃* Matrix.SpecialLinearGroup (Fin 2) S' where
  toFun := Matrix.SpecialLinearGroup.map φ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map φ.symm.toRingHom
  left_inv A := by ext i j; simp
  right_inv A := by ext i j; simp
  map_mul' := map_mul _

theorem orthResDer_one_equiv_psl2 {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    Nonempty (↥(orthResDer F b c 1) ⧸ Subgroup.center ↥(orthResDer F b c 1) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * f))) := by
  obtain ⟨hs, ⟨x, y, hxy⟩, -⟩ := orthResDer_one_facts hirr
  have hZ : Subgroup.center ↥(orthResDer F b c 1) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(orthResDer F b c 1)) with h | h
    · exact h
    · have hy : y ∈ Subgroup.center ↥(orthResDer F b c 1) := by
        rw [h]
        exact Subgroup.mem_top y
      exact absurd ((Subgroup.mem_center_iff.mp hy) x) hxy
  obtain ⟨E, _, _, D, -, ρ, -, -, hinj, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction
      (CFSG.LieType.Universal.Spin.quadMinus 2 F b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 F hirr)
      (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus.finrank_minusSpace_small
        (n := 2) (by norm_num))
      (fun U hU =>
        CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus.exists_quadMinus_ne_zero_small
          hirr (by norm_num) U hU)
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus.nonempty_range_equiv_statedOmega
      ρ hcomm
  have h2 : ↥(orthResDer F b c 1) ≃* Matrix.SpecialLinearGroup (Fin 2) E :=
    (orthResDerEquivStatedOmega (K := F) (b := b) (c := c) 1).trans
      ((MonoidHom.ofInjective hinj).trans e).symm
  haveI := D.finite_E
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  have hE : Fintype.card E = Fintype.card (GaloisField 2 (2 * f)) := by
    have hEcard : Nat.card E = 2 ^ (2 * f) := by
      rw [D.card_E, hF, ← pow_mul, mul_comm]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEcard,
      GaloisField.card 2 (2 * f) (by omega)]
  let φ : E ≃+* GaloisField 2 (2 * f) := FiniteField.ringEquivOfCardEq hE
  have h3 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * f)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * f)) :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.RankThree.PartOne.KCOrthogonal.sl2_center_eq_bot (F := GaloisField 2 (2 * f))).symm)
  have h1 : ↥(orthResDer F b c 1) ⧸ Subgroup.center ↥(orthResDer F b c 1) ≃*
      ↥(orthResDer F b c 1) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨h1.trans (h2.trans ((fongSL2CongrField φ).trans h3))⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
