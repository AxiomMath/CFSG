module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)


section Certs


section LabelToModel

theorem exists_mulEquiv_matrixProjectiveDerived_of_isLabel_twD_gen {K : Type} [Group K]
    [Finite K] {m n : ℕ} (hm : 4 ≤ m) (hn : 2 ≤ n)
    (hK : HasLabel K (fun l : GLALabel => l = ⟨.twD, m, n⟩))
    (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (K ≃* matrixProjectiveDerived (coordinateQuadMinus m F (by omega) b c)) := by
  obtain ⟨-, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaMinus m 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar, CFSG.StandardType.markDeg,
      show m ≠ 2 by omega, show m ≠ 3 by omega] using hM
  obtain ⟨-, F, hfield, hfinite, hcard, b, c, hirr, ⟨e⟩⟩ :=
    hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ n := by rwa [← Nat.card_eq_fintype_card]
  have hchar : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  letI : CharP F 2 := hchar
  refine ⟨F, hfield, hfinite, hchar, hcard, b, c, hirr, ⟨?_⟩⟩
  let eZ : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact eZ.trans (coordinateMinusWitnessEquiv F (by omega) b c e)

theorem exists_mulEquiv_matrixProjectiveDerived_of_isLabel_twD {K : Type} [Group K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n)
    (hK : HasLabel K (fun l : GLALabel => l = ⟨.twD, 5, n⟩))
    (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (K ≃* matrixProjectiveDerived (coordinateQuadMinus 5 F (by omega) b c)) :=
  exists_mulEquiv_matrixProjectiveDerived_of_isLabel_twD_gen (by omega) hn hK hZ

end LabelToModel

@[expose] def TwDLayerData : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n q : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    q.Prime → q ≠ 2 → q ∣ 2 ^ n + 1 → ∀ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
      LayerData166 (matrixProjectiveDerived (coordinateQuadMinus 5 F (by omega) b c)) q 4

theorem layerData166_of_hasLabel_twD_five (hD : TwDLayerData) {J : Type} [Group J] [Finite J]
    {n q : ℕ} (hn : 2 ≤ n) (hJ : HasLabel J (fun l : GLALabel => l = ⟨.twD, 5, n⟩))
    (hZ : Subgroup.center J = ⊥) (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ 2 ^ n + 1) :
    LayerData166 J q 4 := by
  obtain ⟨F, hfield, hfinite, hchar, hF, b, c, hirr, ⟨e⟩⟩ :=
    exists_mulEquiv_matrixProjectiveDerived_of_isLabel_twD hn hJ hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  exact LayerData166.of_mulEquiv e (hD F n q hn hF hq hq2 hqdvd b c hirr) hq

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
