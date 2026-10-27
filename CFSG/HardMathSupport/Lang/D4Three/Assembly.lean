module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Fixed27
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def D4Bridge : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.D 4 q).Valid) (F : Type) [Field F] [Finite F],
    Nat.card F = q.card → Nonempty (AdjointQuotient Tag.D4 F ≃* ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩)

@[expose] def D4FixedBound : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (α : MulAut (adjointGroup Tag.D4 F)), α ^ 3 = 1 →
    α ∉ inner (adjointGroup Tag.D4 F) → 27 ∣ Nat.card (fixedSubgroup α)

theorem e27LieOuterAutAt_D4_of_bridge (hB : D4Bridge) (hF : D4FixedBound) :
    CFSG.HardMathSupport.Malle.E27Lie.E27LieOuterAutAt (fun i => ∃ q, i = .D 4 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hpr : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent (by have := q.exponent_pos; omega),
      TauCeti.PrimePower.card_def]
  obtain ⟨br⟩ := hB q hv (GaloisField q.p q.exponent) hcard
  let φ : K ≃* adjointGroup Tag.D4 (GaloisField q.p q.exponent) :=
    (e.trans br.symm).trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have hu3' : MulAut.congr φ u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hu_inn : u ∉ inner K := fun ⟨k, hk⟩ => hout k hk.symm
  have hout2 : MulAut.congr φ u ∉ inner (adjointGroup Tag.D4 (GaloisField q.p q.exponent)) :=
    fun hin => hu_inn ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff φ u).mp hin)
  have h27 := hF (GaloisField q.p q.exponent) (MulAut.congr φ u) hu3' hout2
  rw [CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr φ u] at h27
  exact CFSG.HardMathSupport.Malle.E27Lie.false_of_dvd_twentySeven u hQ h27

end CFSG.HardMathSupport.Lang.D4Three
