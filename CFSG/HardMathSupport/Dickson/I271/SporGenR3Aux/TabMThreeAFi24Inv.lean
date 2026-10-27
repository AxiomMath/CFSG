module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeCentral
public import CFSG.Sporadic.FischerOddCore.Fi24Block

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

theorem fi24J_involutions :
    (∀ s : CFSG.Sporadic.Fi24.J, s * s = 1 → s ≠ 1 →
      IsConj s CFSG.Sporadic.Fi24.tJ ∨ IsConj s CFSG.Sporadic.FischerOddCore.fi24R2) ∧
    Nat.card ↥(Subgroup.centralizer ({CFSG.Sporadic.Fi24.tJ} : Set CFSG.Sporadic.Fi24.J)) =
      258247006617600 ∧
    Nat.card ↥(Subgroup.centralizer ({CFSG.Sporadic.FischerOddCore.fi24R2} :
      Set CFSG.Sporadic.Fi24.J)) = 160526499840 := by
  refine ⟨fun s hs hs1 => ?_, CFSG.EvenSporadicStandard.TwoFi22.DS81.card_centralizer_tJ,
    (CFSG.Sporadic.FischerOddCore.fi24R2_centralizer_structure).1⟩
  rcases CFSG.Sporadic.Fi24.isConj_tJ_or_r2 CFSG.Fischer.polarFacts
      CFSG.Sporadic.Fi23.d1_mem_localClass CFSG.Sporadic.Fi23.involution_cover hs hs1 with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans CFSG.Sporadic.FischerOddCore.isConj_t2_fi24R2)

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
