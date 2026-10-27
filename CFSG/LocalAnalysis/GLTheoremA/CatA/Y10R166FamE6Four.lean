module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem exists_mulEquiv_adjointGroup_of_isLabel_E6_two {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hlab : lab = ⟨.E6, 0, 2⟩)
    (hK : HasLabel K (fun l : GLALabel => l = lab)) (hz : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (K ≃* adjointGroup Tag.E6 F) := by
  subst hlab
  obtain ⟨-, -, hM⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel hK
  have hM' : LieModel (K ⧸ Subgroup.center K) .E6 0 2 2 := by
    simpa using CFSG.LocalAnalysis.GLTheoremA.lieModel_of_markedModel_E6
      (X := K ⧸ Subgroup.center K) rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
  refine ⟨F, hFld, hFin, ?_, ?_⟩
  · simpa using hFcard
  · letI : Field F := hFld
    letI : Finite F := hFin
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      (φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv Tag.E6 F))⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
