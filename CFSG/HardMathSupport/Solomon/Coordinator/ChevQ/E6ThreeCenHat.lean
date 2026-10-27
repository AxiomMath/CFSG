module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.TableBExc.E6Three (hatGroup hatAut adjointGroup_le_hatGroup
  rootDiagUnit_mem_hatGroup coe_hatAut_apply)

variable {K : Type} [Field K]

theorem cen_e6InndiagGL_eq_hatGroup : e6InndiagGL K = hatGroup .E6 K := by
  refine le_antisymm (sup_le adjointGroup_le_hatGroup ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact rootDiagUnit_mem_hatGroup a
  · rintro _ ⟨g, hg, a, rfl⟩
    exact mul_mem (adjointGroup_le_e6InndiagGL K hg) (rootDiagUnit_mem_e6InndiagGL a)

theorem cen_exists_mul_of_mem_e6InndiagGL {x : ModGL Tag.E6 K} (hx : x ∈ e6InndiagGL K) :
    ∃ g ∈ adjointGroup Tag.E6 K, ∃ b : Fin Tag.E6.rank → Kˣ, x = g * rootDiagUnit Tag.E6 b := by
  rw [cen_e6InndiagGL_eq_hatGroup] at hx
  exact hx

theorem cen_hatAut_eq (x : hatGroup .E6 K) :
    hatAut .E6 K x = e6InndiagConj K ⟨x, cen_e6InndiagGL_eq_hatGroup.ge x.2⟩ :=
  MulEquiv.ext fun h => Subtype.ext ((coe_hatAut_apply x h).trans
    (e6InndiagConj_apply ⟨x, cen_e6InndiagGL_eq_hatGroup.ge x.2⟩ h).symm)

theorem cen_range_hatAut : (hatAut .E6 K).range = e6Inndiag K := by
  rw [← range_e6InndiagConj K]
  ext φ
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (cen_hatAut_eq x).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, cen_e6InndiagGL_eq_hatGroup.le g.2⟩, cen_hatAut_eq _⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
