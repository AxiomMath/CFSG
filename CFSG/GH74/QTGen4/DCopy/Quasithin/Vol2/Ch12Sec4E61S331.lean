module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec4Statements

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem isUniqueM_sup_of_cx_F4 (h331 : Stmt3_3_1_F4) (hcx : Cx1242 G T L V) :
    IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) := by
  have hyp := hcx.hyp
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨hmax, -, huniq⟩, -, -, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at hmax huniq
  exact ⟨⟨hmax, sup_le Subgroup.le_normalizer hyp.normalizes⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩

end CFSG.Quasithin.H13
