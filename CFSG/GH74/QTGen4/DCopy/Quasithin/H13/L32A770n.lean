module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32ANotation

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem normalizer_le_normalizer_L_F4 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two_F4)
    {P : Subgroup G} (hP1 : P ≠ ⊥) (hP2 : IsPGroup 2 ↥P)
    (hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hP1, hP2, rfl⟩
  obtain ⟨M', hM', hNM'⟩ := exists_quasithinIsMaxTwoLocal_ge hloc
  have hM'' : quasithinIsMaxTwoLocal M' := ⟨hM'.1, fun H hH hMH => hM'.2 H hH hMH⟩
  have he := (h13322 G T L h.hyp.h13 L h.fsu.faithful).2.2.2 M' hM'' (hLT.trans hNM')
  exact he ▸ hNM'

end CFSG.Quasithin.H13.L32A
