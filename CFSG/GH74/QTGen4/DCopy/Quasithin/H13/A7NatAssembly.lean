module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.SteinbergCBConstantWeight
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

section Assembly

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem normalizer_le_of_hyp1223_F4 (h331 : Stmt3_3_1_F4) {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V) (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G)) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hV2 : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  obtain ⟨M', hM', hVM'⟩ := exists_maxTwoLocal_ge (L := normalizer (V : Set G)) ⟨V, hV1, hV2, rfl⟩
  have hLT : L ⊔ T ≤ M' := (sup_le hyp.irrPlus.2.2.1 hTV).trans hVM'
  rw [← huniq M' hM' hLT]
  exact hVM'

end Assembly

end CFSG.Quasithin.H13.A7
