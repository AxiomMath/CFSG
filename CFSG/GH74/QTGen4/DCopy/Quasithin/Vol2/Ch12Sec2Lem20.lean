module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem20

variable {G : Type} [Group G]

theorem normalizer_le_of_hyp1223_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1226 : Stmt12_2_6_F4) {T L V : Subgroup G}
    (hH : Hyp1223 G T L V) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have h := (h1226 G T L V hH).2 V (Subgroup.normalizer (V : Set G)) hH.irrPlus.2.1 le_rfl le_rfl
  intro x hx
  have hx' : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (V : Set G) := ⟨hx, hx⟩
  rw [← h] at hx'
  exact hx'.2

end Lem20

open Lem20

end CFSG.Quasithin.H13
