module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

theorem lemma1433Five_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    Lemma1433Five_F4 := by
  intro G _ _ T L V hyp hF
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  obtain ⟨hVe, hV8, hLTV, -, -⟩ := stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V hyp hF
  refine le_antisymm (le_inf ?_ le_rfl) inf_le_right
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  have hVne : V ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV8
    omega
  obtain ⟨M', hM', hle⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (V : Set G)) ⟨V, hVne, hV2, rfl⟩
  have hM'eq := (h13322 G T L hyp.h13 L hyp.h13.faithful).2.2.2 M' hM' (hLTV.trans hle)
  rw [← hM'eq]
  exact hle

end CFSG.Quasithin.H13
