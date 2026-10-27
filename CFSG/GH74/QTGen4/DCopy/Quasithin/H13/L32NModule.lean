module

public import CFSG.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem stmt13_3_2_two_of_stmt13_3_2_F4 (h : Stmt13_3_2_F4) : Stmt13_3_2_two_F4 :=
  fun G _ _ T L hL K hK => (h G T L hL K hK).2.1

theorem stmtL32NModule_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    StmtL32NModule_F4 := by
  intro G _ _ T L V hyp hF
  have hL := h1332 G T L hyp.h13 L hyp.h13.faithful
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hL.2.1.1
  have hcc : conjClosure L T = L :=
    le_antisymm
      (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTL ht) l).1 hl)
      (le_conjClosure L T)
  have hIrr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V := by
    have := hF.irrPlus
    rwa [hcc] at this
  obtain ⟨-, hTV, -, hc, hmod⟩ := hL.2.2.1.2 V hIrr
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hIrr.2.2.1
  have hne : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    have h1 : ⁅V, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
    exact hIrr.2.1 (hIrr.2.2.2.1.symm.trans h1)
  obtain ⟨hnat, hCV⟩ := modules13_3_2_of_L32 hyp.linear hLV hne hmod
  obtain ⟨hcard, hsq⟩ := card_and_sq_of_binaryNaturalSL hnat
  obtain ⟨⟨-, hV1, -⟩, -, -⟩ := h1334 G T L V hyp.h13 hIrr
  refine ⟨⟨hc, fun v hv => ?_⟩, hcard, sup_le hLV hTV, ?_, hc, hnat⟩
  · simpa using congrArg Subtype.val (hsq ⟨v, hv⟩)
  · rw [hV1, hCV, Subgroup.card_bot]

end CFSG.Quasithin.H13
