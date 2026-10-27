module

public import CFSG.Quasithin.H13.A5RawNat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem stmt13_3_2_three_A5_of_F4 (h1332 : Stmt13_3_2_F4) : Stmt13_3_2_three_A5_F4 := by
  intro G _ _ T L h K hK hK5 V hV
  obtain ⟨-, -, -, hc, hmod⟩ := (h1332 G T L h K hK).2.2.1.2 V hV
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hne : ¬ K ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    have h1 : ⁅V, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
    exact hV.2.1 (hV.2.2.2.1.symm.trans h1)
  obtain ⟨hnat, -⟩ := modules13_3_2_of_A5 ((quasithinO2QuotientIso_iff K _).1 hK5) hKV hne hmod
  exact exists_rawData5_of_nat hKV hnat

end CFSG.Quasithin.H13.A5
