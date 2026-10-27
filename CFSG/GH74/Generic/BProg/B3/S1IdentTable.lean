module

public import CFSG.GH74.Generic.Context
public import CFSG.GH74.E2.CompCertsU34
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1IdentTable

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F]

theorem rankCertified_u34 {S : Type} [Group S] (h : LieModel S .PSU 3 2 2) :
    RankCertified S 3 := by
  obtain ⟨-, -, F', _, _, hF', ⟨e'⟩⟩ := lieModel_psu_data h
  exact (CFSG.GH74.E2.rankCertified_SU3_four (q := 2 ^ 2) (by norm_num) hF').of_mulEquiv e'.symm

end S1IdentTable

end CFSG.GH74.Generic.BProg.B3
