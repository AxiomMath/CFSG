module

public import CFSG.Quasithin.H13.U3S1347F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_concl_i_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂)
    (hcomm : ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    Concl1347i T H₁ H₂ := by
  obtain ⟨hH₀, -, -, hsup, hinf, hc₁, hc₂⟩ :=
    s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  obtain ⟨hN₁, hN₂⟩ := s1347_normal_of_comm S h hH₀ hcomm
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hK := s1347_comm_le_of_normal S h ((oTwoRes_le H₂).trans (le_sup_right.trans hN₁))
    ((oTwoRes_le H₁).trans (le_sup_left.trans hN₂))
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := s1347_V0_of_normal S h hH₀ hsup hinf hc₁ hc₂ hN₁ hN₂
  exact ⟨s1347_mul_of_normal h.inH₂.1 (le_oTwoRes_sup_of_isSylowTwoOf hsyl₁) hN₁, hK,
    s1347_quot_of_normal S h hH₀ hN₁ hN₂ hK, v1, v2, v3, v4, v5, v6⟩

end CFSG.Quasithin.H13.U3
