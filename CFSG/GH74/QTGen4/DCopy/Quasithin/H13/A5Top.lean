module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S135
public import CFSG.GH74.QTGen4.U42.A5RecognitionConstructive

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

@[expose] def Input13515_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V)
    (H : Subgroup G), H ∈ S.Hz → H ≤ Subgroup.normalizer (S.L1 : Set G) →
    ¬ IsElemAbelian 2 (conjClosure S.V3 H) → ∃ I : Subgroup G, Data13515 S H I

@[expose] def Input13518_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) →
    ∃ H ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H) ∧
      H ≤ Subgroup.normalizer (S.L1 : Set G)

@[expose] def Input136_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    ¬ IsElemAbelian 2 (conjClosure V S.G1)

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem thm_13_6_1_F4
    (h1323 : Input1323Two_F4) (h1336 : Input1336_F4) (h13515 : Input13515_F4)
    (h13518 : Input13518_F4) (h136 : Input136_F4) (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 := by
  have hG1 := S.G1_mem_Hz_F4 h1336
  by_cases hab : IsElemAbelian 2 (conjClosure S.V3 S.G1)
  ·
    exact absurd (((S.tfae_13_5_10_F4 h1323 hG1).out 2 3).1 hab) (h136 G T L V S)
  ·
    obtain ⟨H, hH, hna, hn⟩ := h13518 G T L V S hab
    obtain ⟨I, D⟩ := h13515 G T L V S H hH hn hna
    exact CFSG.GH74.QTGen4.U42.prop_13_5_17_constructive_F4 S hH D hF431

end Setting

end CFSG.Quasithin.H13.A5
