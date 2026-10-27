module

public import CFSG.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ARuOne
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Hyp147

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem isTSub_V1_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) : IsTSub T V (fsuV1 T V) 1 := by
  obtain ⟨-, -, hLTV, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hTZ : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    have hZ : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
      (Subgroup.closure_le _).mpr fun _ hz => hz.1
    exact (Subgroup.le_centralizer_iff.mp (hZ.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine ⟨inf_le_left, by rw [hV1]; norm_num, fun t ht => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hTV ht) x).mp hxV,
      (Subgroup.mem_normalizer_iff.mp (hTZ ht) x).mp hxZ⟩
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hTV ht) x).mpr hxV,
      (Subgroup.mem_normalizer_iff.mp (hTZ ht) x).mpr hxZ⟩

end Hyp147

namespace Setting147

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem hypF98_F4
    (S : Setting147 G T L V H) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (h1222 : Stmt12_2_2_F4) : HypF98 T V L (fsuV1 T V) V H :=
  L1286.hypF98_of_abelian_F4 h1222 (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
    (a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved))
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) (S.hyp.hyp1281One_F4 h13322 hMod)
    (S.hyp.isTSub_V1_F4 hMod) S.hyp.abelian S.hz

end Setting147

end CFSG.Quasithin.H13
