module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR30
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR31
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR32

public section

namespace CFSG.GH74.GLS

open CFSG CFSG.GH74.GLS.Th2.Obs

theorem b_row2_autU_proved :
    B_row2_autU := by
  intro X _ _ hX ε σ hε2 hσ2 hεσ hσ1 hσε hns
  rcases hX with ⟨⟨e⟩⟩ | hL2
  · exact autU_A7 e ε σ hε2 hσ2 hεσ hσ1 hσε hns
  · obtain ⟨F, _, _, hF, -, ⟨e⟩⟩ := IVK.exists_l2Field_of_hasL2Model_pred (fun q hq => hq) hL2
    exact autU_L2 hF e ε σ hε2 hσ2 hεσ hσ1 hσε hns

theorem b_row2_autZ_proved :
    B_row2_autZ := by
  intro X _ _ hX Eb Pb hEel hE4 hsolv hdih hcomm
  rcases hX with ⟨⟨e⟩⟩ | hL2
  · exact autZ_A7 e Eb Pb hEel hE4 hsolv hdih hcomm
  · obtain ⟨F, _, _, hF, hF9, ⟨e⟩⟩ :=
      IVK.exists_l2Field_of_hasL2Model_pred (fun q hq => hq.1) hL2
    exact autZ_L2 hF hF9.2 e Eb Pb hEel hE4 hsolv hdih hcomm

theorem b_row2_stageB_proved
    (hrank : B_ivk_L29_rank) : B_row2_stageB :=
  b_row2_stageB_of_aut hrank b_row2_autU_proved b_row2_autZ_proved

end CFSG.GH74.GLS
