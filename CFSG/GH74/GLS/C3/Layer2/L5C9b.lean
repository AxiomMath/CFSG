module

public import CFSG.GH74.GLS.C3.Layer2.L5C9
public import CFSG.GH74.GLS.C3.Layer2.L5C12

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

theorem c1facts : C1Facts where
  gen := fun m hlin hQ hQ1 hQ2 F hF hQF hstab => HF.n24_gen m hlin hQ hQ1 hQ2 F hF hQF hstab
  presP := fun m hlin h => HF.pres_P_of_fam m hlin h

theorem c1facts2 : C1Facts2 where
  d8_unique := fun D hD hcard hy d => HF.d8L_unique D hD hcard hy d
  g72_dvd := fun N hN => HF.card_dvd_72 N hN
  cHat_gen := fun N hN hA hex => HF.G72_cHat N hN hA hex
  cHat_v4 := HF.cHat_normalizes_v4L
  v4_normal := HF.v4L_normal
  v4_sub_d8 := HF.v4L_sub_d8L
  d8_sub_n24 := HF.d8L_sub_n24L

end CFSG.GH74.GLS.C3.Layer2.L5
