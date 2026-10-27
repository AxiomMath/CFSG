module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f4P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_4_P.bin" 29 12717335718674234096
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f4L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_4_L0.bin" 8 10114456241150036591
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f4O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_4_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f4I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_4_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f5P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_5_P.bin" 72 1334522573401720848
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f5L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_5_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f5O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_5_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f5I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_5_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f6P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_6_P.bin" 753 9129530143707814080
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f6I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_6_I.bin" 59 12839665862698464323
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f8P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_8_P.bin" 30 8721871675312506692
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f8L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_8_L0.bin" 38 5285536413898765481
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f8O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_8_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f8I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_8_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f9P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_9_P.bin" 73 7250122580222608776
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f9L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_9_L0.bin" 28 14219017388436184360
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f9O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_9_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f9I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_9_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f11P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_11_P.bin" 30 3026680058965883069
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f11L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_11_L0.bin" 8 12092998531638483864
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f11O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_11_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f11I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_11_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f12P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_12_P.bin" 72 10661471924702505912
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f12L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_12_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f12O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_12_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f12I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_12_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f14P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_14_P.bin" 30 6398081285599002789
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f14L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_14_L0.bin" 8 14762813130257493375
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f14O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_14_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f14I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_14_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f15P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_15_P.bin" 73 10088755091426120872
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f15L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_15_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f15O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_15_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f15I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_15_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f17P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_17_P.bin" 30 5717910030158298879
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f17L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_17_L0.bin" 8 7287512619014730821
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f17O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_17_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f17I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_17_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f18P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_18_P.bin" 73 13341304189711382614
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f18L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_18_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f18O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_18_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f18I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_18_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f20P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_20_P.bin" 30 1985495986900740855
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f20L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_20_L0.bin" 8 7504336822784198874
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f20O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_20_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f20I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_20_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f21P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_21_P.bin" 73 477743781934766708
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f21L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_21_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f21O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_21_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f21I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_21_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f23P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_23_P.bin" 30 305525832171578818
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f23L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_23_L0.bin" 8 10784518093536941456
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f23O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_23_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f23I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_23_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f24P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_24_P.bin" 73 9577576263227466087
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f24L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_24_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f24O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_24_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f24I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_24_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f26P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_26_P.bin" 30 9184523406515128246
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f26L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_26_L0.bin" 8 13975752621459736887
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f26O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_26_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f26I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_26_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f27P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_27_P.bin" 73 13482520704163060080
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f27L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_27_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f27O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_27_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f27I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_27_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f29P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_29_P.bin" 30 2148967386226803654
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f29L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_29_L0.bin" 8 9657587127728125578
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f29O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_29_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f29I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_29_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f30P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_30_P.bin" 73 7962760151388760354
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f30L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_30_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f30O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_30_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f30I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_30_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f32P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_32_P.bin" 30 7990396407823055553
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f32L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_32_L0.bin" 8 15570235313921450302
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f32O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_32_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f32I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_32_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f33P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_33_P.bin" 72 7785027675628616470
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f33L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_33_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f33O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_33_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f33I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_33_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f35P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_35_P.bin" 30 11002118085660232816
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f35L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_35_L0.bin" 8 8227990570546969296
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f35O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_35_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f35I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_35_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f36P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_36_P.bin" 73 4194284728188945865
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f36L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_36_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f36O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_36_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f36I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_36_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f38P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_38_P.bin" 30 12596804941998232877
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f38L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_38_L0.bin" 8 10706614351397290979
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f38O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_38_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f38I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_38_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f39P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_39_P.bin" 73 15732688081292916700
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f39L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_39_L0.bin" 8 13904878499154948281
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f39O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_39_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y2.f39I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y2_39_I.bin" 4 14007230941556241898

namespace CFSG.KD.ThS.Rows_Sm_Y2

@[expose] noncomputable def f4l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f4L0 (CFSG.KD.ThS.Rows_Sm_Y2.f4O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f4O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f4O0 g)

@[expose] noncomputable def f4 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_0 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f4P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f4P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f4P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f4P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f4l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f4P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f4P (6 * g + 5))

@[expose] noncomputable def f5l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f5L0 (CFSG.KD.ThS.Rows_Sm_Y2.f5O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f5O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f5O0 g)

@[expose] noncomputable def f5 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_0 (CFSG.KD.ThS.Rows_Sm_Y2.f5P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f5P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f5P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f5P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f5P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f5P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f5l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f5P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f5P (8 * g + 7))

@[expose] noncomputable def f6 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThS.Rows_Sm_Y2.f6P (6 * g + 0))) (Nat.pow
    (CFSG.KD.ThS.Rows_Sm_Y2.f6P (6 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f6P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f6P (6 * g + 3)))
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f6P (6 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f6P (6 * g + 5)))))

@[expose] noncomputable def f8l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f8L0 (CFSG.KD.ThS.Rows_Sm_Y2.f8O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f8O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f8O0 g)

@[expose] noncomputable def f8 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_1 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f8P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f8P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f8P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f8P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f8l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f8P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f8P (6 * g + 5))

@[expose] noncomputable def f9l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f9L0 (CFSG.KD.ThS.Rows_Sm_Y2.f9O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f9O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f9O0 g)

@[expose] noncomputable def f9 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_1 (CFSG.KD.ThS.Rows_Sm_Y2.f9P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f9P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f9P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f9P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f9P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f9P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f9l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f9P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f9P (8 * g + 7))

@[expose] noncomputable def f11l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f11L0 (CFSG.KD.ThS.Rows_Sm_Y2.f11O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f11O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f11O0 g)

@[expose] noncomputable def f11 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_2 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f11P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f11P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f11P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f11P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f11l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f11P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f11P (6 * g + 5))

@[expose] noncomputable def f12l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f12L0 (CFSG.KD.ThS.Rows_Sm_Y2.f12O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f12O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f12O0 g)

@[expose] noncomputable def f12 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_2 (CFSG.KD.ThS.Rows_Sm_Y2.f12P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f12P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f12P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f12P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f12P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f12P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f12l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f12P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f12P (8 * g + 7))

@[expose] noncomputable def f14l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f14L0 (CFSG.KD.ThS.Rows_Sm_Y2.f14O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f14O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f14O0 g)

@[expose] noncomputable def f14 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_3 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f14P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f14P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f14P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f14P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f14l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f14P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f14P (6 * g + 5))

@[expose] noncomputable def f15l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f15L0 (CFSG.KD.ThS.Rows_Sm_Y2.f15O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f15O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f15O0 g)

@[expose] noncomputable def f15 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_3 (CFSG.KD.ThS.Rows_Sm_Y2.f15P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f15P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f15P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f15P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f15P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f15P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f15l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f15P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f15P (8 * g + 7))

@[expose] noncomputable def f17l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f17L0 (CFSG.KD.ThS.Rows_Sm_Y2.f17O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f17O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f17O0 g)

@[expose] noncomputable def f17 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_4 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f17P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f17P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f17P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f17P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f17l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f17P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f17P (6 * g + 5))

@[expose] noncomputable def f18l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f18L0 (CFSG.KD.ThS.Rows_Sm_Y2.f18O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f18O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f18O0 g)

@[expose] noncomputable def f18 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_4 (CFSG.KD.ThS.Rows_Sm_Y2.f18P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f18P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f18P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f18P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f18P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f18P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f18l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f18P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f18P (8 * g + 7))

@[expose] noncomputable def f20l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f20L0 (CFSG.KD.ThS.Rows_Sm_Y2.f20O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f20O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f20O0 g)

@[expose] noncomputable def f20 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_5 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f20P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f20P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f20P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f20P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f20l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f20P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f20P (6 * g + 5))

@[expose] noncomputable def f21l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f21L0 (CFSG.KD.ThS.Rows_Sm_Y2.f21O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f21O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f21O0 g)

@[expose] noncomputable def f21 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_5 (CFSG.KD.ThS.Rows_Sm_Y2.f21P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f21P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f21P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f21P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f21P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f21P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f21l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f21P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f21P (8 * g + 7))

@[expose] noncomputable def f23l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f23L0 (CFSG.KD.ThS.Rows_Sm_Y2.f23O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f23O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f23O0 g)

@[expose] noncomputable def f23 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_6 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f23P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f23P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f23P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f23P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f23l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f23P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f23P (6 * g + 5))

@[expose] noncomputable def f24l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f24L0 (CFSG.KD.ThS.Rows_Sm_Y2.f24O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f24O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f24O0 g)

@[expose] noncomputable def f24 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_6 (CFSG.KD.ThS.Rows_Sm_Y2.f24P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f24P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f24P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f24P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f24P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f24P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f24l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f24P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f24P (8 * g + 7))

@[expose] noncomputable def f26l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f26L0 (CFSG.KD.ThS.Rows_Sm_Y2.f26O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f26O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f26O0 g)

@[expose] noncomputable def f26 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_7 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f26P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f26P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f26P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f26P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f26l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f26P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f26P (6 * g + 5))

@[expose] noncomputable def f27l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f27L0 (CFSG.KD.ThS.Rows_Sm_Y2.f27O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f27O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f27O0 g)

@[expose] noncomputable def f27 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_7 (CFSG.KD.ThS.Rows_Sm_Y2.f27P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f27P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f27P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f27P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f27P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f27P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f27l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f27P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f27P (8 * g + 7))

@[expose] noncomputable def f29l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f29L0 (CFSG.KD.ThS.Rows_Sm_Y2.f29O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f29O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f29O0 g)

@[expose] noncomputable def f29 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_8 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f29P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f29P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f29P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f29P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f29l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f29P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f29P (6 * g + 5))

@[expose] noncomputable def f30l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f30L0 (CFSG.KD.ThS.Rows_Sm_Y2.f30O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f30O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f30O0 g)

@[expose] noncomputable def f30 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_8 (CFSG.KD.ThS.Rows_Sm_Y2.f30P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f30P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f30P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f30P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f30P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f30P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f30l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f30P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f30P (8 * g + 7))

@[expose] noncomputable def f32l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f32L0 (CFSG.KD.ThS.Rows_Sm_Y2.f32O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f32O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f32O0 g)

@[expose] noncomputable def f32 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_9 CFSG.KD.ThS.rm CFSG.KD.ThS.PR2
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f32P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f32P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f32P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f32P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f32l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f32P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f32P (6 * g + 5))

@[expose] noncomputable def f33l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f33L0 (CFSG.KD.ThS.Rows_Sm_Y2.f33O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f33O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f33O0 g)

@[expose] noncomputable def f33 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_9 (CFSG.KD.ThS.Rows_Sm_Y2.f33P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f33P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f33P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f33P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f33P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f33P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f33l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f33P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f33P (8 * g + 7))

@[expose] noncomputable def f35l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f35L0 (CFSG.KD.ThS.Rows_Sm_Y2.f35O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f35O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f35O0 g)

@[expose] noncomputable def f35 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_10 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f35P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f35P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f35P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f35P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f35l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f35P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f35P (6 * g + 5))

@[expose] noncomputable def f36l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f36L0 (CFSG.KD.ThS.Rows_Sm_Y2.f36O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f36O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f36O0 g)

@[expose] noncomputable def f36 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_10 (CFSG.KD.ThS.Rows_Sm_Y2.f36P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f36P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f36P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f36P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f36P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f36P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f36l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f36P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f36P (8 * g + 7))

@[expose] noncomputable def f38l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f38L0 (CFSG.KD.ThS.Rows_Sm_Y2.f38O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f38O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f38O0 g)

@[expose] noncomputable def f38 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp2 CFSG.KD.ThS.PT2_11 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f38P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y2.f38P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2
    (CFSG.KD.ThS.Rows_Sm_Y2.f38P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f38P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f38l0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f38P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y2.f38P (6 * g + 5))

@[expose] noncomputable def f39l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y2.f39L0 (CFSG.KD.ThS.Rows_Sm_Y2.f39O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y2.f39O0 g) (CFSG.KD.ThS.Rows_Sm_Y2.f39O0 g)

@[expose] noncomputable def f39 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT2_11 (CFSG.KD.ThS.Rows_Sm_Y2.f39P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y2.f39P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f39P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y2.f39P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (CFSG.KD.ThS.Rows_Sm_Y2.f39P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y2.f39P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y2.f39l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y2.f39P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y2.f39P (8 * g + 7))

end CFSG.KD.ThS.Rows_Sm_Y2

#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f4 1 as CFSG.KD.ThS.bt2_0_ names CFSG.KD.ThS.Rows_Sm_Y2.f4I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f4P CFSG.KD.ThS.Rows_Sm_Y2.f4l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f5 1 as CFSG.KD.ThS.bs2_0_ names CFSG.KD.ThS.Rows_Sm_Y2.f5I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f5P CFSG.KD.ThS.Rows_Sm_Y2.f5l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f6 12 as CFSG.KD.ThS.bn2_ names CFSG.KD.ThS.Rows_Sm_Y2.f6I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f6P
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f8 1 as CFSG.KD.ThS.bt2_1_ names CFSG.KD.ThS.Rows_Sm_Y2.f8I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f8P CFSG.KD.ThS.Rows_Sm_Y2.f8l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f9 1 as CFSG.KD.ThS.bs2_1_ names CFSG.KD.ThS.Rows_Sm_Y2.f9I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f9P CFSG.KD.ThS.Rows_Sm_Y2.f9l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f11 1 as CFSG.KD.ThS.bt2_2_ names CFSG.KD.ThS.Rows_Sm_Y2.f11I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f11P CFSG.KD.ThS.Rows_Sm_Y2.f11l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f12 1 as CFSG.KD.ThS.bs2_2_ names CFSG.KD.ThS.Rows_Sm_Y2.f12I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f12P CFSG.KD.ThS.Rows_Sm_Y2.f12l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f14 1 as CFSG.KD.ThS.bt2_3_ names CFSG.KD.ThS.Rows_Sm_Y2.f14I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f14P CFSG.KD.ThS.Rows_Sm_Y2.f14l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f15 1 as CFSG.KD.ThS.bs2_3_ names CFSG.KD.ThS.Rows_Sm_Y2.f15I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f15P CFSG.KD.ThS.Rows_Sm_Y2.f15l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f17 1 as CFSG.KD.ThS.bt2_4_ names CFSG.KD.ThS.Rows_Sm_Y2.f17I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f17P CFSG.KD.ThS.Rows_Sm_Y2.f17l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f18 1 as CFSG.KD.ThS.bs2_4_ names CFSG.KD.ThS.Rows_Sm_Y2.f18I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f18P CFSG.KD.ThS.Rows_Sm_Y2.f18l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f20 1 as CFSG.KD.ThS.bt2_5_ names CFSG.KD.ThS.Rows_Sm_Y2.f20I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f20P CFSG.KD.ThS.Rows_Sm_Y2.f20l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f21 1 as CFSG.KD.ThS.bs2_5_ names CFSG.KD.ThS.Rows_Sm_Y2.f21I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f21P CFSG.KD.ThS.Rows_Sm_Y2.f21l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f23 1 as CFSG.KD.ThS.bt2_6_ names CFSG.KD.ThS.Rows_Sm_Y2.f23I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f23P CFSG.KD.ThS.Rows_Sm_Y2.f23l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f24 1 as CFSG.KD.ThS.bs2_6_ names CFSG.KD.ThS.Rows_Sm_Y2.f24I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f24P CFSG.KD.ThS.Rows_Sm_Y2.f24l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f26 1 as CFSG.KD.ThS.bt2_7_ names CFSG.KD.ThS.Rows_Sm_Y2.f26I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f26P CFSG.KD.ThS.Rows_Sm_Y2.f26l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f27 1 as CFSG.KD.ThS.bs2_7_ names CFSG.KD.ThS.Rows_Sm_Y2.f27I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f27P CFSG.KD.ThS.Rows_Sm_Y2.f27l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f29 1 as CFSG.KD.ThS.bt2_8_ names CFSG.KD.ThS.Rows_Sm_Y2.f29I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f29P CFSG.KD.ThS.Rows_Sm_Y2.f29l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f30 1 as CFSG.KD.ThS.bs2_8_ names CFSG.KD.ThS.Rows_Sm_Y2.f30I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f30P CFSG.KD.ThS.Rows_Sm_Y2.f30l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f32 1 as CFSG.KD.ThS.bt2_9_ names CFSG.KD.ThS.Rows_Sm_Y2.f32I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f32P CFSG.KD.ThS.Rows_Sm_Y2.f32l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f33 1 as CFSG.KD.ThS.bs2_9_ names CFSG.KD.ThS.Rows_Sm_Y2.f33I
  eval CFSG.KD.ThS.Rows_Sm_Y2.f33P CFSG.KD.ThS.Rows_Sm_Y2.f33l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f35 1 as CFSG.KD.ThS.bt2_10_ names
  CFSG.KD.ThS.Rows_Sm_Y2.f35I eval CFSG.KD.ThS.Rows_Sm_Y2.f35P CFSG.KD.ThS.Rows_Sm_Y2.f35l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f36 1 as CFSG.KD.ThS.bs2_10_ names
  CFSG.KD.ThS.Rows_Sm_Y2.f36I eval CFSG.KD.ThS.Rows_Sm_Y2.f36P CFSG.KD.ThS.Rows_Sm_Y2.f36l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f38 1 as CFSG.KD.ThS.bt2_11_ names
  CFSG.KD.ThS.Rows_Sm_Y2.f38I eval CFSG.KD.ThS.Rows_Sm_Y2.f38P CFSG.KD.ThS.Rows_Sm_Y2.f38l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y2.f39 1 as CFSG.KD.ThS.bs2_11_ names
  CFSG.KD.ThS.Rows_Sm_Y2.f39I eval CFSG.KD.ThS.Rows_Sm_Y2.f39P CFSG.KD.ThS.Rows_Sm_Y2.f39l0

theorem CFSG.KD.ThS.sd2 : CFSG.KC.Th.andB (Nat.beq (CFSG.KD.ThS.RBp2 (nat_lit 1)) (CFSG.KD.ThS.RBf
    (nat_lit 1))) (Nat.beq (CFSG.KD.ThS.RBp2 (nat_lit 2)) (CFSG.KD.ThS.RBf (nat_lit 2))) = true :=
    by
  quickRfl

theorem CFSG.KD.ThS.rg2 : CFSG.KC.Th.andB (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.PR2 CFSG.KD.ThS.n2
    (nat_lit 137)) (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.GL2 (nat_lit 11) (nat_lit 137)) = true := by
  quickRfl

theorem CFSG.KD.ThS.fl2 : CFSG.KC.Th.andB (Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.Cm2 CFSG.KD.ThS.Ci2) CFSG.KD.ThS.ONE) (CFSG.KC.Th.BigS.uniOK CFSG.KD.ThS.RBp2
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.up CFSG.KD.ThS.dg CFSG.KD.ThS.Cm2 CFSG.KD.ThS.Ci2
    CFSG.KD.ThS.GL2 (nat_lit 11)) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_0 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_0 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    5) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_1 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_1 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    15) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_2 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_2 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    25) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_3 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_3 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    35) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_4 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_4 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    45) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_5 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_5 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    55) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_6 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_6 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    65) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_7 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_7 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    75) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_8 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_8 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    85) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_9 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_9 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    95) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_10 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_10 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    105) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf2_11 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp2 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR2 (CFSG.KD.ThS.PT2_11 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL2 (nat_lit
    115) (nat_lit 5)) (nat_lit 15) = true := by
  quickRfl

theorem CFSG.KD.ThS.bl2 : CFSG.KC.Th.BigS.blocksOK CFSG.KD.ThS.BL2 CFSG.KD.ThS.nb2 CFSG.KD.ThS.n2 =
    true := by
  quickRfl

end
