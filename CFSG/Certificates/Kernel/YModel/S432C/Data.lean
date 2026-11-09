module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM432P
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items CFSG.KD.YMS432C "CFSG/Certificates/Kernel/YModel/S432C/data/plan.items" 8557 1742858536193051551
  GP[60] GL[60] TT0_[255] TT1_[126] TT2_[60] TT3_[24] TT4_[16] TT5_[8] TT6_[2] TT7_[2] TT8_[2]

namespace CFSG.KD.YMS432C

open CFSG.KC.YModel CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def LF (c : Nat) : Nat := CFSG.KD.YM432P.F (CFSG.KC.YModel.lget [0, 1, 2, 3, 4, 5, 6, 7, 8] c)
#kc_repo #kc_natBin CFSG.KD.YMS432C N0 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N0.bin" 118784 10043416896152786499
#kc_repo #kc_natBin CFSG.KD.YMS432C N1 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N1.bin" 118784 12493830715192102604
#kc_repo #kc_natBin CFSG.KD.YMS432C N2 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N2.bin" 118784 9828105884510382661
#kc_repo #kc_natBin CFSG.KD.YMS432C N3 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N3.bin" 118784 13612795367781333664
#kc_repo #kc_natBin CFSG.KD.YMS432C N4 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N4.bin" 118784 12550903278643939347
#kc_repo #kc_natBin CFSG.KD.YMS432C N5 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N5.bin" 118784 11678750341299860902
#kc_repo #kc_natBin CFSG.KD.YMS432C N6 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N6.bin" 118784 9224733510989023731
#kc_repo #kc_natBin CFSG.KD.YMS432C N7 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N7.bin" 118784 12889273369988197010
#kc_repo #kc_natBin CFSG.KD.YMS432C N8 "CFSG/Certificates/Kernel/YModel/S432C/data/net_N8.bin" 118784 4230220469836619178
#kc_select CFSG.KD.YMS432C Nf N 9
@[expose] noncomputable def U0 : Nat := N0
@[expose] noncomputable def U1 : Nat := N1
@[expose] noncomputable def U2 : Nat := N2
@[expose] noncomputable def U3 : Nat := N3
@[expose] noncomputable def U4 : Nat := N4
@[expose] noncomputable def U5 : Nat := N5
@[expose] noncomputable def U6 : Nat := N6
@[expose] noncomputable def U7 : Nat := N7
@[expose] noncomputable def U8 : Nat := N8
#kc_select CFSG.KD.YMS432C GP GP 60
#kc_select CFSG.KD.YMS432C GL GL 60
#kc_repo #kc_natBin CFSG.KD.YMS432C U9 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U9.bin" 118784 7764061447480182283
#kc_repo #kc_natBin CFSG.KD.YMS432C U10 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U10.bin" 118784 10459347710844544998
#kc_repo #kc_natBin CFSG.KD.YMS432C U11 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U11.bin" 118784 13380931688424895076
#kc_repo #kc_natBin CFSG.KD.YMS432C U12 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U12.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U13 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U13.bin" 118784 8468566140156611617
#kc_repo #kc_natBin CFSG.KD.YMS432C U14 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U14.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U15 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U15.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U16 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U16.bin" 118784 10692176200006120194
#kc_repo #kc_natBin CFSG.KD.YMS432C U17 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U17.bin" 118784 14648954268901657641
#kc_repo #kc_natBin CFSG.KD.YMS432C U18 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U18.bin" 118784 13725359529126962473
#kc_repo #kc_natBin CFSG.KD.YMS432C U19 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U19.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U20 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U20.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U21 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U21.bin" 118784 15742069744951278891
#kc_repo #kc_natBin CFSG.KD.YMS432C U22 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U22.bin" 118784 16975419694784664811
#kc_repo #kc_natBin CFSG.KD.YMS432C U23 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U23.bin" 118784 11108778374497459537
#kc_repo #kc_natBin CFSG.KD.YMS432C U24 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U24.bin" 118784 4630080814214541283
#kc_repo #kc_natBin CFSG.KD.YMS432C U25 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U25.bin" 118784 16120960398843480226
#kc_repo #kc_natBin CFSG.KD.YMS432C U26 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U26.bin" 118784 3685993814833053277
#kc_repo #kc_natBin CFSG.KD.YMS432C U27 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U27.bin" 118784 7099539252617388574
#kc_repo #kc_natBin CFSG.KD.YMS432C U28 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U28.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U29 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U29.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U30 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U30.bin" 118784 14945583386145955646
#kc_repo #kc_natBin CFSG.KD.YMS432C U31 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U31.bin" 118784 2980640137317804570
#kc_repo #kc_natBin CFSG.KD.YMS432C U32 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U32.bin" 118784 6038211451826722220
#kc_repo #kc_natBin CFSG.KD.YMS432C U33 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U33.bin" 118784 2241891319829608614
#kc_repo #kc_natBin CFSG.KD.YMS432C U34 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U34.bin" 118784 13400057374926618038
#kc_repo #kc_natBin CFSG.KD.YMS432C U35 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U35.bin" 118784 3319664677037301730
#kc_repo #kc_natBin CFSG.KD.YMS432C U36 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U36.bin" 118784 17369614305452331167
#kc_repo #kc_natBin CFSG.KD.YMS432C U37 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U37.bin" 118784 6344960525023678858
#kc_repo #kc_natBin CFSG.KD.YMS432C U38 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U38.bin" 118784 5174317065728378045
#kc_repo #kc_natBin CFSG.KD.YMS432C U39 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U39.bin" 118784 15512627111967428887
#kc_repo #kc_natBin CFSG.KD.YMS432C U40 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U40.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U41 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U41.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U42 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U42.bin" 118784 14945583386145955646
#kc_repo #kc_natBin CFSG.KD.YMS432C U43 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U43.bin" 118784 17184529258827895256
#kc_repo #kc_natBin CFSG.KD.YMS432C U44 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U44.bin" 118784 6566223891435061974
#kc_repo #kc_natBin CFSG.KD.YMS432C U45 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U45.bin" 118784 15869681029524206500
#kc_repo #kc_natBin CFSG.KD.YMS432C U46 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U46.bin" 118784 2713326699854485780
#kc_repo #kc_natBin CFSG.KD.YMS432C U47 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U47.bin" 118784 12596847315012431460
#kc_repo #kc_natBin CFSG.KD.YMS432C U48 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U48.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U49 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U49.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U50 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U50.bin" 118784 6566223891435061974
#kc_repo #kc_natBin CFSG.KD.YMS432C U51 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U51.bin" 118784 11678750341299860902
#kc_repo #kc_natBin CFSG.KD.YMS432C U52 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U52.bin" 118784 12889273369988197010
#kc_repo #kc_natBin CFSG.KD.YMS432C U53 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U53.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U54 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U54.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U55 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U55.bin" 118784 9664274067369932536
#kc_repo #kc_natBin CFSG.KD.YMS432C U56 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U56.bin" 118784 12889273369988197010
#kc_repo #kc_natBin CFSG.KD.YMS432C U57 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U57.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U58 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U58.bin" 118784 18349894373327612206
#kc_repo #kc_natBin CFSG.KD.YMS432C U59 "CFSG/Certificates/Kernel/YModel/S432C/data/net_U59.bin" 118784 12889273369988197010
#kc_select CFSG.KD.YMS432C U U 60
#kc_select CFSG.KD.YMS432C TT0 TT0_ 255
#kc_select CFSG.KD.YMS432C TT1 TT1_ 126
#kc_select CFSG.KD.YMS432C TT2 TT2_ 60
#kc_select CFSG.KD.YMS432C TT3 TT3_ 24
#kc_select CFSG.KD.YMS432C TT4 TT4_ 16
#kc_select CFSG.KD.YMS432C TT5 TT5_ 8
#kc_select CFSG.KD.YMS432C TT6 TT6_ 2
#kc_select CFSG.KD.YMS432C TT7 TT7_ 2
#kc_select CFSG.KD.YMS432C TT8 TT8_ 2
@[expose] noncomputable def TT (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (TT8) TT7 (Nat.beq i 7)) TT6 (Nat.beq i 6)) TT5 (Nat.beq i 5)) TT4 (Nat.beq i 4)) TT3 (Nat.beq i 3)) TT2 (Nat.beq i 2)) TT1 (Nat.beq i 1)) TT0 (Nat.beq i 0)

end CFSG.KD.YMS432C

end
