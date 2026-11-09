module

public import CFSG.Certificates.Kernel.KDenseP.Norton.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13CheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ElevenCheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenCheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenEligibleDefs
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.Norton CFSG.AGLEmbedding.Norton.MON5_7 in
@[expose] def CFSG.KD.NRT.c125371.P : Prs := tri (tbTreePairs tbB1 tbXTree tbXTreeC [9, 10, 11]) []

#kc_plan CFSG.KD.NRT.c125371 "c125371.plan.txt" 10895 5243229756939558425
#kc_plan CFSG.KD.NRT.c125371 "c125371.grp.txt" 7264 5492751417717773607
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX0.bin" 63707 13872984171410190597
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW0.bin" 65535 5823719485336550909
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX1.bin" 63707 4443904139644140653
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW1.bin" 65535 7787471911744512840
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX2.bin" 63703 12435118511986311128
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW2.bin" 65535 8446556182230700373
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX3.bin" 63707 3131324319067948596
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW3.bin" 65535 4640884246421762147
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX4.bin" 63703 7761326490675038060
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW4.bin" 65535 11642763784444888080
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX5.bin" 63707 14953710895762289072
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW5.bin" 65535 6626000012890861317
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX6.bin" 63707 16462390579224444444
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW6.bin" 65535 15015694281036153384
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX7.bin" 63699 16910344583150057044
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW7.bin" 65535 7387358161580559548
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX8.bin" 63707 14062778714890381641
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW8.bin" 65535 4985849040354992744
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX9.bin" 63707 6641506736569476678
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW9.bin" 65535 10574368580222969616
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX10.bin" 63707 6861535399700443044
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW10.bin" 65535 5796210891971341868
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX11.bin" 63703 1513793211472184284
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW11.bin" 65535 4545379249021603293
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX12.bin" 63707 629549304159283391
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW12.bin" 65535 17835952180593383536
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX13.bin" 63707 6791017628590981248
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW13.bin" 65535 927876206852902200
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX14.bin" 63707 3567962584768683349
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW14.bin" 65535 5592554543781848042
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX15.bin" 63707 18240600772401906000
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW15.bin" 65535 14732982342972148935
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX16.bin" 63707 12201134896493836651
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW16.bin" 65535 860958750585404805
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX17.bin" 63703 8330365999813414000
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW17.bin" 65535 4189301325531648098
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX18.bin" 63707 5408273746061067868
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW18.bin" 65535 8612389591914217790
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX19.bin" 63707 11350902438217682923
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW19.bin" 65535 18314536176291980316
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX20.bin" 63707 16476231905482612347
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW20.bin" 65535 5757703965690023246
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX21.bin" 63703 12729613706595546586
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW21.bin" 65535 10411661004877808957
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX22.bin" 63707 1642191596354289074
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW22.bin" 65535 13009594339845996489
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX23.bin" 63707 3516891297667366598
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW23.bin" 65535 8908271657183233535
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX24.bin" 63707 16635545658758746145
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW24.bin" 65535 12821159600858052012
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX25.bin" 63707 1700117511233481671
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW25.bin" 65535 191463617123500528
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX26.bin" 63707 9809161617362527566
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW26.bin" 65535 5943717093185020385
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX27.bin" 63699 13263879267779642491
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW27.bin" 65535 4533788318716629713
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX28.bin" 63707 12580971634380918815
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW28.bin" 65535 6809779436666390941
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX29.bin" 63707 171250095146584593
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW29.bin" 65534 8286780315763821145
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX30 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX30.bin" 63703 14198873073959975666
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW30 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW30.bin" 65535 5085663316580635101
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX31 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX31.bin" 63707 3655571552368624280
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW31 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW31.bin" 65535 2009690898584551291
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX32 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX32.bin" 63703 11474254398045401146
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW32 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW32.bin" 65535 9197281966198472160
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX33 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX33.bin" 63707 2102461992468746049
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW33 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW33.bin" 65535 12161313511944636104
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX34 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX34.bin" 63707 758081462902811760
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW34 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW34.bin" 65535 13306822651544675956
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX35 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX35.bin" 63703 13668323970817153571
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW35 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW35.bin" 65535 6154738032043618825
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX36 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX36.bin" 63707 696003349332147318
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW36 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW36.bin" 65535 18027825728234165978
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX37 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX37.bin" 63707 1930903599626363473
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW37 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW37.bin" 65535 10516948558344218095
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX38 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX38.bin" 63707 7639907093211089718
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW38 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW38.bin" 65535 1612477683938007384
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX39 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX39.bin" 63707 16931530589024357848
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW39 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW39.bin" 65535 6718357115944618228
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX40 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX40.bin" 63707 4628489687715155721
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW40 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW40.bin" 65535 3531771642803589628
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX41 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX41.bin" 63703 9469214760630082536
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW41 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW41.bin" 65535 7997602628759460096
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX42 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX42.bin" 63703 15427734632662498604
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW42 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW42.bin" 65535 3784242693683174843
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX43 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX43.bin" 63707 9555783225041598150
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW43 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW43.bin" 65535 926649313389969500
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX44 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX44.bin" 63707 13913521799500254087
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW44 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW44.bin" 65535 12889680901325375354
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX45 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX45.bin" 63707 9881742184875980655
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW45 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW45.bin" 65535 7145750846322881449
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX46 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX46.bin" 63707 5854567982011523982
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW46 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW46.bin" 65535 2225497413726816429
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX47 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX47.bin" 63703 1676935063417940013
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW47 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW47.bin" 65535 17469029041420777312
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX48 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX48.bin" 63699 17781478720022245816
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW48 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW48.bin" 65535 4671427191839241070
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX49 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX49.bin" 63703 7325248939605106628
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW49 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW49.bin" 65535 3482867793279170855
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX50 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX50.bin" 63699 9361842726688630110
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW50 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW50.bin" 65535 6172691210476319026
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX51 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX51.bin" 63699 4414072265011644244
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW51 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW51.bin" 65535 10936269453748323044
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX52 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX52.bin" 63707 16276046456683638874
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW52 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW52.bin" 65535 12454233608365119534
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX53 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX53.bin" 63707 6152716147866687208
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW53 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW53.bin" 65535 1742916598754074731
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX54 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX54.bin" 63695 13385573624278363743
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW54 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW54.bin" 65535 1408333938237865185
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX55 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX55.bin" 63707 11561071228449001059
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW55 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW55.bin" 65535 4090645525356141196
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX56 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX56.bin" 63707 12228436644065870291
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW56 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW56.bin" 65535 5078415369433887874
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX57 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX57.bin" 63707 6133502967479768551
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW57 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW57.bin" 65535 2499353185801843290
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX58 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX58.bin" 63707 6000750996951160756
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW58 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW58.bin" 65535 14436300540431087862
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX59 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX59.bin" 63703 16049858627793854314
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW59 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW59.bin" 65535 8004531039848981595
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX60 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX60.bin" 63707 2423294991322458348
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW60 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW60.bin" 65535 18114857976812073099
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX61 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX61.bin" 63707 7298165615056722188
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW61 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW61.bin" 65535 1487408746128824692
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX62 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX62.bin" 63707 8563322733551324579
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW62 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW62.bin" 65535 10067460454075617134
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX63 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX63.bin" 63703 13566182263761857780
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW63 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW63.bin" 65535 3330473575582346032
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX64 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX64.bin" 63699 5566667775357197135
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW64 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW64.bin" 65535 3051184105735998362
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX65 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX65.bin" 63707 3527799771785113229
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW65 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW65.bin" 65535 6555924980275252780
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX66 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX66.bin" 63703 16325619472269204943
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW66 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW66.bin" 65535 945230900279800344
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX67 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX67.bin" 63703 13892313213017986773
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW67 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW67.bin" 65535 5157096532212931940
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX68 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX68.bin" 63699 15985991643742460661
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW68 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW68.bin" 65535 12233326868192386987
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX69 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX69.bin" 63707 4433549929140377376
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW69 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW69.bin" 65535 11147988093727915031
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX70 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX70.bin" 63707 3126497210529629528
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW70 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW70.bin" 65535 2486733428445396016
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX71 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX71.bin" 63707 15821121611458341789
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW71 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW71.bin" 65535 16862680405853342020
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX72 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX72.bin" 63707 17036910408944528270
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW72 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW72.bin" 65535 9901013148459378520
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX73 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX73.bin" 63707 9954864342623061008
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW73 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW73.bin" 65535 8946046160689868215
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX74 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX74.bin" 63707 3581636456100783966
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW74 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW74.bin" 65535 12627320401021181198
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX75 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX75.bin" 63699 16732354201180555883
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW75 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW75.bin" 65535 9049895324573740136
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX76 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX76.bin" 63707 3849631863464979179
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW76 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW76.bin" 65535 5136368540560540146
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX77 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX77.bin" 63699 10637039125099487154
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW77 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW77.bin" 65535 3410210613990156998
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX78 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX78.bin" 63707 1389429686979928334
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW78 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW78.bin" 65535 7912776742214181638
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX79 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX79.bin" 63707 17705277845320190045
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW79 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW79.bin" 65535 9818241063745905469
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX80 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX80.bin" 63703 14884211513622544761
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW80 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW80.bin" 65535 15317510816428775040
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX81 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX81.bin" 63707 1586764157578661725
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW81 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW81.bin" 65535 2821482171156496011
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX82 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX82.bin" 63707 3810517749858241344
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW82 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW82.bin" 65535 12095896618755738535
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX83 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX83.bin" 63707 3176699284946787367
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW83 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW83.bin" 65535 7053753929569246810
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX84 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX84.bin" 63703 9366062518990864826
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW84 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW84.bin" 65535 10798657793121429650
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX85 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX85.bin" 63703 8914013257587663335
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW85 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW85.bin" 65535 3492311967774961710
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX86 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX86.bin" 63707 10697667160731039561
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW86 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW86.bin" 65535 14788828685112247746
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX87 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX87.bin" 63707 2196867572064991745
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW87 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW87.bin" 65535 12772453311977104010
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX88 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX88.bin" 63703 2888843653295253680
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW88 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW88.bin" 65535 2918645363661302771
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX89 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX89.bin" 63707 14198592405971369154
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW89 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW89.bin" 65535 13647969065223502914
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX90 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX90.bin" 63703 8075636501093545378
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW90 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW90.bin" 65535 5088741457660536577
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX91 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX91.bin" 63703 12717778907497906492
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW91 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW91.bin" 65535 11879228345293725784
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX92 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX92.bin" 63703 1694178367811157567
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW92 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW92.bin" 65535 4159412048416023173
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX93 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX93.bin" 63699 9225429373771922110
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW93 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW93.bin" 65535 5054993171780664182
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX94 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX94.bin" 63703 12329082513183528885
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW94 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW94.bin" 65535 14440881614631829496
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX95 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX95.bin" 63707 16183610163846726800
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW95 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW95.bin" 65535 16564505492257030633
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX96 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX96.bin" 63707 7276332378884446131
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW96 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW96.bin" 65535 3578202196945196727
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX97 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX97.bin" 63703 15852381917853594262
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW97 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW97.bin" 65534 5923364279141151803
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX98 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX98.bin" 63703 2472190729310189445
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW98 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW98.bin" 65535 5449319399406292487
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX99 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX99.bin" 63703 17431382084296060361
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW99 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW99.bin" 65535 15800320848045326159
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX100 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX100.bin" 63707 1063848489987696292
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW100 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW100.bin" 65535 691005178194440009
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX101 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX101.bin" 63707 8250899709691525598
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW101 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW101.bin" 65535 6702580398793001952
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX102 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX102.bin" 63707 7626038063541280518
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW102 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW102.bin" 65535 9703826981463276983
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX103 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX103.bin" 63703 3112196063501263513
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW103 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW103.bin" 65535 10520316530455413183
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX104 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX104.bin" 63707 11063561505433685854
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW104 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW104.bin" 65535 4467289660815119243
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX105 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX105.bin" 63703 7241413145129802364
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW105 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW105.bin" 65535 5082903704353738967
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX106 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX106.bin" 63707 1474387569594806523
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW106 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW106.bin" 65535 233214583362652288
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX107 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX107.bin" 63703 6943341627613691286
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW107 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW107.bin" 65535 7991887665491245751
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX108 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX108.bin" 63707 14280503618380291524
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW108 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW108.bin" 65533 17274657111254604497
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX109 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX109.bin" 63707 4554027570909660209
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW109 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW109.bin" 65535 4778021548838758267
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX110 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX110.bin" 63699 4525170186123745677
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW110 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW110.bin" 65535 11373031561860588799
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX111 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX111.bin" 63703 12765865321152315540
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW111 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW111.bin" 65535 3012771602861540523
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX112 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX112.bin" 63707 12775193921469225947
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW112 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW112.bin" 65535 9446954467674837213
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX113 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX113.bin" 63707 4637190585282167279
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW113 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW113.bin" 65535 12901726570704912344
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX114 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX114.bin" 63707 5239110360087942788
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW114 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW114.bin" 65535 429545620834046121
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX115 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX115.bin" 63707 11179252833897158718
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW115 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW115.bin" 65535 6360879194349628373
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX116 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX116.bin" 63707 7397411583954043380
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW116 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW116.bin" 65535 3036421067319477839
#kc_plan CFSG.KD.NRT.c125371 "c125371.rec.txt" 113028 17897074128419723074
#kc_select CFSG.KD.NRT.c125371 CH CH 234
#kc_select CFSG.KD.NRT.c125371 PRf PR 120
#kc_select CFSG.KD.NRT.c125371 GKf GK 234
#kc_select CFSG.KD.NRT.c125371 DPf DP 234
#kc_listDispatch CFSG.KD.NRT.c125371 Gf G 115
#kc_select CFSG.KD.NRT.c125371 RXf RX 117
#kc_select CFSG.KD.NRT.c125371 RAf RA 117
#kc_select CFSG.KD.NRT.c125371 RWf RW 117

namespace CFSG.KD.NRT.c125371

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 120) g

end CFSG.KD.NRT.c125371

#kc_each CFSG.KD.NRT.c125371.u 0 115

end
