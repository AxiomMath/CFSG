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
@[expose] def CFSG.KD.NRT.c125369.P : Prs := tri (tbTreePairs tbB1 tbXTree tbXTreeC [3, 4, 5]) []

#kc_plan CFSG.KD.NRT.c125369 "c125369.plan.txt" 9969 2647408221371961874
#kc_plan CFSG.KD.NRT.c125369 "c125369.grp.txt" 6614 9411735251488576993
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX0.bin" 63707 13872984171410190597
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW0.bin" 65535 5823719485336550909
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX1.bin" 63707 4443904139644140653
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW1.bin" 65535 7787471911744512840
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX2.bin" 63703 12435118511986311128
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW2.bin" 65535 8446556182230700373
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX3.bin" 63703 4712234261441791674
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW3.bin" 65535 6965409381304681471
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX4.bin" 63707 14953710895762289072
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW4.bin" 65535 6626000012890861317
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX5.bin" 63703 12097183633896228864
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW5.bin" 65535 18200375276429292273
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX6.bin" 63703 15057591045986704811
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW6.bin" 65535 4560376121318419533
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX7.bin" 63707 3213063529769478591
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW7.bin" 65535 10561078099272248174
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX8.bin" 63699 18234553899659347716
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW8.bin" 65535 13935328559096864278
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX9.bin" 63707 15229077279178563287
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW9.bin" 65535 6229946604756887417
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX10.bin" 63707 9867932223802125210
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW10.bin" 65535 16992683738233021342
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX11.bin" 63707 1207885505744703721
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW11.bin" 65535 9424712327268425537
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX12.bin" 63707 17365631594358771241
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW12.bin" 65535 5317758451759664505
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX13.bin" 63707 11805638329616978719
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW13.bin" 65535 1163270986351666501
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX14.bin" 63707 16084974923656059299
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW14.bin" 65535 1285988994839809445
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX15.bin" 63707 4589425266932225302
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW15.bin" 65535 852060287314599957
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX16.bin" 63703 9133117675817857339
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW16.bin" 65535 11739513708182494051
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX17.bin" 63707 10954575482416209274
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW17.bin" 65535 3549099647058338915
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX18.bin" 63703 13437514617602371535
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW18.bin" 65535 7180507879609572326
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX19.bin" 63703 5172211391583885898
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW19.bin" 65535 11275004651616302160
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX20.bin" 63707 9487164743548641690
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW20.bin" 65535 3953667914216397406
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX21.bin" 63707 11048600308398680491
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW21.bin" 65535 12026418926503099973
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX22.bin" 63703 6936406192395055684
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW22.bin" 65535 6729190635924345495
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX23.bin" 63707 2928773334585866730
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW23.bin" 65535 6498109015886794591
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX24.bin" 63707 5187356521839478491
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW24.bin" 65535 15106572924394331541
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX25.bin" 63707 16094277090734798220
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW25.bin" 65535 11632961150368232670
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX26.bin" 63703 14348528932095105510
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW26.bin" 65535 11797696188901308300
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX27.bin" 63707 16642884080025547906
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW27.bin" 65535 3614803542081286803
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX28.bin" 63707 109784880295306493
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW28.bin" 65535 18422749555144064380
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX29.bin" 63707 14018728008207912342
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW29.bin" 65535 6975216414198976960
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX30 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX30.bin" 63703 4337481851443493468
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW30 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW30.bin" 65535 8344945239091572677
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX31 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX31.bin" 63707 10032220220481781505
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW31 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW31.bin" 65535 642628441499607551
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX32 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX32.bin" 63707 8242957694793477695
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW32 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW32.bin" 65535 10036182086761360219
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX33 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX33.bin" 63707 17549237731044383611
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW33 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW33.bin" 65535 18134570092934652990
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX34 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX34.bin" 63699 1320680449680254336
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW34 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW34.bin" 65535 11081239612069796204
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX35 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX35.bin" 63707 10758474456355311522
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW35 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW35.bin" 65535 8703522122013465163
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX36 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX36.bin" 63707 5138382901227568560
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW36 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW36.bin" 65535 9451092035784047726
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX37 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX37.bin" 63703 6149645315598338717
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW37 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW37.bin" 65535 7446962803310469816
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX38 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX38.bin" 63707 3490903841304853065
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW38 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW38.bin" 65535 14704154868539731992
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX39 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX39.bin" 63707 16931530589024357848
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW39 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW39.bin" 65535 6718357115944618228
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX40 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX40.bin" 63707 4628489687715155721
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW40 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW40.bin" 65535 3531771642803589628
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX41 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX41.bin" 63703 9469214760630082536
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW41 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW41.bin" 65535 7997602628759460096
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX42 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX42.bin" 63703 1293664048099716689
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW42 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW42.bin" 65535 1537000046818849731
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX43 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX43.bin" 63707 13913521799500254087
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW43 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW43.bin" 65535 12889680901325375354
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX44 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX44.bin" 63707 14826124828400804976
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW44 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW44.bin" 65535 12332106572702387981
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX45 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX45.bin" 63707 17596666301993830769
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW45 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW45.bin" 65535 17637331232741332722
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX46 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX46.bin" 63707 10947923663219019605
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW46 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW46.bin" 65535 16207728934437357748
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX47 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX47.bin" 63707 15213529922786500430
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW47 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW47.bin" 65535 3029052641369459408
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX48 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX48.bin" 63703 3009070878555694871
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW48 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW48.bin" 65535 2127841325425895011
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX49 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX49.bin" 63707 10866913694582633496
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW49 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW49.bin" 65535 12578068153196048414
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX50 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX50.bin" 63703 17216221243652555706
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW50 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW50.bin" 65535 6006201031053073114
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX51 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX51.bin" 63707 9412508058798426861
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW51 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW51.bin" 65535 3406974314087808461
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX52 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX52.bin" 63707 11017108836740887782
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW52 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW52.bin" 65535 5468508870246982296
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX53 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX53.bin" 63703 9578254439083624194
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW53 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW53.bin" 65535 1543133529680456036
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX54 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX54.bin" 63707 3032498440294632398
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW54 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW54.bin" 65535 16956080557500621354
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX55 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX55.bin" 63707 11938405638139266797
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW55 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW55.bin" 65535 8576110681392474438
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX56 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX56.bin" 63707 7404120025173115930
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW56 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW56.bin" 65535 3960171686451933555
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX57 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX57.bin" 63703 12162095031481254172
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW57 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW57.bin" 65535 8515916985388067089
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX58 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX58.bin" 63707 17891295721923017499
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW58 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW58.bin" 65535 8386012075544062323
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX59 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX59.bin" 63703 15513119749283057782
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW59 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW59.bin" 65535 7818120650915138564
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX60 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX60.bin" 63703 4018835756410084809
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW60 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW60.bin" 65535 16544537932903931746
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX61 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX61.bin" 63703 8726781948904243785
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW61 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW61.bin" 65535 15821486182697358629
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX62 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX62.bin" 63703 17591698283176077340
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW62 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW62.bin" 65535 555653152806320501
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX63 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX63.bin" 63703 7824070063777084047
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW63 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW63.bin" 65535 16424688332764782655
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX64 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX64.bin" 63707 17063668630185627200
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW64 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW64.bin" 65535 3338695962167709353
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX65 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX65.bin" 63703 5856971505778352499
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW65 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW65.bin" 65535 10035612483802661108
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX66 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX66.bin" 63707 7289367154582788507
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW66 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW66.bin" 65535 8540127982302277272
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX67 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX67.bin" 63707 2206787873982500586
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW67 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW67.bin" 65535 8938324373716871890
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX68 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX68.bin" 63707 1604942013610080801
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW68 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW68.bin" 65535 7292523982291830056
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX69 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX69.bin" 63707 9465136077848692476
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW69 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW69.bin" 65535 6272248296413116510
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX70 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX70.bin" 63707 18123162257244399445
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW70 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW70.bin" 65535 5182935435709161620
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX71 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX71.bin" 63707 13971239877227568809
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW71 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW71.bin" 65535 3460354408029534784
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX72 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX72.bin" 63707 9495766465766513728
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW72 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW72.bin" 65535 585896179653063922
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX73 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX73.bin" 63699 3723217181383961241
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW73 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW73.bin" 65535 7461689934283480025
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX74 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX74.bin" 63707 10932465580668394459
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW74 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW74.bin" 65535 12759896403237726060
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX75 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX75.bin" 63699 3735019170660092450
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW75 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW75.bin" 65535 10482958041775698815
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX76 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX76.bin" 63707 5734830152048786963
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW76 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW76.bin" 65535 8534033616271107069
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX77 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX77.bin" 63707 9336110022906136126
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW77 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW77.bin" 65535 1469409176622648342
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX78 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX78.bin" 63707 1389429686979928334
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW78 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW78.bin" 65535 7912776742214181638
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX79 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX79.bin" 63707 17705277845320190045
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW79 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW79.bin" 65535 9818241063745905469
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX80 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX80.bin" 63703 14884211513622544761
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW80 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW80.bin" 65535 15317510816428775040
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX81 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX81.bin" 63703 4619101474584098126
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW81 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW81.bin" 65535 1871259195548517539
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX82 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX82.bin" 63707 3176699284946787367
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW82 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW82.bin" 65535 7053753929569246810
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX83 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX83.bin" 63707 5049391544724724127
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW83 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW83.bin" 65535 1445118244161803110
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX84 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX84.bin" 63707 7253874895467889972
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW84 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW84.bin" 65535 17044712172619575762
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX85 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX85.bin" 63707 15628028937254965952
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW85 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW85.bin" 65535 4776931594961566626
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX86 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX86.bin" 63703 12864527261168943975
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW86 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW86.bin" 65535 1761420166036933364
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX87 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX87.bin" 63703 687825662641841000
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW87 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW87.bin" 65535 11504415738390082345
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX88 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX88.bin" 63703 13788874663718595407
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW88 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW88.bin" 65535 5512933585695136999
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX89 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX89.bin" 63707 9881784523778210435
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW89 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW89.bin" 65535 1997921116510784123
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX90 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX90.bin" 63707 6789995163232477140
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW90 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW90.bin" 65535 752756768208867555
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX91 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX91.bin" 63707 17363534647883391161
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW91 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW91.bin" 65535 5310461326447231339
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX92 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX92.bin" 63703 6040917680441057561
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW92 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW92.bin" 65535 15687918965045238987
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX93 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX93.bin" 63703 10881510212945439505
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW93 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW93.bin" 65535 17580713554399139358
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX94 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX94.bin" 63707 4434346323020181640
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW94 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW94.bin" 65535 5834272334868059512
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX95 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX95.bin" 63707 18090702415322942192
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW95 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW95.bin" 65535 8220465065791490965
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX96 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX96.bin" 63703 14376777857506638410
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW96 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW96.bin" 65535 7205567803540017756
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX97 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX97.bin" 63703 12997171986023778060
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW97 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW97.bin" 65535 17381283661987202243
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX98 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX98.bin" 63707 10676958344677129431
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW98 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW98.bin" 65535 16912063764265445433
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX99 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX99.bin" 63707 9920007027714298495
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW99 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW99.bin" 65535 8050200041337291524
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX100 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX100.bin" 63699 17915317520165631017
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW100 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW100.bin" 65535 3303093926324379525
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX101 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX101.bin" 63707 4382483418105785312
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW101 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW101.bin" 65535 3687159813375786979
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX102 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX102.bin" 63703 18435577821920861283
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW102 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW102.bin" 65535 15814832028053337101
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX103 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX103.bin" 63707 8026072494762565295
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW103 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW103.bin" 65535 865184266865409859
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX104 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX104.bin" 63703 12727419657872917469
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW104 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW104.bin" 65535 16897572678781864606
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX105 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX105.bin" 63707 13782947827231507303
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW105 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW105.bin" 65535 11815761264460704210
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX106 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX106.bin" 63707 10245687675419926389
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW106 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW106.bin" 65535 13787917751444760856
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX107 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX107.bin" 63707 9881002456146073481
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW107 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW107.bin" 65535 13059476974261656654
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX108 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX108.bin" 63703 6408496629482774006
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW108 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW108.bin" 65535 11702604867001118295
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX109 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX109.bin" 63707 8305389803819933841
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW109 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW109.bin" 65535 18300298276782515625
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX110 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX110.bin" 63707 13041964041496665720
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW110 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW110.bin" 65535 10298897045178519505
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX111 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX111.bin" 63707 16877255312228991996
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW111 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW111.bin" 65535 16149299429497291806
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX112 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX112.bin" 63703 6607323853654321979
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW112 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW112.bin" 65535 15108539577423359286
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX113 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX113.bin" 63703 207243200319154022
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW113 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW113.bin" 65535 8310362942969650345
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX114 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX114.bin" 63707 7174827245305443478
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW114 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW114.bin" 65535 16487628551396639543
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX115 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX115.bin" 63699 5730224418573797160
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW115 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW115.bin" 65535 14052837414844459160
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX116 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX116.bin" 63707 12558789667138784826
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW116 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW116.bin" 65535 7216005059135823630
#kc_plan CFSG.KD.NRT.c125369 "c125369.rec.txt" 113022 7269934676149556485
#kc_select CFSG.KD.NRT.c125369 CH CH 204
#kc_select CFSG.KD.NRT.c125369 PRf PR 120
#kc_select CFSG.KD.NRT.c125369 GKf GK 204
#kc_select CFSG.KD.NRT.c125369 DPf DP 204
#kc_listDispatch CFSG.KD.NRT.c125369 Gf G 112
#kc_select CFSG.KD.NRT.c125369 RXf RX 117
#kc_select CFSG.KD.NRT.c125369 RAf RA 117
#kc_select CFSG.KD.NRT.c125369 RWf RW 117

namespace CFSG.KD.NRT.c125369

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 120) g

end CFSG.KD.NRT.c125369

#kc_each CFSG.KD.NRT.c125369.u 0 112

end
