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
@[expose] def CFSG.KD.NRT.c125370.P : Prs := tri (tbTreePairs tbB1 tbXTree tbXTreeC [6, 7, 8]) []

#kc_plan CFSG.KD.NRT.c125370 "c125370.plan.txt" 9877 1297271672023684385
#kc_plan CFSG.KD.NRT.c125370 "c125370.grp.txt" 6566 12576032689826532876
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX0.bin" 63707 13872984171410190597
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW0.bin" 65535 5823719485336550909
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX1.bin" 63707 4443904139644140653
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW1.bin" 65535 7787471911744512840
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX2.bin" 63703 12435118511986311128
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW2.bin" 65535 8446556182230700373
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX3.bin" 63707 5681744666874536373
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW3.bin" 65535 8244773723561964722
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX4.bin" 63707 3203111906318550375
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW4.bin" 65535 16124494055102240248
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX5.bin" 63691 2950338712238044721
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW5.bin" 65535 10725688207867971251
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX6.bin" 63707 13593376804804853050
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW6.bin" 65535 8990634652030886345
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX7.bin" 63703 16289322276904989126
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW7.bin" 65535 9212600821709495288
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX8.bin" 63703 13046641812701372361
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW8.bin" 65535 14022905327225425141
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX9.bin" 63699 3622836150931249759
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW9.bin" 65535 9344193006495051281
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX10.bin" 63699 9726064089539140978
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW10.bin" 65535 16468257171692345164
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX11.bin" 63703 14880822394981244631
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW11.bin" 65535 12397829920878912450
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX12.bin" 63703 4013156000363631128
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW12.bin" 65535 5395603459338339879
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX13.bin" 63707 1929039818221768661
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW13.bin" 65535 4410326861164460450
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX14.bin" 63703 7997255666569504469
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW14.bin" 65535 7131391624669874254
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX15.bin" 63707 1525837186686164011
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW15.bin" 65535 3404207656018174951
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX16.bin" 63707 9835880086296344168
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW16.bin" 65535 12525122179492394725
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX17.bin" 63707 5659475079159312498
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW17.bin" 65535 14095021201400383414
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX18.bin" 63699 7804060737584332652
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW18.bin" 65535 391635646712422145
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX19.bin" 63707 11764694777351920727
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW19.bin" 65535 9323368569829037163
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX20.bin" 63707 1061759129726010045
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW20.bin" 65535 7937650973358069691
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX21.bin" 63707 3917492370326885766
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW21.bin" 65535 1374921917871090821
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX22.bin" 63707 7383212902148767518
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW22.bin" 65535 13406090247827253506
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX23.bin" 63699 47631702884262587
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW23.bin" 65535 6060724669910685854
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX24.bin" 63703 860309055438437757
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW24.bin" 65535 11070554083072899785
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX25.bin" 63699 1059425084613742894
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW25.bin" 65535 3286989655732462218
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX26.bin" 63703 8321563893503437436
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW26.bin" 65535 10526039394815424016
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX27.bin" 63707 3485644165504619847
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW27.bin" 65535 14757955389720066944
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX28.bin" 63707 4359494145676332812
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW28.bin" 65535 9811892923962415385
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX29.bin" 63703 6802902636710416253
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW29.bin" 65535 5231529676401105279
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX30 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX30.bin" 63707 4166602506374746623
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW30 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW30.bin" 65535 2462280916912721782
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX31 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX31.bin" 63703 15800708471748442449
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW31 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW31.bin" 65535 18420674160238401833
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX32 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX32.bin" 63703 6270865949389307386
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW32 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW32.bin" 65535 2541964528319768019
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX33 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX33.bin" 63707 15994398185100557170
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW33 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW33.bin" 65535 11488482706469807948
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX34 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX34.bin" 63703 593602890922725307
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW34 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW34.bin" 65535 4788013398870794955
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX35 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX35.bin" 63699 5083750266637847318
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW35 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW35.bin" 65535 14040230280718706662
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX36 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX36.bin" 63703 6800312333743524044
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW36 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW36.bin" 65535 13144116634665681699
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX37 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX37.bin" 63707 9155702136097323627
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW37 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW37.bin" 65535 2661658908975489500
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX38 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX38.bin" 63707 16931530589024357848
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW38 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW38.bin" 65535 6718357115944618228
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX39 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX39.bin" 63707 4628489687715155721
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW39 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW39.bin" 65535 3531771642803589628
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX40 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX40.bin" 63703 9469214760630082536
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW40 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW40.bin" 65535 7997602628759460096
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX41 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX41.bin" 63699 13708155445942188279
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW41 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW41.bin" 65535 8884011441040400193
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX42 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX42.bin" 63707 17355549309997543380
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW42 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW42.bin" 65535 5594939532425378682
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX43 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX43.bin" 63707 12564273422135038181
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW43 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW43.bin" 65535 9315782771628803430
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX44 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX44.bin" 63707 10813709479830208971
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW44 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW44.bin" 65535 11376658579641774189
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX45 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX45.bin" 63707 1268880290305024571
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW45 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW45.bin" 65535 13055412247684649352
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX46 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX46.bin" 63707 13721212828893950021
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW46 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW46.bin" 65535 5383959650515258927
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX47 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX47.bin" 63703 18131425193515117663
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW47 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW47.bin" 65535 8319366307636237548
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX48 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX48.bin" 63703 3155474984895988895
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW48 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW48.bin" 65535 16527247689047961102
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX49 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX49.bin" 63707 18328457558038209918
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW49 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW49.bin" 65535 12058558838994140256
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX50 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX50.bin" 63707 16770102092470788121
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW50 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW50.bin" 65535 10855935227764427209
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX51 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX51.bin" 63699 9011699596459028082
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW51 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW51.bin" 65535 11250941475515711203
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX52 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX52.bin" 63707 1346763536084870037
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW52 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW52.bin" 65535 2242981603628907933
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX53 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX53.bin" 63695 7682341106064320910
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW53 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW53.bin" 65535 18321343386581102032
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX54 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX54.bin" 63703 16196314794268597662
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW54 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW54.bin" 65535 10050783629727121306
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX55 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX55.bin" 63703 2263046150380110396
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW55 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW55.bin" 65535 350090794291353710
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX56 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX56.bin" 63703 17885401189693284932
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW56 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW56.bin" 65535 7282474830015591393
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX57 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX57.bin" 63699 14142811997966976155
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW57 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW57.bin" 65535 11343155735804394343
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX58 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX58.bin" 63707 6141409773366700267
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW58 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW58.bin" 65535 6192958840118665651
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX59 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX59.bin" 63707 6147849785093505696
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW59 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW59.bin" 65535 858971836347696457
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX60 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX60.bin" 63707 11036489324057988841
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW60 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW60.bin" 65535 16265792602502248295
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX61 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX61.bin" 63707 13198230490968299839
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW61 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW61.bin" 65535 3262667461694242353
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX62 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX62.bin" 63707 15754683796629744636
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW62 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW62.bin" 65535 8753468821637305629
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX63 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX63.bin" 63707 9232351933574693696
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW63 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW63.bin" 65535 13676757976196613357
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX64 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX64.bin" 63707 13574896643968415635
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW64 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW64.bin" 65535 6409400186475270845
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX65 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX65.bin" 63699 14801558611551159157
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW65 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW65.bin" 65535 1348905697655474839
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX66 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX66.bin" 63707 8863895090550281749
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW66 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW66.bin" 65535 16540320553516343236
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX67 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX67.bin" 63707 1237702808259393102
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW67 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW67.bin" 65535 17215376755719193493
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX68 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX68.bin" 63707 15480090998862798175
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW68 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW68.bin" 65535 532034566590268750
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX69 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX69.bin" 63703 6512281690450735956
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW69 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW69.bin" 65535 17195330258257643788
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX70 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX70.bin" 63707 4785490514291702504
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW70 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW70.bin" 65535 14327484310946516450
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX71 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX71.bin" 63707 15629073351872991968
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW71 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW71.bin" 65535 10155034889317969867
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX72 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX72.bin" 63703 12361173492001573840
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW72 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW72.bin" 65535 471449901498068850
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX73 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX73.bin" 63703 8009544191012525646
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW73 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW73.bin" 65535 11973219798691096311
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX74 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX74.bin" 63699 6671971788915067853
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW74 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW74.bin" 65535 16637295236650439361
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX75 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX75.bin" 63707 5048062992868354902
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW75 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW75.bin" 65535 17660051957763664119
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX76 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX76.bin" 63707 1389429686979928334
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW76 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW76.bin" 65535 7912776742214181638
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX77 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX77.bin" 63707 17705277845320190045
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW77 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW77.bin" 65535 9818241063745905469
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX78 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX78.bin" 63703 14884211513622544761
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW78 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW78.bin" 65535 15317510816428775040
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX79 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX79.bin" 63707 14748091100376363778
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW79 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW79.bin" 65535 8188484580945345697
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX80 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX80.bin" 63703 14945167830771055778
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW80 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW80.bin" 65535 534866152518884509
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX81 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX81.bin" 63703 2542147408579579879
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW81 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW81.bin" 65535 13714601249233201095
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX82 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX82.bin" 63707 3615986391978373145
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW82 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW82.bin" 65535 795816520510767901
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX83 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX83.bin" 63707 17435386408131901516
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW83 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW83.bin" 65535 3782819075251350954
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX84 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX84.bin" 63703 18081319906149335433
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW84 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW84.bin" 65535 16781886823034538752
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX85 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX85.bin" 63707 10791442740393999523
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW85 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW85.bin" 65535 3635110899592987829
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX86 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX86.bin" 63703 12224776248559925350
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW86 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW86.bin" 65535 4161647546016881817
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX87 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX87.bin" 63707 14761854535043897410
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW87 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW87.bin" 65535 14090780127872573445
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX88 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX88.bin" 63707 17175202216389454139
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW88 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW88.bin" 65535 18299443284205271170
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX89 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX89.bin" 63707 14216266803375612694
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW89 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW89.bin" 65535 10331006950988715098
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX90 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX90.bin" 63707 10048645770210392686
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW90 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW90.bin" 65535 3181619982350964217
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX91 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX91.bin" 63699 12580193005269194333
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW91 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW91.bin" 65535 16546699433455114646
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX92 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX92.bin" 63707 11481004157714617500
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW92 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW92.bin" 65535 16515982369153050759
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX93 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX93.bin" 63707 17288577824891942567
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW93 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW93.bin" 65535 5321826721289403492
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX94 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX94.bin" 63703 12046351720532362726
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW94 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW94.bin" 65534 14133073159510865252
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX95 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX95.bin" 63707 830513720528532674
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW95 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW95.bin" 65535 5184372359499195740
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX96 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX96.bin" 63707 17102169460459362810
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW96 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW96.bin" 65535 870192353977480267
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX97 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX97.bin" 63707 7986706088629015162
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW97 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW97.bin" 65535 7528602997732150078
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX98 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX98.bin" 63703 11952171313303721178
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW98 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW98.bin" 65535 18372605604377203171
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX99 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX99.bin" 63703 2690865280395594040
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW99 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW99.bin" 65535 2570570318822355896
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX100 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX100.bin" 63707 16090336795966639806
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW100 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW100.bin" 65535 9213174374136980629
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX101 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX101.bin" 63707 17992718746262794916
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW101 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW101.bin" 65535 10682997034944661714
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX102 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX102.bin" 63703 6147860117332031692
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW102 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW102.bin" 65535 3744902962905431234
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX103 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX103.bin" 63703 3004449162900318186
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW103 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW103.bin" 65535 5723303921076960764
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX104 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX104.bin" 63703 17604842250427751128
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW104 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW104.bin" 65535 213641614509476371
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX105 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX105.bin" 63703 14845046774552711020
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW105 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW105.bin" 65535 2240155789381022153
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX106 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX106.bin" 63707 15959816678061588216
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW106 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW106.bin" 65535 9476220899931302767
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX107 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX107.bin" 63703 1511938125852835606
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW107 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW107.bin" 65535 16111882957358581592
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX108 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX108.bin" 63707 3885351243553061181
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW108 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW108.bin" 65535 1994965519400074164
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX109 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX109.bin" 63699 11888809097862713838
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW109 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW109.bin" 65535 11846394552595288425
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX110 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX110.bin" 63703 5909537866490458240
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW110 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW110.bin" 65535 4907571991391083513
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX111 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX111.bin" 63703 2011167542964999712
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW111 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW111.bin" 65535 8075159607959003389
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX112 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX112.bin" 63699 1074699164106532787
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW112 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW112.bin" 65535 1062957733271432664
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX113 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX113.bin" 63707 14293154382564426243
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW113 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW113.bin" 65535 687582734571990214
#kc_plan CFSG.KD.NRT.c125370 "c125370.rec.txt" 110128 6984180309335814930
#kc_select CFSG.KD.NRT.c125370 CH CH 204
#kc_select CFSG.KD.NRT.c125370 PRf PR 117
#kc_select CFSG.KD.NRT.c125370 GKf GK 204
#kc_select CFSG.KD.NRT.c125370 DPf DP 204
#kc_listDispatch CFSG.KD.NRT.c125370 Gf G 112
#kc_select CFSG.KD.NRT.c125370 RXf RX 114
#kc_select CFSG.KD.NRT.c125370 RAf RA 114
#kc_select CFSG.KD.NRT.c125370 RWf RW 114

namespace CFSG.KD.NRT.c125370

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 117) g

end CFSG.KD.NRT.c125370

#kc_each CFSG.KD.NRT.c125370.u 0 112

end
