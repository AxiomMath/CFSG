module

public import CFSG.Certificates.Kernel.McL.Model
public import CFSG.Certificates.Kernel.McL.Sub
public import CFSG.Certificates.Kernel.McL.RangeX
public import CFSG.Certificates.Kernel.Schur.Pack
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.Schur.M24

@[expose] def M0 : Nat := nat_lit 6736755261288091546128960264285268478067075
@[expose] def M1 : Nat := nat_lit 6736755261288091546128960264285268478067075
@[expose] def M2 : Nat := nat_lit 7765686648183738834401240450036853835597059
@[expose] def M3 : Nat := nat_lit 6399096711543196369546030405101881909109573
#kc_select CFSG.KC.Schur.M24 MG M 4
@[expose] def R0 : Nat := nat_lit 8
@[expose] def R1 : Nat := nat_lit 538976268
@[expose] def R2 : Nat := nat_lit 19239554410385646369007847458680028103495104244371622695877704874278829582481280835664248419261727328996903878840
@[expose] def R3 : Nat := nat_lit 1260893095046136334935276973050772614330815558475180333808555427999657440158504333716903634594949724779217578886172864
@[expose] def R4 : Nat := nat_lit 68352628135791968671869327766455099795025176394078555879763106250048646768019109126946991887093920
@[expose] def R5 : Nat := nat_lit 23871879601792482813206463530518016013799245762050755265074927120534062361147440459939984
@[expose] def R6 : Nat := nat_lit 34888613676033116589051557917617139885789525442668103056043064937140637936145471548441166418043253782599708151083957106741049346876244192
#kc_select CFSG.KC.Schur.M24 REL R 7
@[expose] def EP0 : Nat := nat_lit 6736755261288091546128960264285268478067075
@[expose] def ED0 : Nat := nat_lit 0
@[expose] def EP1 : Nat := nat_lit 6736755261288091546128960264285268478067075
@[expose] def ED1 : Nat := nat_lit 16
@[expose] def EP2 : Nat := nat_lit 7765686648183738834401240450036853835597059
@[expose] def ED2 : Nat := nat_lit 32
@[expose] def EP3 : Nat := nat_lit 6399096711543196369546030405101881909109573
@[expose] def ED3 : Nat := nat_lit 48
@[expose] def EP4 : Nat := nat_lit 3241368146040741372689303833856945299420104
@[expose] def ED4 : Nat := nat_lit 49
@[expose] def EP5 : Nat := nat_lit 1498782124290747773739365074667374688629518
@[expose] def ED5 : Nat := nat_lit 131137
@[expose] def EP6 : Nat := nat_lit 6029046262618485093942376786080482786833410
@[expose] def ED6 : Nat := nat_lit 196673
@[expose] def EP7 : Nat := nat_lit 4307381043608249127691738725289791875768583
@[expose] def ED7 : Nat := nat_lit 81
@[expose] def EP8 : Nat := nat_lit 3611333212897633160590416063466536140857488
@[expose] def ED8 : Nat := nat_lit 97
@[expose] def EP9 : Nat := nat_lit 3605913845154355641160767703139762906079759
@[expose] def ED9 : Nat := nat_lit 131201
@[expose] def EP10 : Nat := nat_lit 3584126740793736749704850412884858129908620
@[expose] def ED10 : Nat := nat_lit 196737
@[expose] def EP11 : Nat := nat_lit 6039941815945743603812996187144921886556493
@[expose] def ED11 : Nat := nat_lit 145
@[expose] def EP12 : Nat := nat_lit 5974612880141228847149193626867230470590916
@[expose] def ED12 : Nat := nat_lit 161
@[expose] def EP13 : Nat := nat_lit 3252263676991827646579899928992333614870529
@[expose] def ED13 : Nat := nat_lit 131249
@[expose] def EP14 : Nat := nat_lit 1509677659439263006081805250821293328613588
@[expose] def ED14 : Nat := nat_lit 196785
@[expose] def EP15 : Nat := nat_lit 3159708082695493548761413203149740389433809
@[expose] def ED15 : Nat := nat_lit 131265
@[expose] def EP16 : Nat := nat_lit 1487906130924913212898660698931971844223433
@[expose] def ED16 : Nat := nat_lit 196801
@[expose] def EP17 : Nat := nat_lit 6393677092668668893586359817224409208115398
@[expose] def ED17 : Nat := nat_lit 209
@[expose] def EP18 : Nat := nat_lit 4301961611017671363647964360208770813411339
@[expose] def ED18 : Nat := nat_lit 225
@[expose] def EP19 : Nat := nat_lit 6339210961517164135058434575074660230116234
@[expose] def ED19 : Nat := nat_lit 241
@[expose] def EP20 : Nat := nat_lit 4236603557856680356189182766386742609838994
@[expose] def ED20 : Nat := nat_lit 257
@[expose] def EP21 : Nat := nat_lit 5629982588660332479420881568017799653372055
@[expose] def ED21 : Nat := nat_lit 131393
@[expose] def EP22 : Nat := nat_lit 5282647232789300432683590013436748372136470
@[expose] def ED22 : Nat := nat_lit 196929
@[expose] def EP23 : Nat := nat_lit 790482965234358474621931418922119650608147
@[expose] def ED23 : Nat := nat_lit 337
@[expose] def EP24 : Nat := nat_lit 4623255934950146152256682151262428634841429
@[expose] def ED24 : Nat := nat_lit 353
@[expose] def EP25 : Nat := nat_lit 6736755261288091546128960264285268478067075
@[expose] def ED25 : Nat := nat_lit 2
@[expose] def EP26 : Nat := nat_lit 7368324654491947369455139188761880720069312
@[expose] def ED26 : Nat := nat_lit 1638433
@[expose] def EP27 : Nat := nat_lit 7368324654491947369455139188761880720069312
@[expose] def ED27 : Nat := nat_lit 268435875
@[expose] def EP28 : Nat := nat_lit 5695333001751290045585927548812072528127047
@[expose] def ED28 : Nat := nat_lit 131185
@[expose] def EP29 : Nat := nat_lit 7765516191243090594428465238112740451095813
@[expose] def ED29 : Nat := nat_lit 114
@[expose] def EP30 : Nat := nat_lit 2537248076194425347457904704668271047676480
@[expose] def ED30 : Nat := nat_lit 1900993
@[expose] def EP31 : Nat := nat_lit 2537248076194425347457904704668271047676480
@[expose] def ED31 : Nat := nat_lit 268435939
@[expose] def EP32 : Nat := nat_lit 7731986772394969437939856040294035773732096
@[expose] def ED32 : Nat := nat_lit 270205361
@[expose] def EP33 : Nat := nat_lit 464322087405109128909462700659268536821184
@[expose] def ED33 : Nat := nat_lit 270467505
@[expose] def EP34 : Nat := nat_lit 4982678086849271371408946445360915019014912
@[expose] def ED34 : Nat := nat_lit 270205425
@[expose] def EP35 : Nat := nat_lit 3888162430619735115986159504342415313220928
@[expose] def ED35 : Nat := nat_lit 270467569
@[expose] def EP36 : Nat := nat_lit 3147965932519297000310288259732963266692032
@[expose] def ED36 : Nat := nat_lit 270205441
@[expose] def EP37 : Nat := nat_lit 6339210624011537526689237831436960453632832
@[expose] def ED37 : Nat := nat_lit 270467585
@[expose] def EP38 : Nat := nat_lit 3142356361263404603860962019993138528317888
@[expose] def ED38 : Nat := nat_lit 270467601
@[expose] def EP39 : Nat := nat_lit 5702113393752411386935254022774355733065856
@[expose] def ED39 : Nat := nat_lit 270205473
@[expose] def EP40 : Nat := nat_lit 7062570310678429119453722281392066160788864
@[expose] def ED40 : Nat := nat_lit 270205489
@[expose] def EP41 : Nat := nat_lit 4208805246307027285209291715808879253156096
@[expose] def ED41 : Nat := nat_lit 270205505
@[expose] def EP42 : Nat := nat_lit 7411039286393129539191156287321065220030784
@[expose] def ED42 : Nat := nat_lit 270467649
@[expose] def EP43 : Nat := nat_lit 6633307844974307677378545121492002820608384
@[expose] def ED43 : Nat := nat_lit 270205521
@[expose] def EP44 : Nat := nat_lit 3549916229812173913413924907068995042873856
@[expose] def ED44 : Nat := nat_lit 270467665
@[expose] def EP45 : Nat := nat_lit 4242747311904435447904638167802503606322048
@[expose] def ED45 : Nat := nat_lit 270205537
@[expose] def EP46 : Nat := nat_lit 5614415829542906162593246633930318227780672
@[expose] def ED46 : Nat := nat_lit 270467697
@[expose] def EP47 : Nat := nat_lit 4547208042943298093369528068130768358556800
@[expose] def ED47 : Nat := nat_lit 270467713
@[expose] def EP48 : Nat := nat_lit 713681372392940067851708647651411852845696
@[expose] def ED48 : Nat := nat_lit 270205585
@[expose] def EP49 : Nat := nat_lit 7764064986159768955541853107343600047419584
@[expose] def ED49 : Nat := nat_lit 270205601
@[expose] def EP50 : Nat := nat_lit 807337513897758153247020725044224870097920
@[expose] def ED50 : Nat := nat_lit 270205649
@[expose] def EP51 : Nat := nat_lit 2134448029061234895306012304502518599447744
@[expose] def ED51 : Nat := nat_lit 270205681
@[expose] def EP52 : Nat := nat_lit 3954340601399801285331559916266667837818176
@[expose] def ED52 : Nat := nat_lit 270205457
@[expose] def EP53 : Nat := nat_lit 2537248076194425347457904704668271047676480
@[expose] def ED53 : Nat := nat_lit 268436018
@[expose] def EP54 : Nat := nat_lit 8113950940919591093380229976226573908770880
@[expose] def ED54 : Nat := nat_lit 271909697
@[expose] def EP55 : Nat := nat_lit 8113950940919591093380229976226573908770880
@[expose] def ED55 : Nat := nat_lit 536871779
@[expose] def EP56 : Nat := nat_lit 5332147740887266327275533507968242948809472
@[expose] def ED56 : Nat := nat_lit 270467617
@[expose] def EP57 : Nat := nat_lit 6670479930418234954725461384671179644387712
@[expose] def ED57 : Nat := nat_lit 268436002
@[expose] def EP58 : Nat := nat_lit 2909015743679359564618725862584975292645440
@[expose] def ED58 : Nat := nat_lit 272171905
@[expose] def EP59 : Nat := nat_lit 2909015743679359564618725862584975292645440
@[expose] def ED59 : Nat := nat_lit 536871843
@[expose] def EP60 : Nat := nat_lit 8053739715587022563577986703763449048510528
@[expose] def ED60 : Nat := nat_lit 540476273
@[expose] def EP61 : Nat := nat_lit 2870372407021501899362032382757410186793024
@[expose] def ED61 : Nat := nat_lit 540738417
@[expose] def EP62 : Nat := nat_lit 4629119101539335913921249827185009964699712
@[expose] def ED62 : Nat := nat_lit 540476337
@[expose] def EP63 : Nat := nat_lit 1166259766718567603135225486313680135032896
@[expose] def ED63 : Nat := nat_lit 540738481
@[expose] def EP64 : Nat := nat_lit 8037994932463113002254696297798403285344320
@[expose] def ED64 : Nat := nat_lit 540476353
@[expose] def EP65 : Nat := nat_lit 4650412022100362168846929927806854800879680
@[expose] def ED65 : Nat := nat_lit 540476369
@[expose] def EP66 : Nat := nat_lit 1112480470511814144257444087162078066143296
@[expose] def ED66 : Nat := nat_lit 540738513
@[expose] def EP67 : Nat := nat_lit 3176047098328935859651545156842898247725120
@[expose] def ED67 : Nat := nat_lit 540476385
@[expose] def EP68 : Nat := nat_lit 8130204578618023889287826512582580809023552
@[expose] def ED68 : Nat := nat_lit 540476417
@[expose] def EP69 : Nat := nat_lit 2838473656815081327310078906978538510655552
@[expose] def ED69 : Nat := nat_lit 540738561
@[expose] def EP70 : Nat := nat_lit 3235515488056218139971166571207695502692416
@[expose] def ED70 : Nat := nat_lit 540476433
@[expose] def EP71 : Nat := nat_lit 7437407038389594134705662159729833788665920
@[expose] def ED71 : Nat := nat_lit 540738577
@[expose] def EP72 : Nat := nat_lit 5946959471678380165426877712167965172756544
@[expose] def ED72 : Nat := nat_lit 540476465
@[expose] def EP73 : Nat := nat_lit 785904873628688823889966654094888981811264
@[expose] def ED73 : Nat := nat_lit 540738609
@[expose] def EP74 : Nat := nat_lit 2892328677058039293213424478024551474995264
@[expose] def ED74 : Nat := nat_lit 540738625
@[expose] def EP75 : Nat := nat_lit 4623943355472156935925057655855347532120128
@[expose] def ED75 : Nat := nat_lit 540476497
@[expose] def EP76 : Nat := nat_lit 5962022264200780396479506420288474288808000
@[expose] def ED76 : Nat := nat_lit 540476513
@[expose] def EP77 : Nat := nat_lit 6740670814177540551876507785754587501723712
@[expose] def ED77 : Nat := nat_lit 540738673
@[expose] def EP78 : Nat := nat_lit 1160285881197369023332059852029207911424064
@[expose] def ED78 : Nat := nat_lit 540476545
@[expose] def EP79 : Nat := nat_lit 2875749339593734103430262632704132156776512
@[expose] def ED79 : Nat := nat_lit 540738497
@[expose] def EP80 : Nat := nat_lit 8130204578618023889287826512582580809023552
@[expose] def ED80 : Nat := nat_lit 536871938
@[expose] def EP81 : Nat := nat_lit 1101164813922831251127858545349093082013760
@[expose] def ED81 : Nat := nat_lit 542115057
@[expose] def EP82 : Nat := nat_lit 1101164813922831251127858545349093082013760
@[expose] def ED82 : Nat := nat_lit 805307667
@[expose] def EP83 : Nat := nat_lit 7400125999066886302086330819365804267614272
@[expose] def ED83 : Nat := nat_lit 540738529
@[expose] def EP84 : Nat := nat_lit 1161148492423560140931083227776361488736320
@[expose] def ED84 : Nat := nat_lit 536871986
@[expose] def EP85 : Nat := nat_lit 5995280963879390732049939528436188695502912
@[expose] def ED85 : Nat := nat_lit 542377265
@[expose] def EP86 : Nat := nat_lit 5995280963879390732049939528436188695502912
@[expose] def ED86 : Nat := nat_lit 805307731
@[expose] def EP87 : Nat := nat_lit 1841015732005848041037368218523672096608320
@[expose] def ED87 : Nat := nat_lit 540476401
@[expose] def EP88 : Nat := nat_lit 6005997153469977437354589491872042982101056
@[expose] def ED88 : Nat := nat_lit 536871890
@[expose] def EP89 : Nat := nat_lit 1078627399220487110396298376488993013637184
@[expose] def ED89 : Nat := nat_lit 542639473
@[expose] def EP90 : Nat := nat_lit 1078627399220487110396298376488993013637184
@[expose] def ED90 : Nat := nat_lit 805307795
@[expose] def EP91 : Nat := nat_lit 6044366902027317675068463870574878808875072
@[expose] def ED91 : Nat := nat_lit 810681633
@[expose] def EP92 : Nat := nat_lit 1802412103724157117244326435770733294264384
@[expose] def ED92 : Nat := nat_lit 810943777
@[expose] def EP93 : Nat := nat_lit 7422602019411977419535458446360030181597248
@[expose] def ED93 : Nat := nat_lit 811205921
@[expose] def EP94 : Nat := nat_lit 3219590010583066783654444986237118038941760
@[expose] def ED94 : Nat := nat_lit 810681697
@[expose] def EP95 : Nat := nat_lit 8091516231850798564368992455295717672493120
@[expose] def ED95 : Nat := nat_lit 810943841
@[expose] def EP96 : Nat := nat_lit 6033141343379321159932306166878506477166656
@[expose] def ED96 : Nat := nat_lit 810681761
@[expose] def EP97 : Nat := nat_lit 1824528052896126951842809810135580253102144
@[expose] def ED97 : Nat := nat_lit 810943905
@[expose] def EP98 : Nat := nat_lit 7405764912667409834358643401375227708186688
@[expose] def ED98 : Nat := nat_lit 811206049
@[expose] def EP99 : Nat := nat_lit 8086666962461695339926399714871905306288192
@[expose] def ED99 : Nat := nat_lit 810943921
@[expose] def EP100 : Nat := nat_lit 5690213849124370704291789878669084588515392
@[expose] def ED100 : Nat := nat_lit 810681809
@[expose] def EP101 : Nat := nat_lit 3518210114822640776853264881918269493092416
@[expose] def ED101 : Nat := nat_lit 810943953
@[expose] def EP102 : Nat := nat_lit 2462044237830568564874983213544780779495488
@[expose] def ED102 : Nat := nat_lit 811206097
@[expose] def EP103 : Nat := nat_lit 6670660497993825044161784277367578460430400
@[expose] def ED103 : Nat := nat_lit 810943969
@[expose] def EP104 : Nat := nat_lit 2837125778448501917069477411980445021118528
@[expose] def ED104 : Nat := nat_lit 811206113
@[expose] def EP105 : Nat := nat_lit 3180199524480036890504153385581634468454464
@[expose] def ED105 : Nat := nat_lit 810681857
@[expose] def EP106 : Nat := nat_lit 1166080319296973350562099511801453009182784
@[expose] def ED106 : Nat := nat_lit 811206193
@[expose] def EP107 : Nat := nat_lit 7443937435280809642963089483491742098923584
@[expose] def ED107 : Nat := nat_lit 810681969
@[expose] def EP108 : Nat := nat_lit 4302805732138988088774581064590454366150720
@[expose] def ED108 : Nat := nat_lit 811205985
@[expose] def EP109 : Nat := nat_lit 5946960926839386839566848896249413842772032
@[expose] def ED109 : Nat := nat_lit 805307746
@[expose] def EP110 : Nat := nat_lit 6991534725224998116206662402831246594678848
@[expose] def ED110 : Nat := nat_lit 812451521
@[expose] def EP111 : Nat := nat_lit 6991534725224998116206662402831246594678848
@[expose] def ED111 : Nat := nat_lit 1073743587
@[expose] def EP112 : Nat := nat_lit 3192112021882781768936506138859097070248000
@[expose] def ED112 : Nat := nat_lit 810681777
@[expose] def EP113 : Nat := nat_lit 1128217179666055933748240851205653976588352
@[expose] def ED113 : Nat := nat_lit 805307842
@[expose] def EP114 : Nat := nat_lit 4634745988215186600970074655426178313887808
@[expose] def ED114 : Nat := nat_lit 812713729
@[expose] def EP115 : Nat := nat_lit 4634745988215186600970074655426178313887808
@[expose] def ED115 : Nat := nat_lit 1073743651
@[expose] def EP116 : Nat := nat_lit 4214927895255129184395877014121676437200960
@[expose] def ED116 : Nat := nat_lit 811206065
@[expose] def EP117 : Nat := nat_lit 8091516231850798564368992455295717672493120
@[expose] def ED117 : Nat := nat_lit 805307890
@[expose] def EP118 : Nat := nat_lit 4231947333784424464164072001338233617915968
@[expose] def ED118 : Nat := nat_lit 812975937
@[expose] def EP119 : Nat := nat_lit 4231947333784424464164072001338233617915968
@[expose] def ED119 : Nat := nat_lit 1073743715
@[expose] def EP120 : Nat := nat_lit 2195351882151215789262548375566410396213312
@[expose] def ED120 : Nat := nat_lit 1081018097
@[expose] def EP121 : Nat := nat_lit 3899048574636354457837954510522921626902592
@[expose] def ED121 : Nat := nat_lit 1081280241
@[expose] def EP122 : Nat := nat_lit 6697715465441964424611592378383178994032704
@[expose] def ED122 : Nat := nat_lit 1081542385
@[expose] def EP123 : Nat := nat_lit 7742710667749278213906664446711910267363392
@[expose] def ED123 : Nat := nat_lit 1081018225
@[expose] def EP124 : Nat := nat_lit 1443252065739619368191831968798004428415040
@[expose] def ED124 : Nat := nat_lit 1081280369
@[expose] def EP125 : Nat := nat_lit 1455499738954556579229960115918895145820224
@[expose] def ED125 : Nat := nat_lit 1081542513
@[expose] def EP126 : Nat := nat_lit 6034503778462301127652711467889926379151424
@[expose] def ED126 : Nat := nat_lit 1081542529
@[expose] def EP127 : Nat := nat_lit 2461880562059658837279589783570295814889536
@[expose] def ED127 : Nat := nat_lit 1081542545
@[expose] def EP128 : Nat := nat_lit 2848355299035965285440568043911659603632192
@[expose] def ED128 : Nat := nat_lit 1081018273
@[expose] def EP129 : Nat := nat_lit 1454808456108592536036508426105050719068224
@[expose] def ED129 : Nat := nat_lit 1081018289
@[expose] def EP130 : Nat := nat_lit 3263144760395151395265766571519807752773696
@[expose] def ED130 : Nat := nat_lit 1081542577
@[expose] def EP131 : Nat := nat_lit 6698719134472464436561079324891777185095744
@[expose] def ED131 : Nat := nat_lit 1081018305
@[expose] def EP132 : Nat := nat_lit 4938700243365795342821135074476516434518080
@[expose] def ED132 : Nat := nat_lit 1081542593
@[expose] def EP133 : Nat := nat_lit 4237645733593947608827876172353658489151552
@[expose] def ED133 : Nat := nat_lit 1081018369
@[expose] def EP134 : Nat := nat_lit 1781650936385214055656140330602352478003264
@[expose] def ED134 : Nat := nat_lit 1081542657
@[expose] def EP135 : Nat := nat_lit 6676454460033816321036454516748900195115072
@[expose] def ED135 : Nat := nat_lit 1081018385
@[expose] def EP136 : Nat := nat_lit 5968566098660428251449513436441185801216064
@[expose] def ED136 : Nat := nat_lit 1081018161
@[expose] def EP137 : Nat := nat_lit 2462046858606121546400495221247255803338816
@[expose] def ED137 : Nat := nat_lit 1073743762
@[expose] def EP138 : Nat := nat_lit 3588711056041372614328433109048170078019648
@[expose] def ED138 : Nat := nat_lit 1082722433
@[expose] def EP139 : Nat := nat_lit 3588711056041372614328433109048170078019648
@[expose] def ED139 : Nat := nat_lit 1342179491
@[expose] def EP140 : Nat := nat_lit 3594071852977832689921359463921412305854528
@[expose] def ED140 : Nat := nat_lit 1081542449
@[expose] def EP141 : Nat := nat_lit 3594071852977832689921359463921412305854528
@[expose] def ED141 : Nat := nat_lit 1342179523
@[expose] def EP142 : Nat := nat_lit 5271236183995994744182228899327732112695360
@[expose] def ED142 : Nat := nat_lit 1081018241
@[expose] def EP143 : Nat := nat_lit 4634745988215186600970074655426178313887808
@[expose] def ED143 : Nat := nat_lit 1073743666
@[expose] def EP144 : Nat := nat_lit 3529773319641600097793363819877828561477696
@[expose] def ED144 : Nat := nat_lit 1083115745
@[expose] def EP145 : Nat := nat_lit 3529773319641600097793363819877828561477696
@[expose] def ED145 : Nat := nat_lit 1342179587
@[expose] def EP146 : Nat := nat_lit 5620203722757065141049616967601205763907648
@[expose] def ED146 : Nat := nat_lit 1351289009
@[expose] def EP147 : Nat := nat_lit 5609731962697303300765456849309967177228352
@[expose] def ED147 : Nat := nat_lit 1351289041
@[expose] def EP148 : Nat := nat_lit 5613752754711471223784319513772856206696512
@[expose] def ED148 : Nat := nat_lit 1351420113
@[expose] def EP149 : Nat := nat_lit 5674227393462431229552809885376978956853312
@[expose] def ED149 : Nat := nat_lit 1351682257
@[expose] def EP150 : Nat := nat_lit 5695485590035514946830408086953497054683200
@[expose] def ED150 : Nat := nat_lit 1351289105
@[expose] def EP151 : Nat := nat_lit 5603012548127621960707261939253875971989568
@[expose] def ED151 : Nat := nat_lit 1351420177
@[expose] def EP152 : Nat := nat_lit 5642080099697255992453518005122119588651072
@[expose] def ED152 : Nat := nat_lit 1351682321
@[expose] def EP153 : Nat := nat_lit 8043109843314380821612200033603292930777152
@[expose] def ED153 : Nat := nat_lit 1351420193
@[expose] def EP154 : Nat := nat_lit 8080272145542795209831392798687424510959680
@[expose] def ED154 : Nat := nat_lit 1351682337
@[expose] def EP155 : Nat := nat_lit 8085797726520556109655922764881873238499392
@[expose] def ED155 : Nat := nat_lit 1351682353
@[expose] def EP156 : Nat := nat_lit 8091074802548096907047236722676812516958272
@[expose] def ED156 : Nat := nat_lit 1351682369
@[expose] def EP157 : Nat := nat_lit 8124696213735364640555257769870843198578752
@[expose] def ED157 : Nat := nat_lit 1351420257
@[expose] def EP158 : Nat := nat_lit 5625145444880949449899739233178950363258944
@[expose] def ED158 : Nat := nat_lit 1351420081
@[expose] def EP159 : Nat := nat_lit 5642080099697255992453518005122119588651072
@[expose] def ED159 : Nat := nat_lit 1342179602
@[expose] def EP160 : Nat := nat_lit 3545676075923434411218138685137391738167360
@[expose] def ED160 : Nat := nat_lit 1352600033
@[expose] def EP161 : Nat := nat_lit 3545676075923434411218138685137391738167360
@[expose] def ED161 : Nat := nat_lit 1610615299
@[expose] def EP162 : Nat := nat_lit 5668435758164304766521922850796454326050880
@[expose] def ED162 : Nat := nat_lit 1621166609
#kc_select CFSG.KC.Schur.M24 EP EP 163
#kc_select CFSG.KC.Schur.M24 ED ED 163
@[expose] def BP : Nat := nat_lit 417753473088
@[expose] def OJ0 : Nat := nat_lit 3389215278611547699133847600801352312075978813457478336922086186721001619150175331461120356422550638991305284741528289280
@[expose] def OJ1 : Nat := nat_lit 1074940077419248885425802400291786702569909750010735349893903290488319493703810418766485549622906583949596335777253056
@[expose] def OJ2 : Nat := nat_lit 8302131984756535411737474914349688749935271004215392785521761806588242145146663393935007395184614935466277342656
@[expose] def OJ3 : Nat := nat_lit 47160262554655946373624778721673752232686271934228750668477163442918623334890365467627200704440965116466304
@[expose] def OJ4 : Nat := nat_lit 243230110222592198202037837479042713286817422125705225676495562080790287456375692344930383288451734464
@[expose] def OJ5 : Nat := nat_lit 65364890733909125863166731141594288172509508135300285547520224197358263770030784
@[expose] def OJ6 : Nat := nat_lit 2701404224

theorem gens : McL.Sub.gensOK MG (nat_lit 24) (nat_lit 2) = true := by quickRfl
theorem rels : McL.Sub.relsHold MG REL (nat_lit 24) (nat_lit 7) = true := by quickRfl
theorem rels_letters : McL.RangeX.entsBelow REL (nat_lit 7) (nat_lit 4) = true := by quickRfl
theorem ents : McL.Model.elemsOK MG EP ED (nat_lit 24) (nat_lit 2) BP (nat_lit 163) = true := by quickRfl
theorem ep_wrap : McL.RangeX.epWrap EP ED (nat_lit 163) (nat_lit 256) = true := by quickRfl
theorem orb0 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 0) (nat_lit 23) OJ0)) (nat_lit 24) = true := by quickRfl
theorem bp0 : Nat.blt (McL.Model.bpt BP (nat_lit 0)) (nat_lit 24) = true := by quickRfl
theorem orb1 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 1) (nat_lit 22) OJ1)) (nat_lit 23) = true := by quickRfl
theorem bp1 : Nat.blt (McL.Model.bpt BP (nat_lit 1)) (nat_lit 24) = true := by quickRfl
theorem orb2 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 2) (nat_lit 21) OJ2)) (nat_lit 22) = true := by quickRfl
theorem bp2 : Nat.blt (McL.Model.bpt BP (nat_lit 2)) (nat_lit 24) = true := by quickRfl
theorem orb3 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 3) (nat_lit 20) OJ3)) (nat_lit 21) = true := by quickRfl
theorem bp3 : Nat.blt (McL.Model.bpt BP (nat_lit 3)) (nat_lit 24) = true := by quickRfl
theorem orb4 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 4) (nat_lit 19) OJ4)) (nat_lit 20) = true := by quickRfl
theorem bp4 : Nat.blt (McL.Model.bpt BP (nat_lit 4)) (nat_lit 24) = true := by quickRfl
theorem orb5 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 5) (nat_lit 15) OJ5)) (nat_lit 16) = true := by quickRfl
theorem bp5 : Nat.blt (McL.Model.bpt BP (nat_lit 5)) (nat_lit 24) = true := by quickRfl
theorem orb6 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 6) (nat_lit 2) OJ6)) (nat_lit 3) = true := by quickRfl
theorem bp6 : Nat.blt (McL.Model.bpt BP (nat_lit 6)) (nat_lit 24) = true := by quickRfl

end CFSG.KC.Schur.M24

end
