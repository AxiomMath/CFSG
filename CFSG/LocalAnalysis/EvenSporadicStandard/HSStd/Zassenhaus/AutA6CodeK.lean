module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

open CFSG.Permutation.FinPack CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K

@[expose] def IsC (c : List ℕ) : Prop := ∃ σ : P10, code σ = c

theorem isC_code (σ : P10) : IsC (code σ) := ⟨σ, rfl⟩

theorem isC_cmul {a b : List ℕ} (ha : IsC a) (hb : IsC b) : IsC (Core.cmul a b) := by
  obtain ⟨σ, rfl⟩ := ha
  obtain ⟨τ, rfl⟩ := hb
  exact ⟨σ * τ, code_mul σ τ⟩

theorem isC_cid : IsC Core.cid := ⟨1, code_one⟩

theorem isC_of_psl {c : List ℕ} (h : c ∈ Core.pslLit) : IsC c := by
  obtain ⟨x, -, rfl⟩ := exists_psl29_of_code h
  exact ⟨x, rfl⟩

theorem isC_of_autL {c : List ℕ} (h : c ∈ Core.autL) : IsC c := by
  obtain ⟨x, rfl⟩ := Setup.X3Aut.exists_of_mem_autL h
  exact ⟨(x : P10), rfl⟩

theorem pk_cmul {a b : List ℕ} (ha : IsC a) (hb : IsC b) :
    pk (Core.cmul a b) = mulK 10 (pk a) (pk b) := by
  obtain ⟨σ, rfl⟩ := ha
  obtain ⟨τ, rfl⟩ := hb
  rw [← code_mul, pk_code, pk_code, pk_code, enc_mul (n := 10) (by norm_num)]

theorem pk_cid : pk Core.cid = idK := by rw [← code_one, pk_code, enc_one]

theorem pk_inj {a b : List ℕ} (ha : IsC a) (hb : IsC b) (h : pk a = pk b) : a = b := by
  obtain ⟨σ, rfl⟩ := ha
  obtain ⟨τ, rfl⟩ := hb
  rw [pk_code, pk_code] at h
  rw [enc_inj (by norm_num) h]

theorem beq_pk {a b : List ℕ} (ha : IsC a) (hb : IsC b) : (a == b) = Nat.beq (pk a) (pk b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨fun h => by rw [h], pk_inj ha hb⟩

@[expose] noncomputable def peqK (a b c d : ℕ) : Bool :=
  allLtK (fun i => Nat.beq (rd a (rd b i)) (rd c (rd d i))) 10

theorem peqK_iff (σ τ ρ π : P10) :
    peqK (enc σ) (enc τ) (enc ρ) (enc π) = true ↔ σ * τ = ρ * π := by
  rw [peqK, allLtK_iff]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have e := h i i.2
    rw [Nat.beq_eq, rd_enc (by norm_num) τ i, rd_enc (by norm_num) σ (τ i),
      rd_enc (by norm_num) π i, rd_enc (by norm_num) ρ (π i)] at e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact e
  · intro h i hi
    have e := congrArg (fun g : P10 => ((g ⟨i, hi⟩ : Fin 10) : ℕ)) h
    simp only [Equiv.Perm.mul_apply] at e
    have h1 : rd (enc τ) i = τ ⟨i, hi⟩ := rd_enc (by norm_num) τ ⟨i, hi⟩
    have h2 : rd (enc π) i = π ⟨i, hi⟩ := rd_enc (by norm_num) π ⟨i, hi⟩
    rw [Nat.beq_eq, h1, h2, rd_enc (by norm_num) σ, rd_enc (by norm_num) ρ]
    exact e

theorem peq_pk {a b c d : List ℕ} (ha : IsC a) (hb : IsC b) (hc : IsC c) (hd : IsC d) :
    (Core.cmul a b == Core.cmul c d) = peqK (pk a) (pk b) (pk c) (pk d) := by
  obtain ⟨σ, rfl⟩ := ha
  obtain ⟨τ, rfl⟩ := hb
  obtain ⟨ρ, rfl⟩ := hc
  obtain ⟨π, rfl⟩ := hd
  rw [← code_mul, ← code_mul, pk_code, pk_code, pk_code, pk_code, beqC, Bool.eq_iff_iff,
    decide_eq_true_iff, peqK_iff]

theorem comm_pk {a b : List ℕ} (ha : IsC a) (hb : IsC b) :
    (Core.cmul a b == Core.cmul b a) = commLaneK 10 (pk a) (pk b) := by
  obtain ⟨σ, rfl⟩ := ha
  obtain ⟨τ, rfl⟩ := hb
  rw [pk_code, pk_code, comm_eqP]

theorem sq_pk {a : List ℕ} (ha : IsC a) :
    (Core.cmul a a == Core.cid) = Nat.beq (mulK 10 (pk a) (pk a)) idK := by
  rw [beq_pk (isC_cmul ha ha) isC_cid, pk_cmul ha ha, pk_cid]

theorem invT_pk {a : List ℕ} (ha : IsC a) :
    (Core.cmul a a == Core.cid && a != Core.cid) = invTK (pk a) := by
  rw [bne, sq_pk ha, beq_pk ha isC_cid, pk_cid]
  rfl

theorem mem_pk {L : List (List ℕ)} (hL : ∀ c ∈ L, IsC c) {a : List ℕ} (ha : IsC a) :
    a ∈ L ↔ pk a ∈ L.map pk := by
  rw [List.mem_map]
  exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨c, hc, e⟩ => pk_inj (hL c hc) ha e ▸ hc⟩

theorem contains_pk {L : List (List ℕ)} (hL : ∀ c ∈ L, IsC c) {a : List ℕ} (ha : IsC a) :
    L.contains a = memK (pk a) (L.map pk) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, memK_iff]
  exact mem_pk hL ha

theorem all_pk {L : List (List ℕ)} {p : List ℕ → Bool} {q : ℕ → Bool}
    (h : ∀ c ∈ L, p c = q (pk c)) : L.all p = allK q (L.map pk) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, allK_iff]
  constructor
  · intro H e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    rw [← h c hc]
    exact H c hc
  · intro H c hc
    rw [h c hc]
    exact H _ (List.mem_map_of_mem hc)

theorem any_pk {L : List (List ℕ)} {p : List ℕ → Bool} {q : ℕ → Bool}
    (h : ∀ c ∈ L, p c = q (pk c)) : L.any p = anyK q (L.map pk) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, anyK_iff]
  constructor
  · rintro ⟨c, hc, e⟩
    exact ⟨pk c, List.mem_map_of_mem hc, by rw [← h c hc, e]⟩
  · rintro ⟨_, he, e⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    exact ⟨c, hc, by rw [h c hc, e]⟩

theorem map_filter_pk {L : List (List ℕ)} {p : List ℕ → Bool} {q : ℕ → Bool}
    (h : ∀ c ∈ L, p c = q (pk c)) : (L.filter p).map pk = (L.map pk).filter q := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun c hc => by rw [h c hc]; rfl

theorem all_filter (L : List (List ℕ)) (p f : List ℕ → Bool) :
    (L.filter p).all f = L.all fun a => !p a || f a := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filter_cons]
    cases h : p a <;> simp [ih, h]

theorem allK_sub {K IV : List ℕ} {g : ℕ → Bool} (hIV : K.filter g = IV) (f : ℕ → Bool) :
    allK f IV = allK (fun a => !g a || f a) K := by
  rw [Bool.eq_iff_iff, allK_iff, allK_iff, ← hIV]
  constructor
  · intro H a ha
    cases hg : g a
    · rfl
    · rw [Bool.not_true, Bool.false_or]
      exact H a (List.mem_filter.2 ⟨ha, hg⟩)
  · intro H a ha
    obtain ⟨ha, hg⟩ := List.mem_filter.1 ha
    have h := H a ha
    rw [hg, Bool.not_true, Bool.false_or] at h
    exact h

@[expose] noncomputable def cinK (c d : ℕ) (S : List ℕ) : Bool := anyK (fun e => peqK c d e c) S

theorem conj_mem_iff {S : List (List ℕ)} (hS : ∀ c ∈ S, IsC c) (σ τ : P10) :
    Core.cmul (Core.cmul (code σ) (code τ)) (code σ⁻¹) ∈ S ↔
      cinK (enc σ) (enc τ) (S.map pk) = true := by
  rw [← code_mul, ← code_mul, cinK, anyK_iff]
  constructor
  · intro h
    refine ⟨enc (σ * τ * σ⁻¹), ?_, ?_⟩
    · rw [← pk_code]
      exact List.mem_map_of_mem h
    · rw [peqK_iff, inv_mul_cancel_right]
  · rintro ⟨e, he, h⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    obtain ⟨ρ, rfl⟩ := hS c hc
    rw [pk_code, peqK_iff] at h
    rw [h, mul_inv_cancel_right]
    exact hc

@[expose] def pgltK : List ℕ :=
  [632015968320, 635791947345, 623716222320, 13222970745, 640319768370, 628246991745, 86520587145,
   648627622470, 644599739520, 6026318985, 32565900930, 9485514825, 619943375970, 158965724265,
   653158391895, 649127560545, 79326885225, 105547908960, 69851055705, 637299685395, 633281200470,
   443254579545, 652903539570, 628746192720, 26442155865, 36849521235, 35007067185, 6279496530,
   167916102480, 19733487990, 644854776120, 139692426105, 165692004465, 143151621945, 641830454820,
   637809021495, 516555145785, 620442576945, 98887292985, 96996958260, 94616388930, 79580193840,
   92715287175, 619688892195, 223361730345, 641585000520, 653657592870, 427440477225, 436227831840,
   414221292105, 624973346370, 172184909385, 640074129795, 24010842945, 22323431190, 27958792515,
   242222571840, 40874686305, 22069778820, 17508554850, 142899492960, 178027320960, 31702140195,
   13981282950, 430429246080, 633526839045, 576920686665, 169978757445, 139187549505, 152862724200,
   624216713220, 296662296585, 645353977095, 499885614345, 496375268865, 487518908505,
   631770514020, 84154938450, 82687911975, 100403851860, 302587052625, 109071845490, 81680345445,
   90808268400, 9991439985, 105001669380, 87278846055, 503728775265, 627992692245, 207538778505,
   217281807750, 233124669465, 649884746520, 573183230745, 620697429270, 446713775385,
   423398551575, 421050537075, 426682951440, 431953609560, 636301283445, 157136946480,
   645608276595, 229378364025, 40118720550, 18010499415, 233883374880, 246985146960, 26164367925,
   108825572160, 35586790935, 31564398900, 298368536880, 39870096690, 163347503415, 171906928980,
   40626430995, 238679512080, 36008180085, 452084334960, 357027837465, 569357068050, 559964045625,
   155987441160, 173701414965, 375886581810, 154977962355, 150417590145, 69598795650, 165366150165,
   159723905400, 564093256050, 279983915625, 277429244775, 306422285865, 624473408295,
   507079316265, 483542647080, 481415017860, 499128010785, 504935617590, 649384255620,
   289743904905, 108319221255, 91307931960, 307180937985, 315185647665, 99461992515, 177022731345,
   95982729000, 104042881605, 358730928705, 30439319880, 109578749220, 311661311265, 96373721475,
   521036653185, 353281532025, 242956240500, 206780859510, 213008212005, 629001229320,
   580379882505, 556524655110, 419111798595, 418500584760, 447219307335, 491800298310,
   451576624515, 416735050020, 435999097095, 443507363880, 568908132390, 653912076645,
   363044471145, 10340504340, 23508107880, 500450891280, 214839879960, 227675313735, 14262166680,
   371566324080, 85955351160, 10841494935, 515954140560, 27668068500, 306609002640, 287787472530,
   284833560960, 13510414695, 152354448660, 156385685895, 507930579330, 160004735895, 169671154020,
   311200782690, 5175088680, 210530105430, 19479819045, 379154699040, 442402771845, 350411043960,
   378867422985, 554714547045, 572425573890, 565079713095, 177271539480, 151673473350,
   379625997330, 384137965890, 168461420550, 164441976915, 225067962450, 103736936790,
   177779249925, 371808748290, 589237153890, 303100336005, 279225918855, 285990220035,
   492093597780, 506826663000, 551409620055, 519777125220, 490032482565, 495608418840,
   516808061190, 70702896165, 83907203190, 572895827745, 275205421350, 288037705560, 86707303830,
   237903350145, 159252975750, 70452061080, 575564706705, 100965500565, 379906434705, 361088038800,
   344444127585, 581231153760, 78475663110, 283829634615, 91958510595, 233412137985, 515703346275,
   376082344035, 237407142405, 229884129300, 310706855955, 412705441875, 216100509540,
   223614674565, 349009544835, 552241034805, 580127360310, 451328553480, 431428241685,
   520284028950, 447568187505, 245217908550, 422131996725, 434219524980, 280549167990,
   452333143095, 423058700625, 589485777750, 5425866645, 572144034960, 485440701075, 495098272080,
   212752213095, 236915267160, 560241874515, 225318162840, 241962076455, 504725858595,
   563065865760, 373821760545, 349658706480, 568395704625, 490591244640, 301343277840,
   313673347605, 314170226775, 305857074450, 309393958710, 138336999060, 499698897810,
   482669267250, 138838054935, 502666770450, 277180014930, 555966884160, 352242336150,
   448069202580, 374870259990, 352523481960, 346134315540, 588729443445, 550398023955,
   576415416855, 144003470595, 427153266690, 348502853895, 361338279990, 143752627350,
   442653574290, 173410637715, 234163865490, 228176906385, 211535944050, 344194115400,
   576065738100, 289491484965, 370316177700, 486003004980, 275709831285, 296915371875,
   588481188135, 482531092035, 494615463045, 352994104455, 520530302280, 78726432915, 426401465745,
   558738133140, 285230695800, 414499313460, 298618729110, 301572643080, 564336425220,
   430188287745, 240944182530, 216784076865, 434732730690, 550987182705, 382628823075,
   382370727480, 369789896775, 206499766935, 507679768725, 362792182275, 246727051365,
   315682526835, 245476188420, 558448064325, 418112553090, 486944249925, 412995563925,
   580980334995, 207251543400, 567094154595, 356522727540, 383879686020, 279797199000,
   345629791110, 555009574740, 358229295255]

@[expose] def m10tK : List ℕ :=
  [624468064320, 628998833745, 644850353520, 10337994105, 620695217970, 648626332545, 70703534985,
   633531814470, 627994350720, 13507130505, 5426992770, 26157996105, 653154153570, 144004101225,
   637307793495, 619690734945, 85952267625, 78727690080, 99455612505, 619939506195, 652905750870,
   414505451865, 624221504370, 631765354320, 5173839705, 27674624595, 40122868785, 19731538770,
   177275503440, 14265450870, 641835614520, 159249884025, 138335045745, 171900749625, 623715485220,
   644602135095, 486950588985, 636293175345, 78474405945, 100972187700, 108320027970, 92713546800,
   86710510215, 641577813795, 233408829225, 649132904520, 620446815270, 442402100265, 426398783520,
   447566254665, 640069154370, 138839946825, 645357662595, 10843943745, 39868114710, 32571400515,
   246734541120, 22072018785, 31697549700, 40621914210, 169971308640, 154981054080, 40877036835,
   24011608710, 452334940800, 628243306245, 560248205385, 173417247045, 152857642305, 160008073320,
   633274198020, 305853966345, 624974636295, 515702666505, 499696346625, 507931795545,
   649885483620, 70451299410, 108820432935, 105553199700, 315686859345, 81681340530, 104994982245,
   109577389680, 36845205105, 109077537540, 84159045735, 520535441505, 637804967445, 225066688905,
   206496691590, 227673405465, 628750615320, 576068207385, 649379464470, 427156317465,
   448071811095, 451326018675, 431949711120, 442654860120, 653661462645, 143751996720,
   635796001395, 207254618745, 18011748390, 35001669975, 242957632800, 237910889040, 35590861365,
   103743316800, 9487816215, 26448597300, 285235183920, 30443603250, 155984103735, 168468439380,
   36013822995, 234167542800, 17507428725, 434740928880, 379151582745, 572141405970, 581232361785,
   177020933640, 165700636725, 383887360050, 165360523635, 177774548865, 96989300610, 178029855765,
   157140844920, 589487759730, 298367255145, 279794254695, 288038946345, 653910233895,
   500453933865, 507679166760, 520278336900, 504931510305, 515955557430, 640326770820,
   280552235145, 91311277575, 94612236600, 303105069825, 311210418225, 95989956675, 163352638545,
   69850208040, 98893533765, 345631121985, 22321129800, 96378303780, 306612602145, 90805045635,
   495105409665, 358732796025, 228179121780, 213003687030, 225319682085, 645606618120,
   572899070985, 580979864070, 412989609795, 452080371000, 436232913735, 521035846470,
   416738854275, 435990591780, 451581325575, 419119247400, 588733960230, 632023155045,
   352997372265, 23507403540, 13226185320, 494613845520, 237399726360, 240942851655, 6278161560,
   349006477680, 91960128120, 13978068375, 499130701200, 9989200020, 296914139280, 307177199250,
   302579521920, 19481645415, 139690743060, 158968746375, 482536075650, 139189293975, 150415612260,
   275708860770, 31559206440, 245468514390, 6027776805, 369795298080, 430191940485, 352239314040,
   361339512585, 588478837605, 565078947330, 575562913095, 151675758360, 167909853510,
   376086869010, 371574899010, 143150782470, 172191158355, 212756492370, 82686671190, 169677832965,
   379910165250, 568404938850, 287786477445, 285985486215, 298620379395, 485434669140,
   496377009240, 589233005655, 490038383460, 495601158405, 519778484760, 492101255430, 83903341605,
   86523809910, 567092328225, 310697343270, 301338789720, 79578727830, 216098294145, 152359223430,
   87275500440, 572428133265, 69599766165, 356524705425, 379622336400, 375876954465, 555014767200,
   104037897990, 313669015095, 79328351235, 236917720065, 502670632035, 361087174755, 245223416325,
   217287516180, 314178891795, 423389919315, 246979823460, 238676936325, 384132458115,
   558732232245, 569359017270, 431435633160, 421045680405, 504735346710, 422140137585,
   214841788230, 414215084085, 446715499380, 277177770870, 423064048695, 430422100305,
   555973083990, 27952166805, 580128040080, 516806435475, 491793967440, 207535772775, 223362586200,
   550983112275, 206783865240, 210529249575, 481411221795, 573180057120, 378870469665,
   363043656240, 551404534065, 516556034400, 306425533200, 301579928085, 275206269015,
   309396202770, 296663160630, 173694736020, 506827473810, 503719532850, 164433836055,
   499882432530, 289743081810, 564085074240, 362792628630, 412711465620, 344192223510,
   346132923240, 358227735060, 550402864245, 568898775315, 552245350935, 156382033155,
   434214750210, 370307909895, 373817481270, 159720637590, 426685564050, 142900332435,
   223613573010, 233879767185, 242213980530, 382621333320, 563066570100, 277431611685,
   382376050980, 483537356340, 315176982645, 311658944355, 564344668455, 487512708675,
   507077891205, 349656253575, 482673370440, 100397303955, 447216907665, 576417001620,
   279980709240, 418105534260, 279229002390, 283826682120, 554708654340, 427437496065,
   233127908610, 229380689985, 418496350530, 576918426225, 374879641635, 348505798200,
   357025552455, 229881496215, 486008897685, 350413619715, 211537045605, 284836759155,
   241970606340, 556519155525, 443255459970, 490584016965, 443505869205, 558454034835,
   216778675560, 580378465635, 371803039860, 344446080900, 289492062360, 353278333830,
   559957645140, 352526434455]

@[expose] def ivPGLK : List ℕ :=
  [22658101545, 637055557920, 19098244665, 35726304105, 640831353345, 623311665030, 632524603410,
   32267133465, 172928493825, 627087460455, 92132368530, 650789389395, 618780710520, 142640183685,
   139386567000, 654565184820, 103169537175, 95700865680, 82247190420, 646258434885, 444682286400,
   160650447120, 215122024560, 353925085185, 425354101335, 413278565400, 310078174800,
   301056209010, 358387713120, 448711164195, 238376227110, 590392542465, 487819977600,
   517915889730, 589037836080, 590143881795, 378235208310, 509358638355, 500649439845,
   360887886615, 285350647830, 589793605140, 241122580245, 212422660740, 276328682040, 13222970745,
   6026318985, 9485514825, 26442155865, 496375268865, 163347503415, 375886581810, 154977962355,
   483542647080, 504935617590, 307180937985, 227675313735, 169671154020, 151673473350,
   225067962450, 589237153890, 279225918855, 492093597780, 86707303830, 70452061080, 100965500565,
   233412137985, 349009544835, 422131996725, 434219524980, 589485777750, 588729443445,
   344194115400, 289491484965, 370316177700, 296915371875, 588481188135, 78726432915, 430188287745,
   418112553090, 207251543400]

@[expose] def ivM10K : List ℕ :=
  [22658101545, 637055557920, 19098244665, 35726304105, 640831353345, 623311665030, 632524603410,
   32267133465, 172928493825, 627087460455, 92132368530, 650789389395, 618780710520, 142640183685,
   139386567000, 654565184820, 103169537175, 95700865680, 82247190420, 646258434885, 444682286400,
   160650447120, 215122024560, 353925085185, 425354101335, 413278565400, 310078174800,
   301056209010, 358387713120, 448711164195, 238376227110, 590392542465, 487819977600,
   517915889730, 589037836080, 590143881795, 378235208310, 509358638355, 500649439845,
   360887886615, 285350647830, 589793605140, 241122580245, 212422660740, 276328682040]

@[expose] def ivPslK : List ℕ :=
  [22658101545, 637055557920, 19098244665, 35726304105, 640831353345, 623311665030, 632524603410,
   32267133465, 172928493825, 627087460455, 92132368530, 650789389395, 618780710520, 142640183685,
   139386567000, 654565184820, 103169537175, 95700865680, 82247190420, 646258434885, 444682286400,
   160650447120, 215122024560, 353925085185, 425354101335, 413278565400, 310078174800,
   301056209010, 358387713120, 448711164195, 238376227110, 590392542465, 487819977600,
   517915889730, 589037836080, 590143881795, 378235208310, 509358638355, 500649439845,
   360887886615, 285350647830, 589793605140, 241122580245, 212422660740, 276328682040]

@[expose] def dK : List ℕ :=
  [654820258320, 434873340435, 32267133465, 448711164195, 22658101545, 224840319510, 238376227110,
   637055557920]

@[expose] def VaK : List ℕ :=
  [654820258320, 637055557920, 32267133465, 22658101545]

@[expose] def VbK : List ℕ :=
  [654820258320, 448711164195, 238376227110, 32267133465]

@[expose] def KaK : List ℕ :=
  [654820258320, 642135823200, 22658101545, 637055557920, 19098244665, 35726304105, 649639306800,
   32267133465, 172928493825, 92132368530, 161219872305, 88155175170, 104426083890, 229533821190,
   431666700435, 168951296145, 100014752610, 156506624865, 224840319510, 443766020355,
   434873340435, 241633136790, 448711164195, 238376227110]

@[expose] def KbK : List ℕ :=
  [654820258320, 22658101545, 637055557920, 623311665030, 32267133465, 650789389395, 430840100985,
   421231069065, 4988364915, 9017242710, 211098797385, 242399405145, 641076365430, 444682286400,
   627342533955, 36290336070, 228859209600, 215122024560, 18624911235, 417207915600, 224840319510,
   434873340435, 448711164195, 238376227110]

@[expose] def KaL : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 6, 3, 1, 7, 4, 2, 8, 5, 9], [9, 2, 1, 3, 7, 8, 6, 4, 5, 0],
   [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], [9, 3, 6, 1, 8, 5, 2, 7, 4, 0], [9, 6, 3, 2, 4, 7, 1, 5, 8, 0],
   [0, 3, 6, 2, 5, 8, 1, 4, 7, 9], [9, 1, 2, 6, 5, 4, 3, 8, 7, 0], [1, 0, 9, 6, 7, 5, 3, 4, 8, 2],
   [2, 9, 0, 6, 4, 8, 3, 7, 5, 1], [1, 3, 6, 0, 4, 7, 9, 8, 5, 2], [2, 0, 9, 3, 5, 7, 6, 8, 4, 1],
   [2, 3, 6, 9, 7, 4, 0, 5, 8, 1], [6, 0, 9, 2, 8, 4, 1, 7, 5, 3], [3, 9, 0, 2, 7, 5, 1, 8, 4, 6],
   [1, 9, 0, 3, 8, 4, 6, 5, 7, 2], [2, 6, 3, 0, 8, 5, 9, 4, 7, 1], [1, 6, 3, 9, 5, 8, 0, 7, 4, 2],
   [6, 1, 2, 0, 7, 8, 9, 5, 4, 3], [3, 0, 9, 1, 4, 8, 2, 5, 7, 6], [3, 1, 2, 9, 8, 7, 0, 4, 5, 6],
   [6, 9, 0, 1, 5, 7, 2, 4, 8, 3], [3, 2, 1, 0, 5, 4, 9, 7, 8, 6], [6, 2, 1, 9, 4, 5, 0, 8, 7, 3]]

@[expose] def KbL : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [9, 2, 1, 3, 7, 8, 6, 4, 5, 0], [0, 2, 1, 6, 8, 7, 3, 5, 4, 9],
   [6, 8, 7, 3, 5, 4, 0, 2, 1, 9], [9, 1, 2, 6, 5, 4, 3, 8, 7, 0], [3, 5, 4, 0, 2, 1, 6, 8, 7, 9],
   [9, 7, 8, 3, 2, 1, 0, 5, 4, 6], [9, 8, 7, 0, 4, 5, 3, 1, 2, 6], [3, 7, 8, 6, 4, 5, 9, 2, 1, 0],
   [6, 5, 4, 3, 8, 7, 9, 1, 2, 0], [9, 4, 5, 0, 8, 7, 6, 2, 1, 3], [9, 5, 4, 6, 1, 2, 0, 7, 8, 3],
   [6, 7, 8, 0, 1, 2, 3, 4, 5, 9], [0, 4, 5, 3, 1, 2, 9, 8, 7, 6], [3, 4, 5, 6, 7, 8, 0, 1, 2, 9],
   [6, 4, 5, 9, 2, 1, 3, 7, 8, 0], [0, 8, 7, 6, 2, 1, 9, 4, 5, 3], [0, 7, 8, 9, 5, 4, 6, 1, 2, 3],
   [3, 8, 7, 9, 1, 2, 6, 5, 4, 0], [0, 5, 4, 9, 7, 8, 3, 2, 1, 6], [6, 1, 2, 0, 7, 8, 9, 5, 4, 3],
   [3, 1, 2, 9, 8, 7, 0, 4, 5, 6], [3, 2, 1, 0, 5, 4, 9, 7, 8, 6], [6, 2, 1, 9, 4, 5, 0, 8, 7, 3]]

theorem pk_tMul : pk (code A6Models.tMul) = 632015968320 := by decide +kernel

theorem pk_tMulFrob : pk (code A6Models.tMulFrob) = 624468064320 := by decide +kernel

theorem codeK_tMul : code A6Models.tMul = [0, 4, 8, 5, 6, 1, 7, 2, 3, 9] := by decide +kernel

theorem codeK_tMulFrob : code A6Models.tMulFrob = [0, 4, 8, 7, 2, 3, 5, 6, 1, 9] := by
  decide +kernel

theorem pgltK_check : (pslK.map (fun y => mulK 10 y 632015968320) == pgltK) = true := by
  decide +kernel

theorem m10tK_check : (pslK.map (fun y => mulK 10 y 624468064320) == m10tK) = true := by
  decide +kernel

theorem coset_pin {t : List ℕ} {tK : ℕ} {T : List ℕ} (ht : IsC t) (htK : pk t = tK)
    (hT : (pslK.map (fun y => mulK 10 y tK) == T) = true) :
    (Core.pslLit.map (fun c => Core.cmul c t)).map pk = T := by
  rw [← beq_iff_eq.1 hT, ← beq_iff_eq.1 pslK_pin, List.map_map, List.map_map]
  refine List.map_congr_left fun c hc => ?_
  simp only [Function.comp_apply]
  rw [pk_cmul (isC_of_psl hc) ht, htK]

theorem pglt_pin : (Core.pslLit.map (fun c => Core.cmul c [0, 4, 8, 5, 6, 1, 7, 2, 3, 9])).map pk =
    pgltK := by
  rw [← codeK_tMul]
  exact coset_pin (isC_code _) pk_tMul pgltK_check

theorem m10t_pin : (Core.pslLit.map (fun c => Core.cmul c [0, 4, 8, 7, 2, 3, 5, 6, 1, 9])).map pk =
    m10tK := by
  rw [← codeK_tMulFrob]
  exact coset_pin (isC_code _) pk_tMulFrob m10tK_check

theorem ivPGLK_pin : ((pslK ++ pgltK).filter invTK == ivPGLK) = true := by decide +kernel

theorem ivM10K_pin : ((pslK ++ m10tK).filter invTK == ivM10K) = true := by decide +kernel

theorem ivPslK_pin : (pslK.filter invTK == ivPslK) = true := by decide +kernel

theorem invK_pin : (autK.filter invTK == AutA6K.invK) = true := by decide +kernel

theorem dK_pin : (Core.dLit.map pk == dK) = true := by decide +kernel

theorem isC_of_dLit {c : List ℕ} (h : c ∈ Core.dLit) : IsC c := by
  have hs : Core.dLit.all (fun d => Core.pslLit.contains d) = true := by decide +kernel
  exact isC_of_psl (List.contains_iff_mem.1 (List.all_eq_true.1 hs c h))

theorem normL_pin (inv : List ℕ → List ℕ) (hinv : ∀ σ : P10, inv (code σ) = code σ⁻¹)
    {V : List (List ℕ)} (hV : ∀ c ∈ V, IsC c) :
    (Core.pslLit.filter fun k => V.all fun v => V.contains (Core.cmul (Core.cmul k v) (inv k))).map
        pk = pslK.filter (fun k => allK (fun v => cinK k v (V.map pk)) (V.map pk)) := by
  refine (map_filter_pk (q := fun k => allK (fun v => cinK k v (V.map pk)) (V.map pk))
    fun k hk => ?_).trans ?_
  · obtain ⟨κ, rfl⟩ := isC_of_psl hk
    refine all_pk fun v hv => ?_
    obtain ⟨ν, rfl⟩ := hV v hv
    beta_reduce
    rw [hinv, Bool.eq_iff_iff, List.contains_iff_mem, conj_mem_iff hV, pk_code, pk_code]
  · rw [beq_iff_eq.1 pslK_pin]

theorem eq_of_map_pk {A B : List (List ℕ)} (hA : ∀ c ∈ A, IsC c) (hB : ∀ c ∈ B, IsC c)
    (h : A.map pk = B.map pk) : A = B := by
  induction A generalizing B with
  | nil =>
    rw [List.map_nil, eq_comm, List.map_eq_nil_iff] at h
    rw [h]
  | cons a A ih =>
    cases B with
    | nil => exact absurd h (by simp)
    | cons b B =>
      rw [List.map_cons, List.map_cons, List.cons.injEq] at h
      rw [pk_inj (hA a List.mem_cons_self) (hB b List.mem_cons_self) h.1,
        ih (fun c hc => hA c (List.mem_cons_of_mem _ hc))
          (fun c hc => hB c (List.mem_cons_of_mem _ hc)) h.2]

theorem isC_KaL : ∀ c ∈ KaL, IsC c := by
  have hs : KaL.all (fun d => Core.pslLit.contains d) = true := by decide +kernel
  exact fun c h => isC_of_psl (List.contains_iff_mem.1 (List.all_eq_true.1 hs c h))

theorem isC_KbL : ∀ c ∈ KbL, IsC c := by
  have hs : KbL.all (fun d => Core.pslLit.contains d) = true := by decide +kernel
  exact fun c h => isC_of_psl (List.contains_iff_mem.1 (List.all_eq_true.1 hs c h))

theorem KaL_pin : KaL.map pk = KaK := beq_iff_eq.1 (by decide +kernel)

theorem KbL_pin : KbL.map pk = KbK := beq_iff_eq.1 (by decide +kernel)

theorem KaK_check :(pslK.filter (fun k => allK (fun v => cinK k v VaK) VaK) == KaK) = true := by
  decide +kernel

theorem KbK_check : (pslK.filter (fun k => allK (fun v => cinK k v VbK) VbK) == KbK) = true := by
  decide +kernel

@[expose] noncomputable def autNK (KK : List ℕ) : Bool :=
  allK (fun b => !allK (fun d => commLaneK 10 b d) dK || memK b pslK ||
    allK (fun c => !commLaneK 10 c b || !allK (fun d => cinK c d dK) dK ||
      allK (fun k => cinK c k KK) KK) autK) autK

theorem autN_KaK : autNK KaK = true := by decide +kernel

theorem autN_KbK : autNK KbK = true := by decide +kernel

theorem aut_norm (inv : List ℕ → List ℕ) (hinv : ∀ σ : P10, inv (code σ) = code σ⁻¹)
    {K : List (List ℕ)} (hK : ∀ c ∈ K, IsC c) (h : autNK (K.map pk) = true) :
    ∀ b ∈ Core.autL, b ∉ Core.pslLit → (∀ d ∈ Core.dLit, Core.cmul b d = Core.cmul d b) →
    ∀ c ∈ Core.autL, (∀ d ∈ Core.dLit, Core.cmul (Core.cmul c d) (inv c) ∈ Core.dLit) →
    Core.cmul c b = Core.cmul b c → ∀ k ∈ K, Core.cmul (Core.cmul c k) (inv c) ∈ K := by
  intro b hb hbp hbd c hc hcd hcb k hk
  have hdK := beq_iff_eq.1 dK_pin
  obtain ⟨β, rfl⟩ := isC_of_autL hb
  obtain ⟨γ, rfl⟩ := isC_of_autL hc
  obtain ⟨κ, rfl⟩ := hK k hk
  rw [hinv] at hcd ⊢
  have h1 := allK_iff.1 h (enc β) (by rw [← autK_pin, ← pk_code]; exact List.mem_map_of_mem hb)
  have e1 : allK (fun d => commLaneK 10 (enc β) d) dK = true := by
    rw [← hdK, allK_iff]
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
    obtain ⟨δ, rfl⟩ := isC_of_dLit hd
    rw [pk_code, ← comm_eqP, beq_iff_eq]
    exact hbd _ hd
  have e2 : memK (enc β) pslK = false := by
    rw [← beq_iff_eq.1 pslK_pin, ← pk_code, ← contains_pk (fun c hc => isC_of_psl hc) (isC_code β),
      Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
    exact hbp
  simp only [e1, e2, Bool.not_true, Bool.false_or] at h1
  have h2 := allK_iff.1 h1 (enc γ) (by rw [← autK_pin, ← pk_code]; exact List.mem_map_of_mem hc)
  have e3 : commLaneK 10 (enc γ) (enc β) = true := by
    rw [← comm_eqP, beq_iff_eq]
    exact hcb
  have e4 : allK (fun d => cinK (enc γ) d dK) dK = true := by
    rw [← hdK, allK_iff]
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
    obtain ⟨δ, rfl⟩ := isC_of_dLit hd
    rw [pk_code, ← conj_mem_iff (fun c hc => isC_of_dLit hc)]
    exact hcd _ hd
  simp only [e3, e4, Bool.not_true, Bool.false_or] at h2
  have h3 := allK_iff.1 h2 (enc κ) (by rw [← pk_code]; exact List.mem_map_of_mem hk)
  exact (conj_mem_iff hK γ κ).2 h3

@[expose] noncomputable def normEK (a b ab g : ℕ) : Bool :=
  (peqK g a a g || (peqK g a b g || peqK g a ab g)) &&
    (peqK g b a g || (peqK g b b g || peqK g b ab g))

@[expose] noncomputable def vtK (K : List ℕ) (a b ab t : ℕ) : Bool :=
  anyK (fun g => commLaneK 10 g t && !normEK a b ab g) K

@[expose] noncomputable def violK (K : List ℕ) (a b ab : ℕ) : Bool :=
  vtK K a b ab a || (vtK K a b ab b || vtK K a b ab ab)

@[expose] noncomputable def noTIK (K IV : List ℕ) : Bool :=
  allK (fun a => allK (fun b => Nat.beq a b || !commLaneK 10 a b || violK K a b (mulK 10 a b))
    IV) IV

theorem noTI_m10K : noTIK (pslK ++ m10tK) ivM10K = true := by decide +kernel

theorem noTI_pglK : noTIK (pslK ++ pgltK) ivPGLK = true := by decide +kernel

theorem noTI_autK : noTIK autK AutA6K.invK = true := by decide +kernel

@[expose] noncomputable def g3tK (a b t : ℕ) : Bool :=
  anyK (fun g => commLaneK 10 g t && !(commLaneK 10 g a && commLaneK 10 g b)) pslK

@[expose] noncomputable def g3K : Bool :=
  allK (fun a => allK (fun b => Nat.beq a b || !commLaneK 10 a b ||
    (g3tK a b a || (g3tK a b b || g3tK a b (mulK 10 a b)))) AutA6K.invK) AutA6K.invK

theorem g3K_true : g3K = true := by decide +kernel

theorem isC_tMul : IsC [0, 4, 8, 5, 6, 1, 7, 2, 3, 9] := ⟨_, codeK_tMul⟩

theorem isC_tMulFrob : IsC [0, 4, 8, 7, 2, 3, 5, 6, 1, 9] := ⟨_, codeK_tMulFrob⟩

theorem coset_codes {t : List ℕ} {T : List ℕ} (ht : IsC t)
    (hT : (Core.pslLit.map (fun c => Core.cmul c t)).map pk = T) :
    (∀ c ∈ Core.pslLit ++ Core.pslLit.map (fun c => Core.cmul c t), IsC c) ∧
      (Core.pslLit ++ Core.pslLit.map (fun c => Core.cmul c t)).map pk = pslK ++ T := by
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases List.mem_append.1 hc with h | h
    · exact isC_of_psl h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
      exact isC_cmul (isC_of_psl hy) ht
  · rw [List.map_append, beq_iff_eq.1 pslK_pin, hT]

@[expose] noncomputable def invS (c k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.add acc (Nat.shiftLeft i (Nat.mul 4 (rd c i)))) k

@[expose] noncomputable def invPK (c : ℕ) : ℕ := invS c 10

theorem invS_sum (c k : ℕ) : invS c k = ∑ i ∈ Finset.range k, i * 16 ^ rd c i := by
  induction k with
  | zero => simp [invS]
  | succ k ih =>
    change invS c k + k <<< (4 * rd c k) = _
    rw [Nat.shiftLeft_eq, pow_mul, ih, Finset.sum_range_succ]
    norm_num

theorem encF_sum (a : ℕ → ℕ) (k : ℕ) : encF a k = ∑ i ∈ Finset.range k, a i * 16 ^ i := by
  induction k with
  | zero => simp [encF_zero]
  | succ k ih => rw [encF_succ, ih, Finset.sum_range_succ]

theorem enc_inv (σ : P10) : enc σ⁻¹ = invPK (enc σ) := by
  rw [enc, invPK, encF_sum, invS_sum, Finset.sum_range, Finset.sum_range]
  refine (Equiv.sum_comp σ _).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  beta_reduce
  rw [dif_pos (σ i).isLt, rd_enc (by norm_num) σ i]
  simp

theorem isC_invC {a : List ℕ} (ha : IsC a) : IsC (Setup.X3Aut.invC a) := by
  obtain ⟨σ, rfl⟩ := ha
  exact ⟨σ⁻¹, Setup.X3Aut.code_inv σ⟩

theorem pk_invC {a : List ℕ} (ha : IsC a) : pk (Setup.X3Aut.invC a) = invPK (pk a) := by
  obtain ⟨σ, rfl⟩ := ha
  rw [← Setup.X3Aut.code_inv, pk_code, pk_code, enc_inv]

@[expose] noncomputable def ord4sK (s : ℕ) : Bool := !Nat.beq s idK && Nat.beq (mulK 10 s s) idK

@[expose] noncomputable def ord4K (c : ℕ) : Bool := ord4sK (mulK 10 c c)

@[expose] noncomputable def oddK (K IV : List ℕ) : Bool :=
  allK (fun a => anyK (fun g => ord4K (mulK 10 a (mulK 10 (mulK 10 g a) (invPK g)))) K) IV

theorem odd_m10K : oddK (pslK ++ m10tK) ivM10K = true := by decide +kernel

theorem odd_pglK : oddK (pslK ++ pgltK) ivPGLK = true := by decide +kernel

theorem odd_autK : oddK autK AutA6K.invK = true := by decide +kernel

theorem cmul_cid {a : List ℕ} (ha : IsC a) : Core.cmul a Core.cid = a := by
  obtain ⟨σ, rfl⟩ := ha
  rw [← code_one, ← code_mul, mul_one]

theorem isC_m10Rep : IsC [0, 8, 4, 5, 1, 6, 7, 3, 2, 9] :=
  ⟨A6Models.perm10 [[1, 8, 2, 4], [3, 5, 6, 7]], by decide +kernel⟩

theorem isC_tFrob : IsC [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] := ⟨A6Models.tFrob, by decide +kernel⟩

theorem isC_dL : IsC [3, 7, 9, 0, 8, 6, 5, 1, 4, 2] :=
  ⟨A6Models.perm10 [[0, 3], [1, 7], [2, 9], [4, 8], [5, 6]], by decide +kernel⟩

theorem pk_m10Rep : pk [0, 8, 4, 5, 1, 6, 7, 3, 2, 9] = 627994350720 := by decide +kernel

theorem pk_tFrob : pk [0, 1, 2, 6, 7, 8, 3, 4, 5, 9] = 641083073040 := by decide +kernel

theorem pk_dL : pk [3, 7, 9, 0, 8, 6, 5, 1, 4, 2] = 154977962355 := by decide +kernel

@[expose] noncomputable def inM10K (c : ℕ) : Bool :=
  memK c pslK || memK (mulK 10 c 627994350720) pslK

@[expose] noncomputable def inS6K (c : ℕ) : Bool :=
  memK c pslK || memK (mulK 10 c 641083073040) pslK

theorem in2_pk {a r : List ℕ} {rK : ℕ} (ha : IsC a) (hr : IsC r) (hrK : pk r = rK) :
    ([Core.cid, r].any fun rinv => Core.pslLit.contains (Core.cmul a rinv)) =
      (memK (pk a) pslK || memK (mulK 10 (pk a) rK) pslK) := by
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [cmul_cid ha, contains_pk (fun c hc => isC_of_psl hc) ha,
    contains_pk (fun c hc => isC_of_psl hc) (isC_cmul ha hr), pk_cmul ha hr, hrK,
    beq_iff_eq.1 pslK_pin]

theorem inS6_pk {a : List ℕ} (ha : IsC a) : Core.inS6 a = inS6K (pk a) := by
  have e : ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℕ) = Core.cid := rfl
  unfold Core.inS6 Core.s6RepsInv inS6K
  rw [e]
  exact in2_pk ha isC_tFrob pk_tFrob

@[expose] noncomputable def centCK (C : List ℕ) : Bool :=
  allK (fun a => !Nat.beq (mulK 10 a a) idK || inM10K a || inS6K a ||
    allK (fun b => !Nat.beq (mulK 10 b b) idK || inM10K b || inS6K b ||
      anyK (fun p => peqK p a b p) C) C) C

theorem centK_true : allK (fun t => !Nat.beq (mulK 10 t t) idK || Nat.beq t idK ||
    centCK (autK.filter fun x => commLaneK 10 x t)) pslK = true := by
  decide +kernel

theorem outS6K_true : allK (fun c => !Nat.beq (mulK 10 c c) idK || inM10K c || !inS6K c ||
    (anyK (fun y => peqK y c 641083073040 y) pslK ||
      anyK (fun y => peqK y c 641083073040 y) m10tK)) autK = true := by
  decide +kernel

theorem outDK_true : allK (fun c => !Nat.beq (mulK 10 c c) idK || inM10K c || inS6K c ||
    (anyK (fun y => peqK y c 154977962355 y) pslK ||
      anyK (fun y => peqK y c 154977962355 y) m10tK)) autK = true := by
  decide +kernel

theorem any_or_map (L : List (List ℕ)) (A B : List ℕ → Bool) (f : List ℕ → List ℕ) :
    (L.any fun y => A y || B (f y)) = (L.any A || (L.map f).any B) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, List.any_eq_true, List.any_eq_true, List.any_eq_true]
  simp only [List.mem_map, Bool.or_eq_true]
  constructor
  · rintro ⟨y, hy, h | h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨f y, ⟨y, hy, rfl⟩, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨_, ⟨y, hy, rfl⟩, h⟩)
    · exact ⟨y, hy, Or.inl h⟩
    · exact ⟨y, hy, Or.inr h⟩

theorem out_any_pk {c t : List ℕ} {tK : ℕ} (hc : IsC c) (ht : IsC t) (htK : pk t = tK) :
    (Core.pslLit.any fun y => Core.cmul y c == Core.cmul t y ||
      Core.cmul (Core.cmul y [0, 4, 8, 7, 2, 3, 5, 6, 1, 9]) c ==
        Core.cmul t (Core.cmul y [0, 4, 8, 7, 2, 3, 5, 6, 1, 9])) =
      (anyK (fun y => peqK y (pk c) tK y) pslK || anyK (fun y => peqK y (pk c) tK y) m10tK) := by
  rw [any_or_map Core.pslLit (fun y => Core.cmul y c == Core.cmul t y)
    (fun z => Core.cmul z c == Core.cmul t z) (fun y => Core.cmul y [0, 4, 8, 7, 2, 3, 5, 6, 1, 9])]
  have hM : ∀ z ∈ Core.pslLit.map (fun y => Core.cmul y [0, 4, 8, 7, 2, 3, 5, 6, 1, 9]), IsC z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    exact isC_cmul (isC_of_psl hy) isC_tMulFrob
  rw [← beq_iff_eq.1 pslK_pin, ← m10t_pin,
    any_pk (q := fun z => peqK z (pk c) (pk t) z) fun y hy =>
      peq_pk (isC_of_psl hy) hc ht (isC_of_psl hy),
    any_pk (q := fun z => peqK z (pk c) (pk t) z) fun y hy => peq_pk (hM y hy) hc ht (hM y hy), htK]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK
