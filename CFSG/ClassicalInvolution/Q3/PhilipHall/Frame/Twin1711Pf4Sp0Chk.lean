module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0Pack

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> simp

theorem getD_default' {α : Type} (l : List α) (n : ℕ) (d : α) (h : l.length ≤ n) :
    l.getD n d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

@[expose] def pA : ℕ := 50252747108241841391946595921241741878490438704899522398251683912

@[expose] def pB : ℕ := 51201585946502785866740666920841637558834534735787540668305425680

@[expose] def pBi : ℕ := 35306867816290265034160114262163492613756832031677829034186408965

@[expose] def baseGl : List ℕ := [pA, pB, pA, pBi]

@[expose] def invL (l : ℕ) : ℕ :=
  ([2, 3, 0, 1, 7, 8, 9, 4, 5, 6, 11, 10, 14, 15, 12, 13, 20, 21, 22, 23, 16, 17, 18, 19] :
    List ℕ).getD l l

@[expose] def invW (w : List ℕ) : List ℕ := (w.map invL).reverse

@[expose] def letterWords : List (List ℕ) :=
  [[0], [1], [2], [3], [0, 1], [1, 0, 1, 1, 0, 3, 3, 0, 3], [0, 3, 0, 3, 0, 3, 3, 0, 3, 0, 3], [3,
    2], [1, 2, 1, 1, 2, 3, 3, 2, 3], [1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2], [1, 0, 1, 0, 1, 0, 1, 0,
    1, 0, 1, 0], [2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3], [0, 1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 3, 3,
    0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 3, 0, 3, 0, 3, 0, 1, 0, 1, 1,
    0, 1, 1, 0, 3, 3, 0, 3], [3, 2, 3, 2, 3, 2], [1, 2, 1, 1, 2, 3, 3, 2, 3, 3, 2, 3, 2, 1, 2, 1,
    2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3], [1,
    1, 1, 2, 3], [1, 1, 2, 1, 0, 1, 0, 1, 0, 3, 3], [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3,
    3, 0, 3, 0, 3, 0, 3, 3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 3, 3, 0, 1, 1, 1], [1, 1, 2, 1, 0, 1, 0,
    0, 1, 1, 1], [1, 0, 3, 3, 3], [1, 1, 2, 3, 2, 3, 2, 3, 0, 3, 3], [3, 3, 3, 2, 1, 1, 1, 1, 0,
    1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [3,
    3, 3, 2, 2, 3, 2, 3, 0, 3, 3]]

@[expose] def GL : List ℕ := letterWords.map (evalW baseGl)

@[expose] def invChk : Bool :=
  (List.range 24).all fun l => compP (GL.getD l oneP) (GL.getD (invL l) oneP) == oneP

@[expose] def egWords : List (List ℕ) := [[12], [13], [10, 12, 11], [10, 13, 11]]

@[expose] def Egp : List ℕ := egWords.map (evalW GL)

@[expose] def L0w : List (List ℕ) :=
  [[], [12, 12], [12], [12, 12, 12], [13], [13, 12, 12], [12, 13], [12, 13, 12, 12]]

@[expose] def L1w : List (List ℕ) := L0w.map fun w => [10] ++ w ++ [11]

@[expose] def L0p : List ℕ := L0w.map (evalW GL)

@[expose] def L1p : List ℕ := L1w.map (evalW GL)

@[expose] def Ywords : List (List ℕ) :=
  [[4, 5, 6, 5, 4, 5, 6, 5, 4, 4, 4], [4, 6, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4], [4, 5, 4, 5, 4, 4, 4,
    4, 4, 4]]

@[expose] def Yp : List ℕ := Ywords.map (evalW GL)

@[expose] def YIp : List ℕ := Ywords.map fun w => evalW GL (invW w)

@[expose] def r2p : ℕ := evalW GL [12, 12]

@[expose] def Badw : List (ℕ × List ℕ) :=
  [
    (18361329132179190861890454342475534231092699722766488802983161920, [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]),
    (53543800154932361857031218298972937217734180743582616801412137024, [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 3, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3]),
    (13424834291520808867912204404675145813169391916635726345566965824, [3, 2, 3, 2, 3, 2, 3, 2, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 3, 3, 2, 1, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 1, 1, 2, 3, 3, 3, 3]),
    (44699091407157755293469336495573102825392593475323808878467833920, [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 2, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 3, 0, 3, 3, 0, 3, 3, 0, 1, 2, 1, 1, 2, 3, 3, 3]),
    (32142527746131748789541083630093058074225282885812294867469561920, [3, 3, 2, 3, 3, 2, 1, 0, 1, 1, 0, 1, 0, 3, 3, 3, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 0]),
    (58479898843888825753105740678033501423428493491793125754733858944, [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1]),
    (21705811385120483356658848443012106903067982115794713102273224896, [1, 1, 1, 0, 3, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 3, 3, 2, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
    (55190088152823651462257531697684944408312106695822842915601260800, [3, 3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 3, 2, 1, 2, 3, 2, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3, 3, 0, 1, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3]),
    (36750399566823173423759052051693104627719756364153910021692612928, [0, 1, 0, 1, 1, 0, 3, 3, 3, 0, 1, 1, 0, 1, 0, 1, 0, 3, 3, 3, 0, 3, 3, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 3]),
    (23350915405077529471616088016961949825249425464554081983134704000, [3, 3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 3, 0, 3, 3, 3, 3, 2, 3, 3, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 0, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 3]),
    (36749213300411791197016913911114195829661727286728579635775033728, [1, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 2, 3, 3, 3, 3, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3]),
    (37087882253073082729651862325422125348736190108943466491231908672, [3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 3, 0, 3, 3, 3, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 0, 3, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0]),
    (5813300151834194436850722986921624017486094034396934470588281664, [3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 3, 0, 3, 3, 3, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0]),
    (10748609914955462948173099966478028617716411583093971746514383744, [3, 3, 3, 2, 3, 3, 2, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 1, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 0]),
    (58143615582203618138208140848697111264012476174140569190075765696, [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3, 0, 3, 3, 0, 3, 3, 0, 1, 2, 1, 1, 2, 3, 3, 3]),
    (32151312074931286135794684596227157840293032019282370988542010624, [3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 3, 0, 3, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 1, 1, 0, 3, 3, 0]),
    (58469276516623330308103941544543614230774328857871525068877427968, [2, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 3, 2, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 3]),
    (46389289748459204142709154939095944584308505678064698956119549312, [2, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 1, 1, 0, 1, 0, 0, 3, 3, 0, 3, 3, 0, 1, 2, 1, 1, 2, 3, 3, 3]),
    (58468881655282194285504448092909438517836943995727331167400969664, [1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 3, 3, 2, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 1, 2, 3, 2]),
    (9114976204746755325302463719536173827595030996494001252279027456, [3, 3, 3, 2, 1, 1, 2, 3, 3, 3, 0, 1, 1, 0, 3, 3, 3, 3, 2, 3, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 0, 3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 0]),
    (5823979644307867347593535320384641655748708552872897441440773888, [3, 3, 3, 2, 1, 1, 2, 3, 3, 3, 0, 1, 1, 0, 3, 3, 3, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 0, 3, 3, 0]),
    (23307576136931345343248967926526957667741501745313072498216109824, [2, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 3, 0, 3, 3, 0, 1, 0, 1, 1, 1]),
    (58137882430627432570457333574330402225120614820982336359270025152, [2, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 3, 2, 1, 1, 1, 2, 3, 3, 3, 3, 3]),
    (13480804265295453647923358381219758916005941833660781565935990720, [3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 3, 0, 3, 3, 3, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
    (37086694613404363380620870602160177755932209204519403288861143634, [2, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 1, 1, 0, 3, 2, 3, 2, 3, 3, 3, 2, 3]),
    (58142430085098976053980396748521955787108873416184824375137850066, [2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 3, 3, 2, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 3, 3, 3, 2, 1, 1]),
    (37079775481918311594959176795278823798522211867127837104796464658, [3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 3, 2, 2, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3, 3]),
    (58138673737763429792286806569991173833459619503490219762114217682, [1, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 3, 3, 2, 3, 3, 3, 2, 1, 1]),
    (58467644666332295598721125195389436599620822406450415303155128338, [3, 0, 3, 3, 0, 1, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 3]),
    (58467249412670827920892857434670995104325853472411892500262684754, [3, 0, 3, 3, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 0, 1, 1, 2, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
    (51327010663962973543673129245539980291831669190259345930691392026, [0, 3, 3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 3, 3, 0, 3, 3, 3, 3, 2, 3, 3, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 0, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 0, 3, 3, 0, 3, 0]),
    (27213591257506560207849030937572689502202894425278153020370170458, [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 3, 3, 2, 3]),
    (15127112487797613877164310076714496261524807694296414499500729370, [2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 1, 1, 1]),
    (33787573914104977349324161480793945197527069294226477529282127066, [2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 3, 3, 2, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 3]),
    (7456797135132010082796828097306946424728386023665491583910291546, [1, 0, 3, 3, 3, 0, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 1, 1, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 0, 1, 1, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 0]),
    (2521487470090830331318986308234899098821243856243369147263887578, [2, 1, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 1]),
    (24953076833211967955599798283352949858147269021117499692070010973, [2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 0, 1, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 1, 1, 1]),
    (38724485655697625677573347185600493220892219787250710510119497821, [2, 1, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3]),
    (7469462952894041654353971244230150402150463656930324113539596381, [1, 1, 2, 3, 3, 2, 1, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 0, 3, 3, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1]),
    (4178466392455141984581853120824589769592309169338892455045378141, [2, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 3, 3, 2, 1, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 1, 1, 1, 2, 3, 2, 1]),
    (39762599053034935088870740770732171945842196687348978600774526749, [1, 1, 2, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 1, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 1, 1, 0, 3, 2, 3, 2, 3, 2, 3, 3, 3, 3, 2, 1, 1]),
    (27206035392009207753521431429735298867455177653821693633458927389, [0, 1, 0, 1, 0, 3, 3, 3, 0, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 0, 3, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 0])]

@[expose] def Badp : List ℕ := Badw.map Prod.fst

@[expose] def badChk : Bool :=
  Badw.all fun b =>
    compP (compP (evalW GL b.2) r2p) (evalW GL (invW b.2)) == b.1 && b.1 != r2p

@[expose] def tLetter (l : ℕ) : Bool := decide (4 ≤ l) && decide (l ≤ 15)

@[expose] def rowVal (r : List ℕ) : ℕ := evalW GL (r.drop 4)

@[expose] def rowChk (r : List ℕ) : Bool :=
  (r.drop 4).all tLetter &&
  (decide (4 ≤ r.getD 0 0) ||
    compP (rowVal r) (Egp.getD (r.getD 0 0) oneP) != compP (Egp.getD (r.getD 0 0) oneP) (rowVal r)) &&
  (decide (3 ≤ r.getD 1 0) ||
    Badp.contains (compP (compP (compP (compP (compP (evalW GL (invW (r.drop 4)))
      (YIp.getD (r.getD 1 0) oneP)) (rowVal r)) (Yp.getD (r.getD 1 0) oneP))
      (L0p.getD (r.getD 2 0) oneP)) (L1p.getD (r.getD 3 0) oneP)))

@[expose] def chk : ℕ → List (List ℕ) → Bool
  | _, [] => true
  | prev, r :: rs => decide (prev < rowVal r) && rowChk r && chk (rowVal r) rs

@[expose] def lastV : ℕ → List (List ℕ) → ℕ
  | prev, [] => prev
  | _, r :: rs => lastV (rowVal r) rs

@[expose] def cntE (rows : List (List ℕ)) : ℕ :=
  (rows.filter fun r => decide (4 ≤ r.getD 0 0)).length

@[expose] def cntS (rows : List (List ℕ)) : ℕ :=
  (rows.filter fun r => decide (3 ≤ r.getD 1 0)).length

@[expose] def permW (G : ℕ → Equiv.Perm (Fin 36)) (w : List ℕ) : Equiv.Perm (Fin 36) :=
  (w.map G).prod

@[expose] def LG (GB : ℕ → Equiv.Perm (Fin 36)) (l : ℕ) : Equiv.Perm (Fin 36) :=
  permW GB (letterWords.getD l [])

section Sem

variable {GB : ℕ → Equiv.Perm (Fin 36)} (hB : ∀ l, PRep (baseGl.getD l oneP) (GB l))

include hB in
theorem prep_LG (l : ℕ) : PRep (GL.getD l oneP) (LG GB l) := by
  have h := evalW_rep baseGl GB hB (letterWords.getD l [])
  have e : GL.getD l oneP = evalW baseGl (letterWords.getD l []) := by
    unfold GL
    exact getD_map' (evalW baseGl) letterWords l []
  rw [e]
  exact h

include hB in
theorem prep_permW (w : List ℕ) : PRep (evalW GL w) (permW (LG GB) w) :=
  evalW_rep GL (LG GB) (prep_LG hB) w

include hB in
theorem LG_inv (hc : invChk = true) (l : ℕ) : LG GB (invL l) = (LG GB l)⁻¹ := by
  by_cases hl : l < 24
  · have h1 := List.all_eq_true.1 hc l (List.mem_range.2 hl)
    have h2 := (prep_LG hB l).comp (prep_LG hB (invL l))
    have h3 : compP (GL.getD l oneP) (GL.getD (invL l) oneP) = oneP := beq_iff_eq.1 h1
    rw [h3] at h2
    exact eq_inv_of_mul_eq_one_right (PRep.unique h2 PRep.one)
  · have h1 : letterWords.getD l [] = [] := getD_default' _ _ _ (by
      have : letterWords.length = 24 := by decide +kernel
      omega)
    have h2 : invL l = l := by
      unfold invL
      exact getD_default' _ _ _ (by simp; omega)
    rw [h2]
    have hL : LG GB l = 1 := by
      unfold LG permW
      rw [h1]
      rfl
    rw [hL]
    simp

end Sem

theorem permW_invW {G : ℕ → Equiv.Perm (Fin 36)} (hI : ∀ l, G (invL l) = (G l)⁻¹) (w : List ℕ) :
    permW G (invW w) = (permW G w)⁻¹ := by
  unfold permW invW
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  exact List.map_congr_left fun l _ => by simp [hI]

section Rows

variable {GB : ℕ → Equiv.Perm (Fin 36)} (hB : ∀ l, PRep (baseGl.getD l oneP) (GB l))
  (hc : invChk = true) (hbad : badChk = true)

include hB hc hbad in
theorem rowChk_sound {r : List ℕ} (h : rowChk r = true) :
    (∀ l ∈ r.drop 4, 4 ≤ l ∧ l ≤ 15) ∧
    (r.getD 0 0 < 4 →
      permW (LG GB) (r.drop 4) * permW (LG GB) (egWords.getD (r.getD 0 0) []) ≠
        permW (LG GB) (egWords.getD (r.getD 0 0) []) * permW (LG GB) (r.drop 4)) ∧
    (r.getD 1 0 < 3 → ∃ hw ∈ Badw.map Prod.snd,
      (permW (LG GB) (r.drop 4))⁻¹ * (permW (LG GB) (Ywords.getD (r.getD 1 0) []))⁻¹ *
          permW (LG GB) (r.drop 4) * permW (LG GB) (Ywords.getD (r.getD 1 0) []) *
          permW (LG GB) (L0w.getD (r.getD 2 0) []) * permW (LG GB) (L1w.getD (r.getD 3 0) []) =
        permW (LG GB) hw * permW (LG GB) [12, 12] * (permW (LG GB) hw)⁻¹ ∧
      (permW (LG GB) (r.drop 4))⁻¹ * (permW (LG GB) (Ywords.getD (r.getD 1 0) []))⁻¹ *
          permW (LG GB) (r.drop 4) * permW (LG GB) (Ywords.getD (r.getD 1 0) []) *
          permW (LG GB) (L0w.getD (r.getD 2 0) []) * permW (LG GB) (L1w.getD (r.getD 3 0) []) ≠
        permW (LG GB) [12, 12]) := by
  have hI : ∀ l, LG GB (invL l) = (LG GB l)⁻¹ := LG_inv hB hc
  simp only [rowChk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun l hl => ?_, fun he => ?_, fun hy => ?_⟩
  · have := h1 l hl
    simpa [tLetter] using this
  · rcases h2 with h2 | h2
    · omega
    · intro hEq
      apply h2
      have hx := prep_permW hB (r.drop 4)
      have he : PRep (Egp.getD (r.getD 0 0) oneP) (permW (LG GB) (egWords.getD (r.getD 0 0) [])) := by
        have e : Egp.getD (r.getD 0 0) oneP = evalW GL (egWords.getD (r.getD 0 0) []) := by
          unfold Egp
          exact getD_map' (evalW GL) egWords _ []
        rw [e]
        exact prep_permW hB _
      have a := hx.comp he
      have b := he.comp hx
      rw [hEq] at a
      exact a.inj b
  · rcases h3 with h3 | h3
    · omega
    · unfold rowVal at h3
      have hx := prep_permW hB (r.drop 4)
      have hxi := prep_permW hB (invW (r.drop 4))
      rw [permW_invW hI] at hxi
      have hy : PRep (Yp.getD (r.getD 1 0) oneP)
          (permW (LG GB) (Ywords.getD (r.getD 1 0) [])) := by
        have e : Yp.getD (r.getD 1 0) oneP = evalW GL (Ywords.getD (r.getD 1 0) []) := by
          unfold Yp
          exact getD_map' (evalW GL) Ywords _ []
        rw [e]
        exact prep_permW hB _
      have hyi : PRep (YIp.getD (r.getD 1 0) oneP)
          (permW (LG GB) (Ywords.getD (r.getD 1 0) []))⁻¹ := by
        have e : YIp.getD (r.getD 1 0) oneP =
            evalW GL (invW (Ywords.getD (r.getD 1 0) [])) := by
          unfold YIp
          exact getD_map' (fun w => evalW GL (invW w)) Ywords _ []
        rw [e]
        have := prep_permW hB (invW (Ywords.getD (r.getD 1 0) []))
        rwa [permW_invW hI] at this
      have h0 : PRep (L0p.getD (r.getD 2 0) oneP) (permW (LG GB) (L0w.getD (r.getD 2 0) [])) := by
        have e : L0p.getD (r.getD 2 0) oneP = evalW GL (L0w.getD (r.getD 2 0) []) := by
          unfold L0p
          exact getD_map' (evalW GL) L0w _ []
        rw [e]
        exact prep_permW hB _
      have h1' : PRep (L1p.getD (r.getD 3 0) oneP) (permW (LG GB) (L1w.getD (r.getD 3 0) [])) := by
        have e : L1p.getD (r.getD 3 0) oneP = evalW GL (L1w.getD (r.getD 3 0) []) := by
          unfold L1p
          exact getD_map' (evalW GL) L1w _ []
        rw [e]
        exact prep_permW hB _
      have hz := ((((hxi.comp hyi).comp hx).comp hy).comp h0).comp h1'
      have hzmem := List.mem_of_elem_eq_true h3
      obtain ⟨b, hb, hbz⟩ := List.mem_map.1 hzmem
      have hbc := List.all_eq_true.1 hbad b hb
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hbc
      obtain ⟨hb1, hb2⟩ := hbc
      have hinv := prep_permW hB (invW b.2)
      rw [permW_invW hI] at hinv
      have hh := ((prep_permW hB b.2).comp (prep_permW hB [12, 12])).comp hinv
      have hh' : PRep b.1 (permW (LG GB) b.2 * permW (LG GB) [12, 12] * (permW (LG GB) b.2)⁻¹) := by
        rw [← hb1]
        exact hh
      refine ⟨b.2, List.mem_map_of_mem hb, ?_, ?_⟩
      · exact PRep.unique hz (hbz ▸ hh')
      · intro hEq
        apply hb2
        rw [hEq] at hz
        have hr : PRep r2p (permW (LG GB) [12, 12]) := prep_permW hB [12, 12]
        rw [← hbz] at hz
        exact hz.inj hr

end Rows

@[expose] def chkTo : ℕ → ℕ → List (List ℕ) → Bool
  | prev, fin, [] => prev == fin
  | prev, fin, r :: rs => decide (prev < rowVal r) && rowChk r && chkTo (rowVal r) fin rs

theorem chkTo_iff : ∀ (rows : List (List ℕ)) (prev fin : ℕ),
    chkTo prev fin rows = true → chk prev rows = true ∧ lastV prev rows = fin
  | [], prev, fin, h => ⟨rfl, beq_iff_eq.1 h⟩
  | r :: rs, prev, fin, h => by
    simp only [chkTo, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have := chkTo_iff rs (rowVal r) fin h3
    refine ⟨?_, this.2⟩
    simp only [chk, Bool.and_eq_true]
    exact ⟨⟨h1, h2⟩, this.1⟩

theorem chk_append : ∀ (rs ss : List (List ℕ)) (prev : ℕ),
    chk prev (rs ++ ss) = true ↔ chk prev rs = true ∧ chk (lastV prev rs) ss = true
  | [], ss, prev => by simp [chk, lastV]
  | r :: rs, ss, prev => by
    simp only [List.cons_append, chk, lastV, Bool.and_eq_true]
    rw [chk_append rs ss (rowVal r)]
    tauto

theorem chk_sound : ∀ (rows : List (List ℕ)) (prev : ℕ), chk prev rows = true →
    (∀ r ∈ rows, rowChk r = true) ∧ (rows.map rowVal).Pairwise (· < ·) ∧
      prev ≤ lastV prev rows ∧ ∀ r ∈ rows, prev < rowVal r
  | [], prev, _ => ⟨by simp, by simp, le_refl _, by simp⟩
  | r :: rs, prev, h => by
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2, ih3, ih4⟩ := chk_sound rs (rowVal r) h3
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h2
      · exact ih1 r' hr'
    · refine List.pairwise_cons.2 ⟨?_, ih2⟩
      intro v hv
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hv
      exact ih4 r' hr'
    · exact le_trans h1.le ih3
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h1
      · exact lt_trans h1 (ih4 r' hr')

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K
