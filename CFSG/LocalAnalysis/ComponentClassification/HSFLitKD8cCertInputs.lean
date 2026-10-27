module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cNorm

public section

namespace CFSG.ComponentClassification.HSFLit.KD8c

open Sec8

@[expose] def ccE {D : ExtData MC} (x : Ext D) : ℕ :=
  (Finset.univ.filter fun g : Ext D => g * x = x * g).card

@[expose] def cntE {D : ExtData MC} (x : Ext D) : ℕ :=
  (Finset.univ.filter fun g : Ext D => g * x = x * g ∧ (g * g = 1 ∨ g * g = x)).card

@[expose] def codeE {D : ExtData MC} (x : Ext D) : ℕ := 256 * (bif x.e then 1 else 0) + codeMC x.a

@[expose] def ofCodeE {D : ExtData MC} (c : ℕ) : Ext D := ⟨ofCode c, c / 256 % 2 == 1⟩

@[expose] def conjE {D : ExtData MC} (tab : ℕ) (x : Ext D) : Ext D :=
  ofCodeE (tget tab 9 (codeE x))

@[expose] def chi0B (bs : ℕ) (a : MC) : Bool :=
  ((List.range 8).zip (MC.nfBits a)).foldl (fun acc p => acc ^^ (bs.testBit p.1 && p.2)) false

@[expose] def chiB {D : ExtData MC} (bs : ℕ) (qb : Bool) (x : Ext D) : Bool :=
  chi0B bs x.a ^^ (qb && x.e)

@[expose] def seedB {D : ExtData MC} (q0 : Bool) (x : Ext D) : Bool :=
  !x.e && (inE 6 x.a || inE 7 x.a || (q0 && codeMC x.a == 16))

@[expose] def checkA (D : ExtData MC) (bs : ℕ) (qb q0 : Bool) (reps : List ℕ) (tab g cg : ℕ) :
    Bool :=
  reps.all (fun r => seedB q0 (ofCodeE (D := D) r)) &&
  decide (∀ x : Ext D, x * x = 1 → x ≠ 1 → chiB bs qb x = true →
    codeE (conjE tab x * x * (conjE tab x)⁻¹) ∈ reps) &&
  decide (∀ x : Ext D, chiB bs qb x = false → x * x ≠ 1 → x * x * (x * x) = 1 →
    codeE (conjE tab (x * x) * (x * x) * (conjE tab (x * x))⁻¹) ∈ reps) &&
  chiB bs qb (ofCodeE (D := D) g) &&
  decide (ofCodeE (D := D) g * ofCodeE g * (ofCodeE g * ofCodeE g) = 1) &&
  decide (ofCodeE (D := D) cg * (ofCodeE g * ofCodeE g) * (ofCodeE cg)⁻¹ = Ext.incl D MC.t ∨
    ofCodeE (D := D) cg * (ofCodeE g * ofCodeE g) * (ofCodeE cg)⁻¹ = Ext.incl D MC.u)

@[expose] def checkE (D : ExtData MC) (bs : ℕ) (qb : Bool) (reps : List ℕ) (tab : ℕ) : Bool :=
  decide (64 ≤ ccE (Ext.incl D MC.u)) && chiB bs qb (Ext.incl D MC.u) &&
  reps.all (fun r => seedB false (ofCodeE (D := D) r) || decide (ccE (ofCodeE (D := D) r) ≠ 64) ||
    decide (cntE (ofCodeE (D := D) r) ≠ cntE (Ext.incl D MC.u))) &&
  decide (∀ x : Ext D, x * x = 1 → x ≠ 1 → chiB bs qb x ≠ chiB bs qb (Ext.incl D MC.u) →
    codeE (conjE tab x * x * (conjE tab x)⁻¹) ∈ reps)

@[expose] def tab10 : ℕ :=
  110428046860940689156172021747206708968014136185161537319772894133223424 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (3458666282978755125533023865187104338217152723144833911814081124237312 + 2 ^ 256 *
  (145444772511744 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (745026431634804601281461715535957083823099871232 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (13479973448132426568143297129295324983104982916858859383265337278464)))))))

@[expose] def tab11 : ℕ :=
  60926495659095503277573183373312 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (11443069879996025999503544246455641016455135232))

@[expose] def tab20 : ℕ :=
  60926495659095503277573183373312 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (15727600551263721970570790117245872737380990976))

@[expose] def tab21 : ℕ :=
  60926495659095503277573183373312 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (15727600551263721970570790117245872737380990976))

@[expose] def tab70 : ℕ :=
  60926495659095503277573183373312 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (12867529979552169552669439892280148406237659136))

@[expose] def tab71 : ℕ :=
  60926495659095503277573183373312 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (12867529979552169552669439892280148406237659136))

@[expose] def tab50 : ℕ :=
  110428046860940689156172021749298775635267333463115063854880568813551616 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (3458666282978755125533036732717083890386705392584726191962487361896448 + 2 ^ 256 *
  (145444772511744 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (963262934128865406684993953090312584215405155673464538927613207214880194560 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (6190866473071135717328976008462491830848644748036836739980784228747968512 + 2 ^ 256 *
  (180566197559885824 + 2 ^ 256 *
  (14134776518227074636666380005943348126619871175087243623303336047834849280 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (631873750011343704833835024629780591660474343705606048123856093184 + 2 ^ 256 *
  (17179869184 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (82248899793143162811073979620946607641057069507828855889616873455616 + 2 ^ 256 *
  (548063113999088594326517211960402982971824406528 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (1130782121458165970933501962418076086236884487380261486799706218580461142080)))))))))))))))))

@[expose] def tab51 : ℕ :=
  110428046860940689156172021749298775635267333463115063854880568813551616 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (3458666282978755125533036732717083890386705392584726191962487361896448 + 2 ^ 256 *
  (145444772511744 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (963262934128865406684993953090312584215405155673464538927613207214880194560 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (6190866473071135717328976008462491830848644748036836739980784228747968512 + 2 ^ 256 *
  (180566197559885824 + 2 ^ 256 *
  (27606985387162255149739023449108101809804435888681546220650096895197184 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (1234128417990904531616226886918012878737051899225184897511456768 + 2 ^ 256 *
  (33554432 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (280608314367533360295176812523726321069333399207936 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (2208558830972980411979496020347804855931415014411699066105039670346776576)))))))))))))))))

@[expose] def tab61 : ℕ :=
  110428046860940689156172021749298775635267333463115063854880568813551616 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (3458666282978755125533038168327556045795570128039305333179428722704384 + 2 ^ 256 *
  (145444772511744 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (1416459206244520987223013793987357487115933848461205319677602510691935191040 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (3545772185663652145794605824244821826196757234452536092714746819976888320 + 2 ^ 256 *
  (216524625834672128 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (16384 + 2 ^ 256 *
  (84808659109362447819998280035660088759719227050029709989837097662045749248 + 2 ^ 256 *
  (2305843009213693952 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (4083388403051261561561504095497749528576 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (32138760885179805510844686364693987065859473869374764997410816)))))))))))))))))

@[expose] def chk10 : Bool :=
  checkA (D 1 (by decide) (by decide) 0) 1 false true [1, 8, 16] tab10 272 48

@[expose] def chk11 : Bool :=
  checkA (D 1 (by decide) (by decide) 1) 0 true false [1, 2, 8] tab11 272 16

@[expose] def chk20 : Bool :=
  checkA (D 2 (by decide) (by decide) 0) 0 true false [1, 2, 8] tab20 276 48

@[expose] def chk21 : Bool :=
  checkA (D 2 (by decide) (by decide) 1) 0 true false [1, 2, 8] tab21 276 16

@[expose] def chk70 : Bool :=
  checkA (D 7 (by decide) (by decide) 0) 0 true false [1, 2, 8] tab70 276 48

@[expose] def chk71 : Bool :=
  checkA (D 7 (by decide) (by decide) 1) 0 true false [1, 2, 8] tab71 276 16

@[expose] def chk50 : Bool :=
  checkE (D 5 (by decide) (by decide) 0) 10 false [1, 2, 4, 8, 16, 256, 275] tab50

@[expose] def chk51 : Bool :=
  checkE (D 5 (by decide) (by decide) 1) 10 false [1, 2, 4, 8, 16, 274] tab51

@[expose] def chk61 : Bool :=
  checkE (D 6 (by decide) (by decide) 1) 10 false [1, 2, 4, 8, 16, 278] tab61

end CFSG.ComponentClassification.HSFLit.KD8c
