
module

public import CFSG.Certificates.Kernel.HeSylKSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.GrSLit.HeldFix

@[expose] def heAutSylowCheckG (gs gQ gE gF gU : List (Array Nat)) (z r s : Array Nat) : Bool :=
  let X := eltsN 32 gs
  let Q := eltsN 32 gQ
  let E := eltsN 32 gE
  let F := eltsN 32 gF
  let U := eltsN 32 gU
  enumCheckN 32 gs 2048 && enumCheckN 32 gQ 128 && enumCheckN 32 gE 64 &&
    enumCheckN 32 gF 64 && enumCheckN 32 gU 16 &&
    validA 32 z && validA 32 r && validA 32 s &&
    gQ.all (inLN 32 X) && gE.all (inLN 32 X) && gF.all (inLN 32 X) &&
    gU.all (inLN 32 Q) && inLN 32 Q z && inLN 32 X r && inLN 32 X s &&
    gs.all (fun g => gQ.all fun q => inLN 32 Q (conjA 32 g q)) &&
    gQ.all (fun g => gE.all fun q => inLN 32 E (conjA 32 g q)) &&
    gQ.all (fun g => gF.all fun q => inLN 32 F (conjA 32 g q)) &&
    eqA 32 (mulN 32 z z) (idA 32) && !(eqA 32 z (idA 32)) && gs.all (commN 32 z) &&
    X.all (fun x => !(gs.all (commN 32 x)) || inZN 32 z x) &&
    Q.all (fun x => inZN 32 z (mulN 32 x x)) &&
    Q.all (fun x => !(gQ.all (commN 32 x)) || inZN 32 z x) &&
    gQ.any (fun a => gQ.any fun b => !(commN 32 a b)) &&
    E.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    gE.all (fun a => gE.all (commN 32 a)) &&
    F.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    gF.all (fun a => gF.all (commN 32 a)) &&
    U.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    gU.all (fun a => gU.all (commN 32 a)) &&
    gE.any (fun a => !(inLN 32 F a)) &&
    inLN 32 Q (powN 32 r 8) && inLN 32 Q (mulN 32 s s) &&
    inLN 32 Q (mulN 32 (mulN 32 s r) (mulN 32 s r)) &&
    (List.range 7).all (fun i => !(inLN 32 Q (powN 32 r (i + 1)))) &&
    (List.range 8).all (fun i => !(inLN 32 Q (mulN 32 s (powN 32 r i)))) &&
    uniqQN 32 X Q z && uniqEN 32 X E F

theorem heAutSylowCheck_eq : heAutSylowCheck = heAutSylowCheckG hfT0Tabs32.toList heAutQ32
    heAutE32 heAutF32 heAutU32 heAutZ32 heAutR32 heAutS32 := rfl

open CFSG.KLie.CT (anyN andB orB notB)

theorem uniqQN_of {n w NX NQ : Nat} {TX TQ : Nat → Nat} {z FZ F1 : Nat}
    (hX : ∀ i < NX, PP n w (TX i)) (hQ : ∀ i < NQ, PP n w (TQ i)) (hz : PP n w z)
    (hf : flagsK n w NX TX z FZ F1 = true) (hu : cntR (uqAt n w NX TX NQ TQ FZ z) 0 NX < 64) :
    uniqQN n ((List.range NX).map fun i => unpack n w (TX i))
      ((List.range NQ).map fun i => unpack n w (TQ i)) (unpack n w z) = true := by
  have e : (((List.range NX).map fun i => unpack n w (TX i)).filter fun x =>
      !(inLN n ((List.range NQ).map fun i => unpack n w (TQ i)) x) &&
        inZN n (unpack n w z) (mulN n x x) &&
        !(goodQN n ((List.range NX).map fun i => unpack n w (TX i)) (unpack n w z) x)).length =
      cntR (uqAt n w NX TX NQ TQ FZ z) 0 NX := by
    rw [cntR_eq, List.filter_map, List.length_map]
    congr 1
    refine List.filter_congr fun i hi => ?_
    have hi' := List.mem_range.1 hi
    have px := hX i hi'
    have hb : inZ n w z (pcomp n w (mask w) (TX i) (TX i)) = bitK FZ i :=
      (flagsK_spec hf hi').1.symm
    simp only [Function.comp_apply]
    unfold uqAt
    rw [strictB_eq', andB_eq, andB_eq, notB_eq, notB_eq, inLN_eq px hQ, mulN_PP px px,
      inZN_PP hz (px.mul px), goodQN_eq hX hz px hf, hb]
    generalize bitK FZ i = a
    generalize HexaK.inL NQ TQ (TX i) = b
    generalize goodQK n w NX TX FZ z (TX i) = c
    cases a <;> cases b <;> cases c <;> rfl
  unfold uniqQN
  rw [e]
  exact decide_eq_true hu

theorem heAutK_sound {w : Nat} {gs gQ gE gF gU : List (Array Nat)}
    {cX cQ cE cF cU NX NQ NE NF NU : Nat}
    {GX GQ GE GF GU TX TQ TE TF TU EX EQ EE EF EU SX SQ SE SF SU : Nat → Nat}
    {z r s : Array Nat} {Pz Pr Ps FZ F1 : Nat}
    (pX : Pin 32 w gs cX GX NX TX EX SX) (pQ : Pin 32 w gQ cQ GQ NQ TQ EQ SQ)
    (pE : Pin 32 w gE cE GE NE TE EE SE) (pF : Pin 32 w gF cF GF NF TF EF SF)
    (pU : Pin 32 w gU cU GU NU TU EU SU)
    (hsz : NX = 2048 ∧ NQ = 128 ∧ NE = 64 ∧ NF = 64 ∧ NU = 16)
    (hz : z = unpack 32 w Pz) (hr : r = unpack 32 w Pr) (hs : s = unpack 32 w Ps)
    (hpz : permOK 32 w (mask w) (32 * w) Pz (pinvS 32 w (mask w) Pz) = true)
    (hpr : permOK 32 w (mask w) (32 * w) Pr (pinvS 32 w (mask w) Pr) = true)
    (hps : permOK 32 w (mask w) (32 * w) Ps (pinvS 32 w (mask w) Ps) = true)
    (hf : flagsK 32 w NX TX Pz FZ F1 = true)
    (hrest : restK 32 w cX GX NX TX cQ GQ NQ TQ cE GE NE TE cF GF NF TF cU GU NU TU Pz Pr Ps = true)
    (huq : cntR (uqAt 32 w NX TX NQ TQ FZ Pz) 0 NX < 64)
    (hue : allR (ueAt 32 w NX TX NE TE NF TF F1) 0 NX = true) :
    heAutSylowCheckG gs gQ gE gF gU z r s = true := by
  obtain ⟨hNX, hNQ, hNE, hNF, hNU⟩ := hsz
  have sX := PP_pts pX.ok pX.perm
  have sQ := PP_pts pQ.ok pQ.perm
  have sE := PP_pts pE.ok pE.perm
  have sF := PP_pts pF.ok pF.perm
  have sU := PP_pts pU.ok pU.perm
  have qX := PP_gen pX.ok pX.perm
  have qQ := PP_gen pQ.ok pQ.perm
  have qE := PP_gen pE.ok pE.perm
  have qF := PP_gen pF.ok pF.perm
  have qU := PP_gen pU.ok pU.perm
  have gX := gens_eq pX.size pX.bind
  have gQ' := gens_eq pQ.size pQ.bind
  have gE' := gens_eq pE.size pE.bind
  have gF' := gens_eq pF.size pF.bind
  have gU' := gens_eq pU.size pU.bind
  have hsz : szOK 32 w = true := (sX 0 (by omega)).sz
  have pz : PP 32 w Pz := PP_of_permOK hsz hpz
  have pr : PP 32 w Pr := PP_of_permOK hsz hpr
  have ps : PP 32 w Ps := PP_of_permOK hsz hps
  have cX := enumCheckN_of pX.size pX.bind pX.perm pX.ok pX.fuel
  have cQ' := enumCheckN_of pQ.size pQ.bind pQ.perm pQ.ok pQ.fuel
  have cE' := enumCheckN_of pE.size pE.bind pE.perm pE.ok pE.fuel
  have cF' := enumCheckN_of pF.size pF.bind pF.perm pF.ok pF.fuel
  have cU' := enumCheckN_of pU.size pU.bind pU.perm pU.ok pU.fuel
  rw [hNX] at cX
  rw [hNQ] at cQ'
  rw [hNE] at cE'
  rw [hNF] at cF'
  rw [hNU] at cU'
  subst hz hr hs
  simp only [heAutSylowCheckG]
  rw [eltsN_eq pX.size pX.bind pX.ok pX.fuel, eltsN_eq pQ.size pQ.bind pQ.ok pQ.fuel,
    eltsN_eq pE.size pE.bind pE.ok pE.fuel, eltsN_eq pF.size pF.bind pF.ok pF.fuel,
    eltsN_eq pU.size pU.bind pU.ok pU.fuel]
  unfold restK at hrest
  simp only [andB_eq, Bool.and_eq_true] at hrest
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24, g25, g26⟩ := hrest
  unfold elemAbK at g18 g19 g20
  simp only [andB_eq, Bool.and_eq_true] at g18 g19 g20
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨cX, cQ', cE', cF', cU', validA_unpack hpz, validA_unpack hpr, validA_unpack hps,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, uniqQN_of sX sQ pz hf huq, uniqEN_of sX sE sF hf hue⟩
  ·
    rw [gQ', all_map_congr fun k hk => inLN_eq (qQ k (List.mem_range.1 hk)) sX]
    exact List.all_eq_true.2 fun k hk => allN_spec g1 k (List.mem_range.1 hk)
  ·
    rw [gE', all_map_congr fun k hk => inLN_eq (qE k (List.mem_range.1 hk)) sX]
    exact List.all_eq_true.2 fun k hk => allN_spec g2 k (List.mem_range.1 hk)
  ·
    rw [gF', all_map_congr fun k hk => inLN_eq (qF k (List.mem_range.1 hk)) sX]
    exact List.all_eq_true.2 fun k hk => allN_spec g3 k (List.mem_range.1 hk)
  ·
    rw [gU', all_map_congr fun k hk => inLN_eq (qU k (List.mem_range.1 hk)) sQ]
    exact List.all_eq_true.2 fun k hk => allN_spec g4 k (List.mem_range.1 hk)
  · rw [inLN_eq pz sQ]
    exact g5
  · rw [inLN_eq pr sX]
    exact g6
  · rw [inLN_eq ps sX]
    exact g7
  ·
    rw [gX, gQ', List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, List.all_map]
    refine List.all_eq_true.2 fun q hq => ?_
    rw [List.mem_range] at hq
    rw [Function.comp_apply, conjA_PP (qX k hk) (qQ q hq),
      inLN_eq ((qX k hk).conjK (qQ q hq)) sQ]
    exact allN_spec (allN_spec g8 k hk) q hq
  ·
    rw [gQ', gE', List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, List.all_map]
    refine List.all_eq_true.2 fun q hq => ?_
    rw [List.mem_range] at hq
    rw [Function.comp_apply, conjA_PP (qQ k hk) (qE q hq),
      inLN_eq ((qQ k hk).conjK (qE q hq)) sE]
    exact allN_spec (allN_spec g9 k hk) q hq
  ·
    rw [gQ', gF', List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, List.all_map]
    refine List.all_eq_true.2 fun q hq => ?_
    rw [List.mem_range] at hq
    rw [Function.comp_apply, conjA_PP (qQ k hk) (qF q hq),
      inLN_eq ((qQ k hk).conjK (qF q hq)) sF]
    exact allN_spec (allN_spec g10 k hk) q hq
  · rw [mulN_PP pz pz, eqA_id_PP (pz.mul pz)]
    exact g11
  · rw [eqA_id_PP pz, ← notB_eq]
    exact g12
  · rw [gX, all_map_congr (p := commN 32 (unpack 32 w Pz))
      fun k hk => commN_PP pz (qX k (List.mem_range.1 hk))]
    exact List.all_eq_true.2 fun k hk => allN_spec g13 k (List.mem_range.1 hk)
  ·
    rw [List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have pi := sX i hi'
    have h1 := allN_spec g14 i hi'
    rw [strictB_eq', orB_eq, notB_eq, allN_eq'] at h1
    rw [Function.comp_apply, gX, all_map_congr (p := commN 32 (unpack 32 w (TX i)))
      fun k hk => commN_PP pi (qX k (List.mem_range.1 hk)), inZN_PP pz pi]
    exact h1
  · rw [List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have pi := sQ i hi'
    have h1 := allN_spec g15 i hi'
    rw [strictB_eq'] at h1
    rw [Function.comp_apply, mulN_PP pi pi, inZN_PP pz (pi.mul pi)]
    exact h1
  ·
    rw [List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have pi := sQ i hi'
    have h1 := allN_spec g16 i hi'
    rw [strictB_eq', orB_eq, notB_eq, allN_eq'] at h1
    rw [Function.comp_apply, gQ', all_map_congr (p := commN 32 (unpack 32 w (TQ i)))
      fun k hk => commN_PP pi (qQ k (List.mem_range.1 hk)), inZN_PP pz pi]
    exact h1
  ·
    simp only [anyN_eq, List.any_eq_true, List.mem_range, notB_eq] at g17
    obtain ⟨a, ha, b, hb, hab⟩ := g17
    rw [gQ']
    refine List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩,
      List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩, ?_⟩⟩
    rw [commN_PP (qQ a ha) (qQ b hb)]
    exact hab
  · rw [List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have pi := sE i hi'
    have h1 := allN_spec g18.1 i hi'
    rw [strictB_eq'] at h1
    rw [Function.comp_apply, mulN_PP pi pi, eqA_id_PP (pi.mul pi)]
    exact h1
  · rw [gE']
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range] at ha hb
    rw [commN_PP (qE a ha) (qE b hb)]
    exact allN_spec (allN_spec g18.2 a ha) b hb
  · rw [List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have pi := sF i hi'
    have h1 := allN_spec g19.1 i hi'
    rw [strictB_eq'] at h1
    rw [Function.comp_apply, mulN_PP pi pi, eqA_id_PP (pi.mul pi)]
    exact h1
  · rw [gF']
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range] at ha hb
    rw [commN_PP (qF a ha) (qF b hb)]
    exact allN_spec (allN_spec g19.2 a ha) b hb
  · rw [List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have pi := sU i hi'
    have h1 := allN_spec g20.1 i hi'
    rw [strictB_eq'] at h1
    rw [Function.comp_apply, mulN_PP pi pi, eqA_id_PP (pi.mul pi)]
    exact h1
  · rw [gU']
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range] at ha hb
    rw [commN_PP (qU a ha) (qU b hb)]
    exact allN_spec (allN_spec g20.2 a ha) b hb
  ·
    simp only [anyN_eq, List.any_eq_true, List.mem_range, notB_eq] at g21
    obtain ⟨a, ha, hab⟩ := g21
    rw [gE']
    refine List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩, ?_⟩
    rw [inLN_eq (qE a ha) sF]
    exact hab
  · rw [powN_PP pr 8, inLN_eq (pw_PP pr 8) sQ]
    exact g22
  · rw [mulN_PP ps ps, inLN_eq (ps.mul ps) sQ]
    exact g23
  · rw [mulN_PP ps pr, mulN_PP (ps.mul pr) (ps.mul pr), inLN_eq ((ps.mul pr).mul (ps.mul pr)) sQ]
    rw [strictN_eq'] at g24
    exact g24
  ·
    refine List.all_eq_true.2 fun i hi => ?_
    have h1 := allN_spec g25 i (List.mem_range.1 hi)
    rw [powN_PP pr (i + 1), inLN_eq (pw_PP pr (i + 1)) sQ, ← notB_eq]
    exact h1
  ·
    refine List.all_eq_true.2 fun i hi => ?_
    have h1 := allN_spec g26 i (List.mem_range.1 hi)
    rw [powN_PP pr i, mulN_PP ps (pw_PP pr i), inLN_eq (ps.mul (pw_PP pr i)) sQ, ← notB_eq]
    exact h1

end CFSG.KC.HeAutK

end
