
module

public import Certificates.Data.Kernel.HeSylK
public import CFSG.Certificates.Kernel.HeAutKLoops
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.HexaKGlue
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowTests
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow (eltsN enumCheckN inLN mulN commN commZN inZN powN
  setYN goodQN uniqEN)
open CFSG.KLie.CT (anyN andB orB notB)

variable {n w : Nat}

theorem eqB_eq (a b : Bool) : eqB a b = (a == b) := by cases a <;> cases b <;> rfl

theorem cntR_eq (f : Nat → Bool) (N : Nat) : cntR f 0 N = ((List.range N).filter f).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [cntR_succ, ih, Nat.zero_add, List.range_succ, List.filter_append, List.length_append]
    cases h : f N <;> simp [h]

theorem cntR_zero {f : Nat → Bool} {N : Nat} (h : cntR f 0 N = 0) : ∀ i < N, f i = false := by
  rw [cntR_eq, List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
  intro i hi
  simpa using h i (List.mem_range.2 hi)

theorem allR_spec {f : Nat → Bool} {lo : Nat} :
    ∀ {N : Nat}, allR f lo N = true → ∀ k < N, f (lo + k) = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | N + 1, h, k, hk => by
    have e : allR f lo (N + 1) = (allR f lo N && f (lo + N)) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allR_spec h.1 k hk
    · exact h.2

theorem inZ_eq (z t : Nat) : inZ n w z t = (Nat.beq t (pidn n w) || Nat.beq t z) := by
  unfold inZ
  rw [strictB_eq', orB_eq]

theorem inZN_PP {z t : Nat} (hz : PP n w z) (ht : PP n w t) :
    inZN n (unpack n w z) (unpack n w t) = inZ n w z t := by
  unfold inZN
  rw [eqA_id_PP ht, eqA_PP ht hz, inZ_eq]

theorem commZN_PP {z a b : Nat} (hz : PP n w z) (ha : PP n w a) (hb : PP n w b) :
    commZN n (unpack n w z) (unpack n w a) (unpack n w b) = commZ n w z a b := by
  unfold commZN commN commZ
  simp only [strictB_eq', orB_eq]
  rw [mulN_PP ha hb, mulN_PP hb ha, eqA_PP (ha.mul hb) (hb.mul ha), mulN_PP (hb.mul ha) hz,
    eqA_PP (ha.mul hb) ((hb.mul ha).mul hz)]
  rfl

theorem pw_PP {a : Nat} (ha : PP n w a) : ∀ k, PP n w (pw n w a k)
  | 0 => PP.id ha.sz
  | k + 1 => by
    change PP n w (strictN (pw n w a k) fun acc => mul n w a acc)
    rw [strictN_eq']
    exact ha.mul (pw_PP ha k)

theorem powN_PP {a : Nat} (ha : PP n w a) :
    ∀ k, powN n (unpack n w a) k = unpack n w (pw n w a k)
  | 0 => idA_eq ha.sz
  | k + 1 => by
    change mulN n (unpack n w a) (powN n (unpack n w a) k) =
      unpack n w (strictN (pw n w a k) fun acc => mul n w a acc)
    rw [powN_PP ha k, mulN_PP ha (pw_PP ha k), strictN_eq']
    rfl

theorem flagsK_spec {N : Nat} {T : Nat → Nat} {z FZ F1 : Nat} (h : flagsK n w N T z FZ F1 = true)
    {i : Nat} (hi : i < N) :
    bitK FZ i = inZ n w z (mul n w (T i) (T i)) ∧
      bitK F1 i = Nat.beq (mul n w (T i) (T i)) (pidn n w) := by
  have h1 := allN_spec h i hi
  rw [strictB_eq', strictB_eq', andB_eq, Bool.and_eq_true, eqB_eq, eqB_eq] at h1
  exact ⟨beq_iff_eq.1 h1.1, beq_iff_eq.1 h1.2⟩

theorem setYK_rec (T : Nat → Nat) (FZ z x : Nat) : ∀ M acc,
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc))
        (CFSG.KLie.CT.andB (bitK FZ r) (commZ n w z x (T r)))) M acc =
      (List.range M).filter (fun r => CFSG.KLie.CT.andB (bitK FZ r) (commZ n w z x (T r))) ++ acc
  | 0, acc => rfl
  | M + 1, acc => by
    change Bool.rec (motive := fun _ => List Nat) _ _ (CFSG.KLie.CT.andB (bitK FZ M) (commZ n w z x (T M))) = _
    rw [List.range_succ, List.filter_append]
    cases h : CFSG.KLie.CT.andB (bitK FZ M) (commZ n w z x (T M))
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ M acc = _
      rw [setYK_rec T FZ z x M acc]
      simp [h]
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ M (M :: acc) = _
      rw [setYK_rec T FZ z x M (M :: acc)]
      simp [h]

theorem setYK_eq (N : Nat) (T : Nat → Nat) (FZ z x : Nat) :
    setYK n w N T FZ z x = (List.range N).filter (fun r => CFSG.KLie.CT.andB (bitK FZ r) (commZ n w z x (T r))) :=
  (setYK_rec T FZ z x N []).trans (List.append_nil _)

theorem lt_of_mem_setYK {N : Nat} {T : Nat → Nat} {FZ z x a : Nat}
    (ha : a ∈ setYK n w N T FZ z x) : a < N := by
  rw [setYK_eq] at ha
  exact List.mem_range.1 (List.mem_filter.1 ha).1

theorem setYN_eq {N : Nat} {T : Nat → Nat} {z FZ F1 x : Nat} (hT : ∀ i < N, PP n w (T i))
    (hz : PP n w z) (hx : PP n w x) (hf : flagsK n w N T z FZ F1 = true) :
    setYN n ((List.range N).map fun i => unpack n w (T i)) (unpack n w z) (unpack n w x) =
      (setYK n w N T FZ z x).map fun i => unpack n w (T i) := by
  unfold setYN
  rw [setYK_eq, List.filter_map]
  congr 1
  refine List.filter_congr fun j hj => ?_
  have hj' := List.mem_range.1 hj
  have pj := hT j hj'
  simp only [Function.comp_apply]
  rw [mulN_PP pj pj, inZN_PP hz (pj.mul pj), commZN_PP hz hx pj, andB_eq, (flagsK_spec hf hj').1]
  rfl

theorem goodQN_eq {N : Nat} {T : Nat → Nat} {z FZ F1 x : Nat} (hT : ∀ i < N, PP n w (T i))
    (hz : PP n w z) (hx : PP n w x) (hf : flagsK n w N T z FZ F1 = true) :
    goodQN n ((List.range N).map fun i => unpack n w (T i)) (unpack n w z) (unpack n w x) =
      goodQK n w N T FZ z x := by
  have e : (((setYK n w N T FZ z x).map fun i => unpack n w (T i)).any fun y =>
      ((setYK n w N T FZ z x).map fun i => unpack n w (T i)).any fun y' =>
        !(commZN n (unpack n w z) y y')) =
      (setYK n w N T FZ z x).any fun a => (setYK n w N T FZ z x).any fun b =>
        CFSG.KLie.CT.notB (commZ n w z (T a) (T b)) := by
    refine any_map_congr fun a ha => any_map_congr fun b hb => ?_
    rw [commZN_PP hz (hT a (lt_of_mem_setYK ha)) (hT b (lt_of_mem_setYK hb)), notB_eq]
  unfold goodQK
  simp only [goodQN]
  rw [setYN_eq hT hz hx hf, e, strictB_eq', List.length_map, orB_eq, andB_eq, blt_eq_decide,
    beq_nat]

theorem uniqAll_of {NX NQ : Nat} {TX TQ : Nat → Nat} {z FZ F1 : Nat}
    (hX : ∀ i < NX, PP n w (TX i)) (hQ : ∀ i < NQ, PP n w (TQ i)) (hz : PP n w z)
    (hf : flagsK n w NX TX z FZ F1 = true) (hu : cntR (uqAt n w NX TX NQ TQ FZ z) 0 NX = 0) :
    (((List.range NX).map fun i => unpack n w (TX i)).all fun x =>
      inLN n ((List.range NQ).map fun i => unpack n w (TQ i)) x ||
        !(inZN n (unpack n w z) (mulN n x x)) ||
        goodQN n ((List.range NX).map fun i => unpack n w (TX i)) (unpack n w z) x) = true := by
  rw [List.all_map, List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have px := hX i hi'
  have h0 := cntR_zero hu i hi'
  unfold uqAt at h0
  rw [strictB_eq', andB_eq, andB_eq, notB_eq, notB_eq] at h0
  have hb : inZ n w z (pcomp n w (mask w) (TX i) (TX i)) = bitK FZ i := (flagsK_spec hf hi').1.symm
  simp only [Function.comp_apply]
  rw [inLN_eq px hQ, mulN_PP px px, inZN_PP hz (px.mul px), goodQN_eq hX hz px hf, hb]
  revert h0
  generalize bitK FZ i = a
  generalize HexaK.inL NQ TQ (TX i) = b
  generalize goodQK n w NX TX FZ z (TX i) = c
  cases a <;> cases b <;> cases c <;> simp

theorem uniqEN_of {NX NE NF : Nat} {TX TE TF : Nat → Nat} {z FZ F1 : Nat}
    (hX : ∀ i < NX, PP n w (TX i)) (hE : ∀ i < NE, PP n w (TE i)) (hF : ∀ i < NF, PP n w (TF i))
    (hf : flagsK n w NX TX z FZ F1 = true)
    (hue : allR (ueAt n w NX TX NE TE NF TF F1) 0 NX = true) :
    uniqEN n ((List.range NX).map fun i => unpack n w (TX i))
      ((List.range NE).map fun i => unpack n w (TE i))
      ((List.range NF).map fun i => unpack n w (TF i)) = true := by
  unfold uniqEN
  rw [List.all_map, List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have px := hX i hi'
  have h1 := allR_spec hue i hi'
  rw [Nat.zero_add] at h1
  unfold ueAt at h1
  rw [strictB_eq'] at h1
  have hb : Nat.beq (pcomp n w (mask w) (TX i) (TX i)) (pidn n w) = bitK F1 i :=
    (flagsK_spec hf hi').2.symm
  have hcnt : (((List.range NX).map fun i => unpack n w (TX i)).filter fun y =>
      eqA n (mulN n y y) (idA n) && commN n (unpack n w (TX i)) y).length =
      cntR (fun j => CFSG.KLie.CT.andB (bitK F1 j) (comm n w (TX i) (TX j))) 0 NX := by
    rw [cntR_eq, List.filter_map, List.length_map]
    congr 1
    refine List.filter_congr fun j hj => ?_
    have hj' := List.mem_range.1 hj
    have pj := hX j hj'
    simp only [Function.comp_apply]
    rw [mulN_PP pj pj, eqA_id_PP (pj.mul pj), commN_PP px pj, andB_eq, (flagsK_spec hf hj').2]
    rfl
  simp only [Function.comp_apply]
  rw [mulN_PP px px, eqA_id_PP (px.mul px), hb, eqA_id_PP px, inLN_eq px hE, inLN_eq px hF, hcnt]
  simp only [orB_eq, notB_eq, blt_eq_decide] at h1
  simpa only [Bool.or_assoc] using h1

@[expose] def sylCheck16G (gs gQ gE gF gU : List (Array Nat)) (z r s : Array Nat) : Bool :=
  let X := eltsN 16 gs
  let Q := eltsN 16 gQ
  let E := eltsN 16 gE
  let F := eltsN 16 gF
  let U := eltsN 16 gU
  enumCheckN 16 gs 1024 && enumCheckN 16 gQ 128 && enumCheckN 16 gE 64 &&
    enumCheckN 16 gF 64 && enumCheckN 16 gU 16 &&
    validA 16 z && validA 16 r && validA 16 s &&
    gQ.all (inLN 16 X) && gE.all (inLN 16 X) && gF.all (inLN 16 X) &&
    gU.all (inLN 16 Q) && inLN 16 Q z && inLN 16 X r && inLN 16 X s &&
    gs.all (fun g => gQ.all fun q => inLN 16 Q (conjA 16 g q)) &&
    gs.all (fun g => gE.all fun q => inLN 16 E (conjA 16 g q)) &&
    gs.all (fun g => gF.all fun q => inLN 16 F (conjA 16 g q)) &&
    eqA 16 (mulN 16 z z) (idA 16) && !(eqA 16 z (idA 16)) && gs.all (commN 16 z) &&
    X.all (fun x => !(gs.all (commN 16 x)) || inZN 16 z x) &&
    Q.all (fun x => inZN 16 z (mulN 16 x x)) &&
    Q.all (fun x => !(gQ.all (commN 16 x)) || inZN 16 z x) &&
    gQ.any (fun a => gQ.any fun b => !(commN 16 a b)) &&
    E.all (fun x => eqA 16 (mulN 16 x x) (idA 16)) &&
    gE.all (fun a => gE.all (commN 16 a)) &&
    F.all (fun x => eqA 16 (mulN 16 x x) (idA 16)) &&
    gF.all (fun a => gF.all (commN 16 a)) &&
    U.all (fun x => eqA 16 (mulN 16 x x) (idA 16)) &&
    gU.all (fun a => gU.all (commN 16 a)) &&
    gE.any (fun a => !(inLN 16 F a)) &&
    inLN 16 Q (powN 16 r 4) && inLN 16 Q (mulN 16 s s) &&
    inLN 16 Q (mulN 16 (mulN 16 s r) (mulN 16 s r)) &&
    !(inLN 16 Q r) && !(inLN 16 Q (powN 16 r 2)) && !(inLN 16 Q (powN 16 r 3)) &&
    !(inLN 16 Q s) && !(inLN 16 Q (mulN 16 s r)) && !(inLN 16 Q (mulN 16 s (powN 16 r 2))) &&
    !(inLN 16 Q (mulN 16 s (powN 16 r 3))) &&
    X.all (fun x => inLN 16 Q x || !(inZN 16 z (mulN 16 x x)) || goodQN 16 X z x) &&
    uniqEN 16 X E F

open CFSG.ComponentClassification.AS81.HeSylow in
theorem sylCheck16_eq : sylCheck16 =
    sylCheck16G heSyl16 heSylQ16 heSylE16 heSylF16 heSylEz16 heSylZ16 heSylR16 heSylS16 := rfl

theorem heSylK_sound {w : Nat} {gs gQ gE gF gU : List (Array Nat)}
    {cX cQ cE cF cU NX NQ NE NF NU : Nat}
    {GX GQ GE GF GU TX TQ TE TF TU EX EQ EE EF EU SX SQ SE SF SU : Nat → Nat}
    {z r s : Array Nat} {Pz Pr Ps FZ F1 : Nat}
    (pX : Pin 16 w gs cX GX NX TX EX SX) (pQ : Pin 16 w gQ cQ GQ NQ TQ EQ SQ)
    (pE : Pin 16 w gE cE GE NE TE EE SE) (pF : Pin 16 w gF cF GF NF TF EF SF)
    (pU : Pin 16 w gU cU GU NU TU EU SU)
    (hsz : NX = 1024 ∧ NQ = 128 ∧ NE = 64 ∧ NF = 64 ∧ NU = 16)
    (hz : z = unpack 16 w Pz) (hr : r = unpack 16 w Pr) (hs : s = unpack 16 w Ps)
    (hpz : permOK 16 w (mask w) (16 * w) Pz (pinvS 16 w (mask w) Pz) = true)
    (hpr : permOK 16 w (mask w) (16 * w) Pr (pinvS 16 w (mask w) Pr) = true)
    (hps : permOK 16 w (mask w) (16 * w) Ps (pinvS 16 w (mask w) Ps) = true)
    (hf : flagsK 16 w NX TX Pz FZ F1 = true)
    (hrest : restK16 16 w cX GX NX TX cQ GQ NQ TQ cE GE NE TE cF GF NF TF cU GU NU TU Pz Pr Ps =
      true)
    (huq : cntR (uqAt 16 w NX TX NQ TQ FZ Pz) 0 NX = 0)
    (hue : allR (ueAt 16 w NX TX NE TE NF TF F1) 0 NX = true) :
    sylCheck16G gs gQ gE gF gU z r s = true := by
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
  have hsz : szOK 16 w = true := (sX 0 (by omega)).sz
  have pz : PP 16 w Pz := PP_of_permOK hsz hpz
  have pr : PP 16 w Pr := PP_of_permOK hsz hpr
  have ps : PP 16 w Ps := PP_of_permOK hsz hps
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
  simp only [sylCheck16G]
  rw [eltsN_eq pX.size pX.bind pX.ok pX.fuel, eltsN_eq pQ.size pQ.bind pQ.ok pQ.fuel,
    eltsN_eq pE.size pE.bind pE.ok pE.fuel, eltsN_eq pF.size pF.bind pF.ok pF.fuel,
    eltsN_eq pU.size pU.bind pU.ok pU.fuel]
  unfold restK16 at hrest
  simp only [andB_eq, Bool.and_eq_true] at hrest
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31⟩ := hrest
  unfold elemAbK at g18 g19 g20
  simp only [andB_eq, Bool.and_eq_true] at g18 g19 g20
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨cX, cQ', cE', cF', cU', validA_unpack hpz, validA_unpack hpr, validA_unpack hps,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, uniqAll_of sX sQ pz hf huq,
    uniqEN_of sX sE sF hf hue⟩
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
    rw [gX, gE', List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, List.all_map]
    refine List.all_eq_true.2 fun q hq => ?_
    rw [List.mem_range] at hq
    rw [Function.comp_apply, conjA_PP (qX k hk) (qE q hq),
      inLN_eq ((qX k hk).conjK (qE q hq)) sE]
    exact allN_spec (allN_spec g9 k hk) q hq
  ·
    rw [gX, gF', List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, List.all_map]
    refine List.all_eq_true.2 fun q hq => ?_
    rw [List.mem_range] at hq
    rw [Function.comp_apply, conjA_PP (qX k hk) (qF q hq),
      inLN_eq ((qX k hk).conjK (qF q hq)) sF]
    exact allN_spec (allN_spec g10 k hk) q hq
  · rw [mulN_PP pz pz, eqA_id_PP (pz.mul pz)]
    exact g11
  · rw [eqA_id_PP pz, ← notB_eq]
    exact g12
  · rw [gX, all_map_congr (p := commN 16 (unpack 16 w Pz))
      fun k hk => commN_PP pz (qX k (List.mem_range.1 hk))]
    exact List.all_eq_true.2 fun k hk => allN_spec g13 k (List.mem_range.1 hk)
  ·
    rw [List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have pi := sX i hi'
    have h1 := allN_spec g14 i hi'
    rw [strictB_eq', orB_eq, notB_eq, allN_eq'] at h1
    rw [Function.comp_apply, gX, all_map_congr (p := commN 16 (unpack 16 w (TX i)))
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
    rw [Function.comp_apply, gQ', all_map_congr (p := commN 16 (unpack 16 w (TQ i)))
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
  · rw [powN_PP pr 4, inLN_eq (pw_PP pr 4) sQ]
    exact g22
  · rw [mulN_PP ps ps, inLN_eq (ps.mul ps) sQ]
    exact g23
  · rw [mulN_PP ps pr, mulN_PP (ps.mul pr) (ps.mul pr), inLN_eq ((ps.mul pr).mul (ps.mul pr)) sQ]
    rw [strictN_eq'] at g24
    exact g24
  · rw [inLN_eq pr sQ, ← notB_eq]
    exact g25
  · rw [powN_PP pr 2, inLN_eq (pw_PP pr 2) sQ, ← notB_eq]
    exact g26
  · rw [powN_PP pr 3, inLN_eq (pw_PP pr 3) sQ, ← notB_eq]
    exact g27
  · rw [inLN_eq ps sQ, ← notB_eq]
    exact g28
  · rw [mulN_PP ps pr, inLN_eq (ps.mul pr) sQ, ← notB_eq]
    exact g29
  · rw [powN_PP pr 2, mulN_PP ps (pw_PP pr 2), inLN_eq (ps.mul (pw_PP pr 2)) sQ, ← notB_eq]
    exact g30
  · rw [powN_PP pr 3, mulN_PP ps (pw_PP pr 3), inLN_eq (ps.mul (pw_PP pr 3)) sQ, ← notB_eq]
    exact g31

end CFSG.KC.HeAutK

end
