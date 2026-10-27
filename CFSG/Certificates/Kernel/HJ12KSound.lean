module

public import Certificates.Data.Kernel.HJ12K
public import CFSG.Certificates.Kernel.Mat12PSound
public import CFSG.Certificates.Kernel.GammaUListSound
public import CFSG.Certificates.Kernel.LceSP.Popcount
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LceSP.Base
public import Certificates.Data.Kernel.LceSTab

public section

namespace Certificates.Kernel.HJ12K

open CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.Quasithin.H13.MatNCert CFSG.GammaU.Native
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

theorem nat_beq (a b : ℕ) : (a == b) = Nat.beq a b :=
  Bool.eq_iff_iff.2 (by rw [beq_iff_eq, Nat.beq_eq])

theorem nat_ble (a b : ℕ) : decide (a ≤ b) = Nat.ble a b :=
  Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff, Nat.ble_eq])

theorem unpackA_toList (X : ℕ) : (unpackA X).toList = unpackQ X := rfl

theorem unpackQ_length (X : ℕ) : (unpackQ X).length = 12 := rfl

theorem unpackQ_lt4096 (X : ℕ) : ∀ c ∈ unpackQ X, c < 4096 := fun c hc => unpackQ_lt X c hc

theorem appL_eq_mvNR : ∀ (l : List ℕ) (n : ℕ), GammaUList.appL l n = mvNR l n
  | [], _ => rfl
  | r :: l, n => by
    change Nat.xor (Nat.mul (Nat.mod n 2) r) (GammaUList.appL l (Nat.div n 2)) =
      Nat.xor (Nat.mul r (Nat.land n 1)) (mvNR l (Nat.shiftRight n 1))
    have h1 : Nat.mul (Nat.mod n 2) r = Nat.mul r (Nat.land n 1) := by
      change n % 2 * r = r * (n &&& 1)
      rw [Nat.and_one_is_mod, Nat.mul_comm]
    have h2 : Nat.shiftRight n 1 = Nat.div n 2 := by
      change n >>> 1 = n / 2
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    rw [h1, h2, appL_eq_mvNR l]

theorem appN_unpackA (X n : ℕ) : appN (unpackA X) n = mvNR (unpackQ X) n := by
  rw [GammaUList.appN_eq (g := unpackA X) (unpackQ_length X) (unpackQ_lt4096 X) n, unpackA_toList,
    appL_eq_mvNR]

theorem mulR_unpackA (X Y : ℕ) : mulR (unpackA X) (unpackA Y) = unpackA (mulQ X Y) := by
  rw [mulR, unpackA, unpackA, unpackA, ← mulN_unpackQ, List.map_toArray]
  congr 1
  rw [mulN]
  refine List.map_congr_left fun n _ => ?_
  rw [← unpackA, appN_unpackA, mvNR_eq]

theorem beq_unpackA {X Y : ℕ} (hX : X < 2 ^ 144) (hY : Y < 2 ^ 144) :
    (unpackA X == unpackA Y) = (X == Y) := by
  rw [GammaUList.beq_toList, unpackA_toList, unpackA_toList, unpackQ_beq hX hY]

theorem unpackA_inj {X Y : ℕ} (hX : X < 2 ^ 144) (hY : Y < 2 ^ 144) (h : unpackA X = unpackA Y) :
    X = Y :=
  unpackQ_inj hX hY (by rw [← unpackA_toList, h, unpackA_toList])

theorem idR_eq : idR = unpackA oneQ := by decide

theorem hjAc_eq : hjAc = unpackA acQ := by decide

theorem hjBc_eq : hjBc = unpackA bcQ := by decide

theorem hjJc_eq : hjJc = unpackA jcQ := by decide

theorem jcQ_lt : jcQ < 2 ^ 144 := by decide

theorem okRows_unpackA (X : ℕ) : okRows (unpackA X) = true := by
  rw [okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨rfl, fun i hi => decide_eq_true ?_⟩
  exact unpackQ_lt4096 X _ (List.getElem_mem (by simpa [unpackA] using hi))

theorem wordStep_eq (X l : ℕ) :
    mulR (unpackA X) (if l = 0 then hjAc else hjBc) = unpackA (mulQ X (if l = 0 then acQ else bcQ)) := by
  split_ifs
  · rw [hjAc_eq, mulR_unpackA]
  · rw [hjBc_eq, mulR_unpackA]

theorem wordR_foldl : ∀ (w : List ℕ) (X : ℕ),
    w.foldl (fun acc l => mulR acc (if l = 0 then hjAc else hjBc)) (unpackA X) =
      unpackA (w.foldl (fun acc l => mulQ acc (if l = 0 then acQ else bcQ)) X)
  | [], _ => rfl
  | l :: w, X => by
    rw [List.foldl_cons, List.foldl_cons, wordStep_eq, wordR_foldl w]

theorem wordR_eq (w : List ℕ) : wordR w = unpackA (wordQ w) := by
  rw [wordR, wordQ, idR_eq, wordR_foldl]

theorem wordQ_lt (w : List ℕ) : wordQ w < 2 ^ 144 := by
  rw [wordQ]
  suffices h : ∀ X, X < 2 ^ 144 →
      w.foldl (fun acc l => mulQ acc (if l = 0 then acQ else bcQ)) X < 2 ^ 144 from h _ oneQ_lt
  induction w with
  | nil => exact fun X hX => hX
  | cons l w ih => exact fun X _ => ih _ (mulQ_lt _ _)

theorem words_eq (ws : List (List ℕ)) : ws.map wordR = (ws.map wordQ).map unpackA := by
  rw [List.map_map]
  exact List.map_congr_left fun w _ => wordR_eq w

theorem words_lt (ws : List (List ℕ)) : ∀ g ∈ ws.map wordQ, g < 2 ^ 144 := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordQ_lt w

@[expose] def laneOK : Bool :=
  (List.range 12).all fun j => (List.range 4096).all fun v => (lane j).testBit v == v.testBit j

set_option maxRecDepth 100000 in
theorem laneOK_eq : laneOK = true := by quickRfl

theorem lane_testBit (j : ℕ) (hj : j < 12) (v : ℕ) (hv : v < 4096) :
    (lane j).testBit v = v.testBit j := by
  have h := laneOK_eq
  rw [laneOK, List.all_eq_true] at h
  have h2 := h j (List.mem_range.2 hj)
  rw [List.all_eq_true] at h2
  exact beq_iff_eq.1 (h2 v (List.mem_range.2 hv))

theorem testBit_laneMask : ∀ (A : List ℕ) (j i v : ℕ), v < 4096 → j + A.length ≤ 12 →
    (laneMask A j i).testBit v = (mvN A (v >>> j)).testBit i
  | [], j, i, v, _, _ => by simp [laneMask, mvN]
  | c :: A, j, i, v, hv, hl => by
    rw [List.length_cons] at hl
    rw [laneMask, mvN, Nat.testBit_xor, Nat.testBit_xor, ← Nat.shiftRight_succ,
      testBit_laneMask A (j + 1) i v hv (by omega), testBit_iteQ, testBit_iteQ,
      lane_testBit j (by omega) v hv, Nat.testBit_shiftRight, Bool.and_comm]
    simp only [Nat.add_zero]

theorem foldl_and_testBit (f : ℕ → ℕ) (v : ℕ) : ∀ (l : List ℕ) (m : ℕ),
    (l.foldl (fun m i => m &&& f i) m).testBit v = (m.testBit v && l.all fun i => (f i).testBit v)
  | [], m => by simp
  | i :: l, m => by
    rw [List.foldl_cons, foldl_and_testBit f v l, Nat.testBit_and, List.all_cons, Bool.and_assoc]

theorem fullM_testBit {v : ℕ} (hv : v < 4096) : fullM.testBit v = true := by
  rw [fullM, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  exact hv

theorem fixMask_testBit (X : ℕ) {v : ℕ} (hv : v < 4096) :
    (fixMask (unpackQ X)).testBit v = Nat.beq (mvNR (unpackQ X) v) v := by
  rw [fixMask, foldl_and_testBit, fullM_testBit hv, Bool.true_and, mvNR_eq, Bool.eq_iff_iff,
    Nat.beq_eq, List.all_eq_true]
  have hlt : mvN (unpackQ X) v < 2 ^ 12 := mvN_lt _ _ (unpackQ_lt X)
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 12
    · have := h i (List.mem_range.2 hi)
      rw [Nat.testBit_xor, fullM_testBit hv, Nat.testBit_xor,
        testBit_laneMask _ 0 i v hv (by rw [unpackQ_length]), Nat.shiftRight_zero,
        lane_testBit i hi v hv] at this
      revert this
      cases (mvN (unpackQ X) v).testBit i <;> cases v.testBit i <;> simp
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num [hv] : v < 2 ^ 12)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro h i hi
    have hi' := List.mem_range.1 hi
    rw [Nat.testBit_xor, fullM_testBit hv, Nat.testBit_xor,
      testBit_laneMask _ 0 i v hv (by rw [unpackQ_length]), Nat.shiftRight_zero,
      lane_testBit i hi' v hv, h]
    simp

theorem fixCodes_unpackA (X : ℕ) : fixCodes (unpackA X) = fixQ X := by
  rw [fixCodes, fixQ, bitsM]
  refine List.filter_congr fun v hv => ?_
  rw [appN_unpackA, nat_beq, fixMask_testBit X (List.mem_range.1 hv)]

theorem length_filter_range (p : ℕ → Bool) : ∀ n,
    ((List.range n).filter p).length = ∑ j ∈ Finset.range n, if p j = true then 1 else 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range p n,
      Finset.sum_range_succ]
    cases h : p n <;> simp [h]

theorem bitsM_length (M : ℕ) : (bitsM M).length = CFSG.KC.pc4096 M := by
  rw [bitsM, length_filter_range, CFSG.Certificates.LceP.pc4096_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (M / 2 ^ j) with h | h <;> simp [h]

theorem fixCodes_length (X : ℕ) : (fixCodes (unpackA X)).length = fixCnt X := by
  rw [fixCodes_unpackA, fixQ, bitsM_length, fixCnt]

@[expose] def SeenRel (h : Std.HashSet (Array ℕ)) (t : NT ℕ) : Prop :=
  ∀ q, q < 2 ^ 144 → h.contains (unpackA q) = memP t q

@[expose] def stepM (acc : List (Array ℕ) × Std.HashSet (Array ℕ)) (t : Array ℕ) :
    List (Array ℕ) × Std.HashSet (Array ℕ) :=
  match acc with
  | (l, h) => if h.contains ((fun x : Array ℕ => x) t) then (l, h)
    else (t :: l, h.insert ((fun x : Array ℕ => x) t))

@[expose] def stepP (acc : List ℕ × NT ℕ) (t : ℕ) : List ℕ × NT ℕ :=
  if memP acc.2 t then acc else (t :: acc.1, insP acc.2 t)

theorem foldl_step : ∀ (L : List ℕ), (∀ t ∈ L, t < 2 ^ 144) →
    ∀ (l : List ℕ) (h : Std.HashSet (Array ℕ)) (t : NT ℕ), (∀ q ∈ l, q < 2 ^ 144) →
      SeenRel h t →
      ((L.map unpackA).foldl stepM (l.map unpackA, h)).1 = (L.foldl stepP (l, t)).1.map unpackA ∧
      SeenRel ((L.map unpackA).foldl stepM (l.map unpackA, h)).2 (L.foldl stepP (l, t)).2 ∧
      ∀ q ∈ (L.foldl stepP (l, t)).1, q < 2 ^ 144
  | [], _, l, h, t, hl, hr => ⟨rfl, hr, hl⟩
  | x :: L, hL, l, h, t, hl, hr => by
    have hx : x < 2 ^ 144 := hL x List.mem_cons_self
    have hL' : ∀ t ∈ L, t < 2 ^ 144 := fun t ht => hL t (List.mem_cons_of_mem x ht)
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hc : h.contains (unpackA x) = memP t x := hr x hx
    by_cases hm : memP t x = true
    · have e1 : stepM (l.map unpackA, h) (unpackA x) = (l.map unpackA, h) := by
        simp only [stepM, hc, hm, if_true]
      have e2 : stepP (l, t) x = (l, t) := by simp only [stepP, hm, if_true]
      rw [e1, e2]
      exact foldl_step L hL' l h t hl hr
    · have hm' : memP t x = false := by simpa using hm
      have e1 : stepM (l.map unpackA, h) (unpackA x) =
          ((x :: l).map unpackA, h.insert (unpackA x)) := by
        simp only [stepM, hc, hm', Bool.false_eq_true, if_false, List.map_cons]
      have e2 : stepP (l, t) x = (x :: l, insP t x) := by
        simp only [stepP, hm', Bool.false_eq_true, if_false]
      rw [e1, e2]
      refine foldl_step L hL' (x :: l) _ _ ?_ ?_
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hx
        · exact hl q hq
      · intro q hq
        rw [Std.HashSet.contains_insert, memP_insP, beq_unpackA hx hq, hr q hq]

theorem flat_eq (gs fr : List ℕ) :
    (fr.map unpackA).flatMap (fun s => ((gs.map unpackA).map fun g x => mulR x g).map fun f => f s) =
      (fr.flatMap fun s => gs.map fun g => mulQ s g).map unpackA := by
  induction fr with
  | nil => rfl
  | cons s fr ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih, List.map_append]
    congr 1
    rw [List.map_map, List.map_map, List.map_map]
    exact List.map_congr_left fun g _ => mulR_unpackA s g

theorem flat_lt (gs fr : List ℕ) : ∀ t ∈ fr.flatMap (fun s => gs.map fun g => mulQ s g), t < 2 ^ 144 := by
  intro t ht
  obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 ht
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hs
  exact mulQ_lt s g

theorem bfsRound_eq (gs fr : List ℕ) (h : Std.HashSet (Array ℕ)) (t : NT ℕ) (hr : SeenRel h t) :
    (bfsRound (fun x : Array ℕ => x) ((gs.map unpackA).map fun g x => mulR x g) (fr.map unpackA) h).1 =
        (roundQ gs fr t).1.map unpackA ∧
      SeenRel (bfsRound (fun x : Array ℕ => x) ((gs.map unpackA).map fun g x => mulR x g)
        (fr.map unpackA) h).2 (roundQ gs fr t).2 ∧
      ∀ q ∈ (roundQ gs fr t).1, q < 2 ^ 144 := by
  have e1 : bfsRound (fun x : Array ℕ => x) ((gs.map unpackA).map fun g x => mulR x g)
      (fr.map unpackA) h =
      (((fr.flatMap fun s => gs.map fun g => mulQ s g).map unpackA).foldl stepM
        (([] : List ℕ).map unpackA, h)) := by
    rw [bfsRound, flat_eq]
    rfl
  have e2 : roundQ gs fr t = (fr.flatMap fun s => gs.map fun g => mulQ s g).foldl stepP ([], t) :=
    rfl
  rw [e1, e2]
  exact foldl_step _ (flat_lt gs fr) [] h t (by simp) hr

theorem bfsClosure_eq (gs : List ℕ) : ∀ (fuel : ℕ) (fr vis : List ℕ) (h : Std.HashSet (Array ℕ))
    (t : NT ℕ), (∀ q ∈ fr, q < 2 ^ 144) → (∀ q ∈ vis, q < 2 ^ 144) → SeenRel h t →
    bfsClosure (fun x : Array ℕ => x) ((gs.map unpackA).map fun g x => mulR x g) fuel
        (fr.map unpackA) h (vis.map unpackA) = (closQ gs fuel fr t vis).map unpackA ∧
      ∀ q ∈ closQ gs fuel fr t vis, q < 2 ^ 144
  | 0, fr, vis, h, t, hfr, hvis, _ => by
    refine ⟨by rw [bfsClosure, closQ, List.map_append], fun q hq => ?_⟩
    rw [closQ] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hfr q hq
    · exact hvis q hq
  | fuel + 1, fr, vis, h, t, hfr, hvis, hr => by
    obtain ⟨r1, r2, r3⟩ := bfsRound_eq gs fr h t hr
    have hfv : ∀ q ∈ fr ++ vis, q < 2 ^ 144 := fun q hq => by
      rcases List.mem_append.1 hq with hq | hq
      · exact hfr q hq
      · exact hvis q hq
    rw [bfsClosure, closQ, r1, List.isEmpty_map]
    split_ifs with he
    · exact ⟨by rw [List.map_append], hfv⟩
    · rw [← List.map_append]
      exact bfsClosure_eq gs fuel _ _ _ _ r3 hfv r2

theorem enumGrp_eq (gs : List ℕ) :
    enumGrp (gs.map unpackA) = (enumQ gs).map unpackA ∧ ∀ q ∈ enumQ gs, q < 2 ^ 144 := by
  rw [enumGrp, enumQ, idR_eq]
  refine bfsClosure_eq gs 100000 [oneQ] [] _ _ (by simpa using oneQ_lt) (by simp) ?_
  intro q hq
  rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty,
    beq_unpackA oneQ_lt hq]

theorem contains_map {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 144) {y : ℕ} (hy : y < 2 ^ 144) :
    (L.map unpackA).contains (unpackA y) = L.contains y := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [← unpackA_inj (hL x hx) hy e]
  · exact fun h => ⟨y, h, rfl⟩

theorem closedCheck_eq (gs X : List ℕ) (hX : ∀ q ∈ X, q < 2 ^ 144) :
    closedCheck (gs.map unpackA) (X.map unpackA) = closedQ gs X := by
  change (X.map unpackA).all (fun x => (gs.map unpackA).all fun g =>
      (Std.HashSet.ofList (X.map unpackA)).contains (mulR x g)) =
    X.all fun x => gs.all fun g => memP (ofListP X) (mulQ x g)
  rw [List.all_map]
  refine congrArg X.all (funext fun x => ?_)
  rw [Function.comp_apply, List.all_map]
  refine congrArg gs.all (funext fun g => ?_)
  rw [Function.comp_apply, Std.HashSet.contains_ofList, mulR_unpackA, contains_map hX (mulQ_lt x g),
    memP_ofListP]

theorem dedup_length {X : List ℕ} (hX : ∀ q ∈ X, q < 2 ^ 144) (h : nodupP X = true) :
    (X.map unpackA).dedup.length = X.length := by
  have hn : (X.map unpackA).Nodup :=
    List.Nodup.map_on (fun x hx y hy e => unpackA_inj (hX x hx) (hX y hy) e) ((nodupP_iff X).1 h)
  rw [List.dedup_eq_self.2 hn, List.length_map]

theorem mulL_unpackQ (X Y : ℕ) :
    GammaUList.mulL (unpackQ X) (unpackQ Y) = unpackQ (mulQ X Y) := by
  rw [← unpackA_toList, ← unpackA_toList, ← GammaUList.mulR_toList (g := unpackA X)
    (unpackQ_length X) (unpackQ_lt4096 X), mulR_unpackA, unpackA_toList]

theorem invR_unpackA {g r : ℕ} (h : invOKQ g r = true) : invR (unpackA g) = unpackA r := by
  rw [invOKQ, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  have hok : GammaUList.invOK (unpackQ g) (unpackQ r) = true := by
    have hb : ∀ X, ((unpackQ X).all fun c => decide (c < 4096)) = true := fun X =>
      List.all_eq_true.2 fun c hc => decide_eq_true (unpackQ_lt4096 X c hc)
    simp only [GammaUList.invOK, unpackQ_length, hb, mulL_unpackQ, h.1, h.2, Bool.and_true,
      Bool.true_and, beq_self_eq_true]
    rw [oneQ_eq]
    rfl
  exact GammaUList.invR_eq hok

theorem gensOKN_of (gs : List ℕ) (h : gensOKQ gs = true) : gensOKN (gs.map unpackA) = true := by
  rw [gensOKQ, List.all_eq_true] at h
  rw [gensOKN, List.all_eq_true]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
  have hi := h g hg
  rw [invR_unpackA hi, okRows_unpackA, okRows_unpackA, mulR_unpackA, mulR_unpackA, idR_eq,
    beq_unpackA (mulQ_lt _ _) oneQ_lt, beq_unpackA (mulQ_lt _ _) oneQ_lt]
  rw [invOKQ, Bool.and_eq_true] at hi
  rw [nat_beq, nat_beq, hi.1, hi.2]
  rfl

theorem x7_sound {x : ℕ} (hx : x < 2 ^ 144) (h : x7Core x = true) :
    (mulR (mulR (mulR (unpackA x) (unpackA x)) (mulR (unpackA x) (unpackA x)))
        (mulR (mulR (unpackA x) (unpackA x)) (unpackA x)) == idR &&
      unpackA x != idR && fixCodes (unpackA x) == [0]) = true := by
  rw [x7Core] at h
  simp only [mulR_unpackA, idR_eq, fixCodes_unpackA, bne, beq_unpackA (mulQ_lt _ _) oneQ_lt,
    beq_unpackA hx oneQ_lt, nat_beq]
  exact h

theorem hjX7Check_of (h : x7Q = true) : hjX7Check = true := by
  have := x7_sound (wordQ_lt hj_x7Word) h
  rw [← wordR_eq] at this
  exact this

theorem p3_sound (gs : List ℕ) (hgs : ∀ g ∈ gs, g < 2 ^ 144) (J : ℕ) (hJ : J < 2 ^ 144)
    (h : p3At gs (enumQ gs) J 27 = true) :
    (gensOKN (gs.map unpackA) && closedCheck (gs.map unpackA) (enumGrp (gs.map unpackA)) &&
      (enumGrp (gs.map unpackA)).dedup.length == 27 &&
      mulR (mulR (unpackA J) (unpackA J)) (unpackA J) == idR &&
      [idR, unpackA J, mulR (unpackA J) (unpackA J)].all fun c =>
        (enumGrp (gs.map unpackA)).all fun p =>
          mulR c p == idR || decide ((fixCodes (mulR c p)).length ≤ 256)) = true := by
  obtain ⟨hE, hEv⟩ := enumGrp_eq gs
  rw [p3At] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨gensOKN_of gs h1, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hE, closedCheck_eq gs _ hEv]
    exact h2
  · rw [hE, dedup_length hEv h3, nat_beq]
    exact h4
  · rw [mulR_unpackA, mulR_unpackA, idR_eq, beq_unpackA (mulQ_lt _ _) oneQ_lt, nat_beq]
    exact h5
  · rw [hE, mulR_unpackA, idR_eq]
    rw [List.all_eq_true] at h6 ⊢
    intro c hc
    have hc' : c ∈ [oneQ, J, mulQ J J].map unpackA := by simpa using hc
    obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
    have := h6 c' hc''
    rw [List.all_eq_true] at this ⊢
    intro p hp
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
    rw [mulR_unpackA, beq_unpackA (mulQ_lt _ _) oneQ_lt, fixCodes_length, nat_beq, nat_ble]
    exact this p' hp'

theorem hjP3Check_of (h : p3Q = true) : hjP3Check = true := by
  have := p3_sound _ (words_lt hj_p3Words) jcQ jcQ_lt h
  rw [← words_eq, ← hjJc_eq] at this
  exact this

end Certificates.Kernel.HJ12K

end
