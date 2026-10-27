module

public import CFSG.Certificates.Kernel.M3BFib.Fib0Sound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBElem
public import Certificates.Data.Kernel.M3BFib.RootClaim

public section

namespace CFSG.KC.M3BF

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open Timmesfeld.M3B (B0 nfD eOf AD aget ebasis cubeE zconjE adPow adOne zeroV repD tD)

@[expose] noncomputable def toEK (x : EK) : Elt 12 := (vz x.1, ((x.2 : ℕ) : ZMod 3))

theorem toEK_eq (a b : ℕ) : toEK (a, b) = (vz a, ((b : ℕ) : ZMod 3)) := rfl

theorem rc_cast_mod (m : ℕ) : ((Nat.mod m 3 : ℕ) : ZMod 3) = (m : ZMod 3) := cast_mod3 m

theorem rc_cast_inj {a b : ℕ} (ha : a < 3) (hb : b < 3) (h : (a : ZMod 3) = (b : ZMod 3)) :
    a = b := by
  have e := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e

theorem betaK_cast (a b : ℕ) : ((betaK a b : ℕ) : ZMod 3) = betaC 12 (toMat (B0 ())) (vz a) (vz b) := by
  obtain ⟨hL1, hL2, hL3⟩ := lpM_ok
  rw [betaK, dot_eq 12 _ _ (dig_length _) (dig3_length _)]
  push_cast
  simp only [lane_vm _ _ (dig3_length _) (dig3_lt _) hL1 hL2, vz_dig3, hL3, betaC, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem emulK_eq (a e b f : ℕ) : emulK (a, e) (b, f) =
    (enc (List.zipWith (fun a b => Nat.mod (Nat.add a b) 3) (dig3 a) (dig3 b)),
      Nat.mod (Nat.add (Nat.add e f) (betaK a b)) 3) := rfl

theorem vz_zip (a b : ℕ) :
    GoodRow (enc (List.zipWith (fun a b => Nat.mod (Nat.add a b) 3) (dig3 a) (dig3 b))) ∧
      vz (enc (List.zipWith (fun a b => Nat.mod (Nat.add a b) 3) (dig3 a) (dig3 b))) = vz a + vz b := by
  have hl : (List.zipWith (fun a b => Nat.mod (Nat.add a b) 3) (dig3 a) (dig3 b)).length = 12 := by
    rw [List.length_zipWith, dig3_length, dig3_length, min_self]
  have h3 : ∀ d ∈ List.zipWith (fun a b => Nat.mod (Nat.add a b) 3) (dig3 a) (dig3 b), d < 3 := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    rw [List.getElem_zipWith]
    exact Nat.mod_lt _ (by norm_num)
  refine ⟨goodRow_enc hl h3, funext fun k => ?_⟩
  rw [vz_enc hl h3, getD_zipWith _ _ _ _ (by rw [dig3_length]; exact k.isLt)
    (by rw [dig3_length]; exact k.isLt), rc_cast_mod, Nat.add_eq, Pi.add_apply]
  push_cast
  rfl

theorem goodRow_emulK (x y : EK) : GoodRow (emulK x y).1 := by
  obtain ⟨a, e⟩ := x
  obtain ⟨b, f⟩ := y
  rw [emulK_eq]
  dsimp only
  exact (vz_zip a b).1

theorem goodRow_sqK (x : EK) : GoodRow (sqK x).1 := by
  rw [sqK]
  exact goodRow_emulK _ _

theorem emulK_sound (x y : EK) : toEK (emulK x y) = emul (toMat (B0 ())) (toEK x) (toEK y) := by
  obtain ⟨a, e⟩ := x
  obtain ⟨b, f⟩ := y
  rw [emulK_eq, toEK_eq, toEK_eq, toEK_eq, emul_eq, (vz_zip a b).2, rc_cast_mod, Nat.add_eq,
    Nat.add_eq]
  push_cast
  rw [betaK_cast]

theorem toEK_zero : toEK (0, 0) = eone := by
  rw [toEK_eq, vz_zero, Nat.cast_zero]
  rfl

theorem sqK_sound (x : EK) : toEK (sqK x) = epow (toMat (B0 ())) (toEK x) 2 := by
  rw [sqK, emulK_sound, emulK_sound, toEK_zero]
  rfl

theorem substP_eq (T : PD) (a e : ℕ) : substP T (a, e) =
    ((compK LpM (a :: List.replicate 11 0, e :: List.replicate 11 0, 1) T).1.headD 0,
      (compK LpM (a :: List.replicate 11 0, e :: List.replicate 11 0, 1) T).2.1.headD 0) := rfl

theorem substP_sound {T : PD} (hT : GoodPD T) {x : EK} (hx : GoodRow x.1) :
    GoodRow (substP T x).1 ∧ toEK (substP T x) = subst (toMat (B0 ())) (dK T) (toEK x) := by
  obtain ⟨a, e⟩ := x
  have hXg : GoodPD (a :: List.replicate 11 0, e :: List.replicate 11 0, 1) := by
    refine ⟨rfl, fun r hr => ?_, rfl⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hx
    · rw [List.eq_of_mem_replicate hr]
      exact goodRow_zero
  have hrow : (dK (a :: List.replicate 11 0, e :: List.replicate 11 0, 1)).1 0 = toEK (a, e) := by
    simp only [dK, toEK, Fin.val_zero, List.getD_cons_zero]
  obtain ⟨hPg, hPd⟩ := compK_sound lpM_ok hXg hT
  have e0 : (dK (compK LpM (a :: List.replicate 11 0, e :: List.replicate 11 0, 1) T)).1 0 =
      subst (toMat (B0 ())) (dK T) ((dK (a :: List.replicate 11 0, e :: List.replicate 11 0, 1)).1 0) := by
    rw [hPd]
    simp only [comp]
  rw [hrow] at e0
  rw [substP_eq, toEK_eq, ← e0]
  generalize compK LpM (a :: List.replicate 11 0, e :: List.replicate 11 0, 1) T = P at hPg ⊢
  refine ⟨?_, ?_⟩
  · rw [headD_eq_getD]
    exact hPg.2.1 _ (getD_mem (by rw [hPg.1]; norm_num))
  · rw [headD_eq_getD, headD_eq_getD]
    simp only [dK, Fin.val_zero]

theorem vz_pow64 (i : Fin 12) : vz (Nat.pow 64 i) = Pi.single i 1 := by
  have h : ∀ i j : Fin 12, vz (Nat.pow 64 i) j = (Pi.single i 1 : Fin 12 → ZMod 3) j := by
    decide +kernel
  exact funext (h i)

theorem getD_range_map {α : Type} (f : ℕ → α) (d : α) (i : Fin 12) :
    ((List.range 12).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

theorem eP_eq (v : List ℕ) : eP v = (enc (padV v), 0) := rfl

theorem rc_toE_eOf (v : List ℕ) :
    toE (eOf v 0) = ((fun i : Fin 12 => ((v.getD i.val 0 : ℕ) : ZMod 3)), 0) := by
  unfold toE eOf
  rw [vfun_vofFn]
  refine Prod.ext (funext fun i => ?_) rfl
  change HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.toZ (Fin.ofNat 3 (v.getD i.val 0)) =
    ((v.getD i.val 0 : ℕ) : ZMod 3)
  apply ZMod.val_injective
  rw [toZ_val, Fin.val_ofNat, ZMod.val_natCast]

theorem eP_sound {v : List ℕ} (h : vOKB v = true) : GoodRow (eP v).1 ∧ toEK (eP v) = toE (eOf v 0) := by
  have hl : (padV v).length = 12 := by simp [padV]
  have h3 : ∀ d ∈ padV v, d < 3 := by
    simp only [vOKB, List.all_eq_true, Nat.blt_eq] at h
    exact h
  rw [eP_eq, toEK_eq, rc_toE_eOf]
  dsimp only
  refine ⟨goodRow_enc hl h3, Prod.ext (funext fun k => ?_) Nat.cast_zero⟩
  dsimp only
  rw [vz_enc hl h3 k, padV, getD_range_map]

theorem nfL_eq (v : List ℕ) : nfL v = ((nfRows (eP v)).map Prod.fst, (nfRows (eP v)).map Prod.snd, 1) :=
  rfl

theorem nfRows_getD (x : EK) (i : Fin 12) :
    (nfRows x).getD i (0, 0) = emulK (emulK (sqK x) (Nat.pow 64 i, 0)) x := by
  rw [nfRows, getD_range_map]

theorem nfRows_length (x : EK) : (nfRows x).length = 12 := by
  simp [nfRows]

theorem nfL_sound {v : List ℕ} (h : vOKB v = true) :
    GoodPD (nfL v) ∧ dK (nfL v) = toD (nfD (B0 ()) (eOf v 0)) := by
  obtain ⟨hxg, hx⟩ := eP_sound h
  have hrow : ∀ i : Fin 12, (dK (nfL v)).1 i = toEK (emulK (emulK (sqK (eP v)) (Nat.pow 64 i, 0)) (eP v)) := by
    intro i
    have hi : (i : ℕ) < (nfRows (eP v)).length := by rw [nfRows_length]; exact i.isLt
    rw [nfL_eq]
    simp only [dK]
    rw [getD_map_lt (d := (0, 0)) hi, getD_map_lt (d := (0, 0)) hi, nfRows_getD]
    rfl
  have hlam : (dK (nfL v)).2 = ((1 : ℕ) : ZMod 3) := by
    rw [nfL_eq, dK]
  have hlam' : (toD (nfD (B0 ()) (eOf v 0))).2 = 1 := by
    rw [toD, nfD]
    rfl
  refine ⟨?_, Prod.ext (funext fun i => ?_) ?_⟩
  · rw [nfL_eq]
    refine ⟨by simp [nfRows_length], fun r hr => ?_, by simp [nfRows_length]⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    rw [nfRows, List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact goodRow_emulK _ _
  · rw [hrow]
    change _ = toE (aget (nfD (B0 ()) (eOf v 0)) i)
    unfold nfD aget
    rw [ofFn_get!, toE_emul, toE_emul, toE_epow, toE_ebasis, emulK_sound, emulK_sound, sqK_sound,
      hx, toEK_eq, vz_pow64, Nat.cast_zero]
  · rw [hlam, hlam', Nat.cast_one]

theorem goodRow_ext {r r' : ℕ} (h : GoodRow r) (h' : GoodRow r') (e : vz r = vz r') : r = r' := by
  have hd : dig3 r = dig3 r' := by
    refine List.ext_getElem (by rw [dig3_length, dig3_length]) fun k hk hk' => ?_
    have hk12 : k < 12 := by rwa [dig3_length] at hk
    have ek := congrFun e ⟨k, hk12⟩
    change (((dig3 r).getD k 0 : ℕ) : ZMod 3) = (((dig3 r').getD k 0 : ℕ) : ZMod 3) at ek
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] at ek
    exact rc_cast_inj (dig3_lt r _ (List.getElem_mem hk)) (dig3_lt r' _ (List.getElem_mem hk')) ek
  calc r = enc (dig3 r) := h.symm
    _ = enc (dig3 r') := by rw [hd]
    _ = r' := h'

@[expose] noncomputable def redB (D : PD) : Bool :=
  D.2.1.all (fun c => Nat.blt c 3) && Nat.blt D.2.2 3

theorem redB_spec {D : PD} (h : redB D = true) : (∀ c ∈ D.2.1, c < 3) ∧ D.2.2 < 3 := by
  simp only [redB, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  exact h

theorem redB_of {D : PD} (h1 : ∀ c ∈ D.2.1, c < 3) (h2 : D.2.2 < 3) : redB D = true := by
  simp only [redB, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq]
  exact ⟨h1, h2⟩

theorem redB_compK (Lp : List ℕ) (D D' : PD) : redB (compK Lp D D') = true := by
  refine redB_of (fun c hc => ?_) ?_
  · unfold compK at hc
    dsimp only at hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    rw [List.getElem_zipWith]
    exact Nat.mod_lt _ (by norm_num)
  · unfold compK
    dsimp only
    exact Nat.mod_lt _ (by norm_num)

theorem redB_nfL (v : List ℕ) : redB (nfL v) = true := by
  rw [nfL_eq]
  refine redB_of (fun c hc => ?_) (by norm_num)
  dsimp only at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  rw [nfRows, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  generalize emulK (sqK (eP v)) (Nat.pow 64 i, 0) = p
  generalize eP v = q
  obtain ⟨a, e⟩ := p
  obtain ⟨b, f⟩ := q
  rw [emulK_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem redB_powK (Lp : List ℕ) (D : PD) (n : ℕ) : redB (powK Lp D (n + 1)) = true :=
  redB_compK Lp _ D

theorem redB_repRK (ts : List PD) (k : ℕ) (v : List ℕ) : redB (repRK ts k v) = true := by
  unfold repRK
  split_ifs
  · exact redB_nfL v
  · exact redB_compK _ _ _

theorem dK_inj {D D' : PD} (hD : GoodPD D) (hD' : GoodPD D') (hr : redB D = true)
    (hr' : redB D' = true) (h : dK D = dK D') : D = D' := by
  obtain ⟨hc, hl⟩ := redB_spec hr
  obtain ⟨hc', hl'⟩ := redB_spec hr'
  have h1 : D.1 = D'.1 := by
    refine List.ext_getElem (by rw [hD.1, hD'.1]) fun k hk hk' => ?_
    have hk12 : k < 12 := by rwa [hD.1] at hk
    have ek := congrArg Prod.fst (congrFun (congrArg Prod.fst h) ⟨k, hk12⟩)
    change vz (D.1.getD k 0) = vz (D'.1.getD k 0) at ek
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] at ek
    exact goodRow_ext (hD.2.1 _ (List.getElem_mem hk)) (hD'.2.1 _ (List.getElem_mem hk')) ek
  have h2 : D.2.1 = D'.2.1 := by
    refine List.ext_getElem (by rw [hD.2.2, hD'.2.2]) fun k hk hk' => ?_
    have hk12 : k < 12 := by rwa [hD.2.2] at hk
    have ek := congrArg Prod.snd (congrFun (congrArg Prod.fst h) ⟨k, hk12⟩)
    change ((D.2.1.getD k 0 : ℕ) : ZMod 3) = ((D'.2.1.getD k 0 : ℕ) : ZMod 3) at ek
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] at ek
    exact rc_cast_inj (hc _ (List.getElem_mem hk)) (hc' _ (List.getElem_mem hk')) ek
  have h3 : D.2.2 = D'.2.2 := rc_cast_inj hl hl' (congrArg Prod.snd h)
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem pdEq_self (D : PD) : pdEq D D = true := by
  simp [pdEq]

theorem redB_oneK : redB oneK = true := by decide +kernel

theorem adEq_of_pdEq {P Q : PD} {A A' : AD} (hP : GoodPD P ∧ dK P = toD A)
    (hQ : GoodPD Q ∧ dK Q = toD A') (h : pdEq P Q = true) : Timmesfeld.M3B.adEq A A' = true :=
  adEq_complete (by rw [← hP.2, ← hQ.2, eq_of_pdEq h])

theorem adEq_false_of_pdEq {P Q : PD} {A A' : AD} (hP : GoodPD P ∧ dK P = toD A)
    (hQ : GoodPD Q ∧ dK Q = toD A') (hr : redB P = true) (hr' : redB Q = true)
    (h : pdEq P Q = false) : Timmesfeld.M3B.adEq A A' = false := by
  cases hq : Timmesfeld.M3B.adEq A A'
  · rfl
  · have e := dK_inj hP.1 hQ.1 hr hr' (by rw [hP.2, hQ.2, adEq_sound hq])
    rw [e, pdEq_self] at h
    exact absurd h (by decide)

theorem repRK_sound {ts : List PD} {k : ℕ} (hT : GoodPD (ts.getD k oneK) ∧
    dK (ts.getD k oneK) = toD (tDk k)) {v : List ℕ} (h : vOKB v = true) :
    GoodPD (repRK ts k v) ∧ dK (repRK ts k v) = toD (repD k v) := by
  have hN := nfL_sound h
  by_cases hk : k = 0
  · rw [repRK, repD, if_pos hk, if_pos hk]
    exact hN
  · rw [repRK, repD, if_neg hk, if_neg hk]
    obtain ⟨g, e⟩ := compK_sound lpM_ok hT.1 hN.1
    refine ⟨g, ?_⟩
    rw [e, toD_comp, hT.2, hN.2, tDk, if_neg hk]

theorem cube_eqK {T : PD} {t : AD} (hT : GoodPD T ∧ dK T = toD t) {v : List ℕ}
    (hv : vOKB v = true) : toE (cubeE (B0 ()) t (eOf v 0)) = toEK (cubeK T (eP v)) := by
  obtain ⟨hxg, hx⟩ := eP_sound hv
  obtain ⟨hyg, hy⟩ := substP_sound hT.1 hxg
  have hc : cubeK T (eP v) = emulK (emulK (substP T (substP T (eP v))) (substP T (eP v))) (eP v) :=
    rfl
  rw [hc, emulK_sound, emulK_sound, (substP_sound hT.1 hyg).2, hy, hT.2, hx]
  unfold cubeE
  rw [toE_emul, toE_emul, toE_subst, toE_subst]

theorem cube_one {T : PD} {t : AD} (hT : GoodPD T ∧ dK T = toD t) {v : List ℕ}
    (hv : vOKB v = true) (hc1 : ((cubeK T (eP v)).1 == 0) = true)
    (hc2 : ((cubeK T (eP v)).2 == 1 || (cubeK T (eP v)).2 == 2) = true) :
    Timmesfeld.M3B.eeq (zeroV, (cubeE (B0 ()) t (eOf v 0)).2) (cubeE (B0 ()) t (eOf v 0)) = true ∧
      ((cubeE (B0 ()) t (eOf v 0)).2 != 0) = true := by
  have hcu := cube_eqK hT hv
  rw [beq_iff_eq] at hc1
  simp only [Bool.or_eq_true, beq_iff_eq] at hc2
  generalize cubeK T (eP v) = K at hcu hc1 hc2
  generalize cubeE (B0 ()) t (eOf v 0) = cu at hcu ⊢
  obtain ⟨a, e⟩ := K
  dsimp only at hc1 hc2
  subst hc1
  rw [toEK_eq, vz_zero] at hcu
  have e2 := congrArg Prod.snd hcu
  simp only [toE] at e2
  refine ⟨eeq_complete ?_, ?_⟩
  · rw [toE_zero_pair, hcu]
    exact Prod.ext rfl e2
  · rw [bne_iff_ne]
    intro h0
    rw [h0, toZ_zero] at e2
    rcases hc2 with rfl | rfl <;> exact absurd e2 (by decide)

theorem cube_triv {T : PD} {t : AD} (hT : GoodPD T ∧ dK T = toD t) {v : List ℕ}
    (hv : vOKB v = true) (hc : (cubeK T (eP v) == (0, 0)) = true) :
    Timmesfeld.M3B.eeq (cubeE (B0 ()) t (eOf v 0)) Timmesfeld.M3B.eone = true := by
  rw [beq_iff_eq] at hc
  refine eeq_complete ?_
  rw [cube_eqK hT hv, hc, toEK_zero, toE_eone]

theorem conj_ok {T : PD} {t : AD} (hT : GoodPD T ∧ dK T = toD t) {v y : List ℕ}
    (hv : vOKB v = true) (s : ℕ)
    (h : (s != 3 || (vOKB y && zconjK T (eP v) (eP y) == emulK (eP v) (0, 1))) = true) :
    (s != 3 || Timmesfeld.M3B.eeq (zconjE (B0 ()) t (eOf v 0) (eOf y 0))
      (Timmesfeld.M3B.emul (B0 ()) (eOf v 0) (zeroV, 1))) = true := by
  by_cases h3 : s = 3
  · subst h3
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨hvy, hz⟩ := h
    obtain ⟨hxg, hx⟩ := eP_sound hv
    have hy := (eP_sound hvy).2
    have hzs : toEK (zconjK T (eP v) (eP y)) = emul (toMat (B0 ())) (emul (toMat (B0 ()))
        (subst (toMat (B0 ())) (dK T) (epow (toMat (B0 ())) (toEK (eP y)) 2)) (toEK (eP v)))
        (toEK (eP y)) := by
      rw [zconjK, emulK_sound, emulK_sound, (substP_sound hT.1 (goodRow_sqK (eP y))).2, sqK_sound]
    refine eeq_complete ?_
    unfold zconjE
    rw [toE_emul, toE_emul, toE_subst, toE_epow, toE_emul, toE_zero_pair, ← hT.2, ← hx, ← hy,
      ← hzs, hz, emulK_sound, toEK_eq 0 1, vz_zero, Nat.cast_one]
    rfl
  · simp [h3]

theorem rootOK_of_F {ts : List PD}
    (hts : ∀ k < 4, GoodPD (ts.getD k oneK) ∧ dK (ts.getD k oneK) = toD (tDk k))
    {c : ℕ × List ℕ × ℕ × List ℕ} (h : rootOKF ts c = true) : rootOK c = true := by
  obtain ⟨k, v, s, y⟩ := c
  unfold rootOKF at h
  unfold rootOK
  dsimp only at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hk, hv⟩, hs⟩ := h
  have hT := hts k hk
  have hR := repRK_sound hT hv
  split_ifs at hs ⊢ with h0 h4 h1
  ·
    rw [Bool.not_eq_true'] at hs ⊢
    exact adEq_false_of_pdEq (pow_sound hR 3) one_sound (redB_powK _ _ 2) redB_oneK hs
  ·
    exact adEq_of_pdEq hR one_sound hs
  ·
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs ⊢
    obtain ⟨⟨hne, hc1, hc2⟩, hconj⟩ := hs
    exact ⟨⟨adEq_false_of_pdEq hR one_sound (redB_repRK _ _ _) redB_oneK hne,
      cube_one hT hv hc1 hc2⟩, conj_ok hT hv s hconj⟩
  ·
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs ⊢
    obtain ⟨⟨hne, hc⟩, hconj⟩ := hs
    exact ⟨⟨adEq_false_of_pdEq hR one_sound (redB_repRK _ _ _) redB_oneK hne, cube_triv hT hv hc⟩,
      conj_ok hT hv s hconj⟩

theorem rootsOK_of_F {ts : List PD}
    (hts : ∀ k < 4, GoodPD (ts.getD k oneK) ∧ dK (ts.getD k oneK) = toD (tDk k))
    (h : rootChkF ts rootClaims = true) : rootsOK () = true := by
  unfold rootsOK
  unfold rootChkF at h
  rw [List.all_eq_true] at h ⊢
  exact fun c hc => rootOK_of_F hts (h c hc)

end CFSG.KC.M3BF

end
