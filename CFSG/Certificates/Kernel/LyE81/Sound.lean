module

public import Certificates.Data.Kernel.LyE81.Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporLyKit
public import CFSG.Certificates.Kernel.ArrBfsSim
public import CFSG.Certificates.Kernel.LyS0.Sound
public import CFSG.Certificates.Kernel.LocalQTSecLemmas
import CFSG.Certificates.Kernel.SporSch.LyLoop
import Mathlib.Tactic.IntervalCases
public import CFSG.Open.Defs

public section

namespace CFSG.KS.LyE81K

open CFSG.KD.LyE81 CFSG.KD.LyS0 CFSG.KC.Ord CFSG.KC.Enum CFSG.KS.SporSch.LyM CFSG.KS.Ord
open CFSG.Sporadic.He.Native CFSG.RankThree.PartTwo.Sec4.Item434SporLy
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Monster.B.Fischer CFSG.KS.ArrBfsSim
open CFSG.KS.LyS0K (strictN_eq strictB_eq nIf_eq bIf_eq mulE mulV idE vOne blt_of hv)

local notation "U" X:max => unpackL 111 12 1332 X

theorem canonM {X : Nat} (h : vld X = true) : Canon 5 111 12 X :=
  validM_canon CFSG.KD.OrdLy.consts (hv h)

theorem powE {M : Nat} (hM : vld M = true) (e : Nat) :
    powM 5 111 (U M) e = U (pw M e) ∧ vld (pw M e) = true := by
  have h := powM_eq CFSG.KD.OrdLy.consts (hv hM) e
  exact h

theorem powLE {M : Nat} (hM : vld M = true) (e : Nat) :
    powL (U M) e = U (powLK M e) ∧ vld (powLK M e) = true := by
  unfold powL powLK
  rw [nIf_eq]
  by_cases he : e = 1
  · subst he
    have hb : Nat.beq 1 1 = true := rfl
    rw [if_pos rfl, hb, if_pos rfl]
    exact ⟨rfl, hM⟩
  · have hb : Nat.beq e 1 = false := Bool.eq_false_iff.2 fun h => he (Nat.eq_of_beq_eq_true h)
    rw [if_neg he, hb]
    exact powE hM e

theorem wordK_go (G : Nat → Nat) : ∀ (w : List (Nat × Nat)) (acc : Nat),
    List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun x _ ih acc => strictN (mul acc (powLK (G x.1) x.2)) ih) w acc =
      w.foldl (fun acc x => mul acc (powLK (G x.1) x.2)) acc
  | [], _ => rfl
  | x :: w, acc => by
    change strictN (mul acc (powLK (G x.1) x.2)) _ = _
    rw [strictN_eq, List.foldl_cons, wordK_go G w]

theorem evalWord_go {gs : Array Mat} {G : Nat → Nat} : ∀ (w : List (Nat × Nat)) (acc : Mat)
    (A : Nat), acc = U A → vld A = true →
    (∀ x ∈ w, gs[x.1]! = U (G x.1) ∧ vld (G x.1) = true) →
    w.foldl (fun acc x => mulM 5 111 acc (powL gs[x.1]! x.2)) acc =
        U (w.foldl (fun acc x => mul acc (powLK (G x.1) x.2)) A) ∧
      vld (w.foldl (fun acc x => mul acc (powLK (G x.1) x.2)) A) = true
  | [], _, A, he, hA, _ => ⟨he, hA⟩
  | x :: w, acc, A, he, hA, hg => by
    obtain ⟨e1, v1⟩ := hg x List.mem_cons_self
    obtain ⟨e2, v2⟩ := powLE v1 x.2
    rw [List.foldl_cons, List.foldl_cons]
    refine evalWord_go w _ _ ?_ (mulV hA v2) fun y hy => hg y (List.mem_cons_of_mem x hy)
    rw [he, e1, e2, mulE hA v2]

theorem evalWord_eq {gs : Array Mat} {G : Nat → Nat} {w : List (Nat × Nat)}
    (hg : ∀ x ∈ w, gs[x.1]! = U (G x.1) ∧ vld (G x.1) = true) :
    evalWord gs w = U (wordK G w) ∧ vld (wordK G w) = true := by
  unfold evalWord wordK
  rw [wordK_go]
  exact evalWord_go w _ _ idE vOne hg

theorem invE {X Y : Nat} (hX : vld X = true) (hY : vld Y = true)
    (h : Nat.beq (mul X Y) CFSG.KD.OrdLy.ONE = true) : invM 5 111 (U X) = U Y :=
  invM_eq (by norm_num) CFSG.KD.OrdLy.consts (hv hX) (hv hY) h

theorem beqU {X Y : Nat} (hX : vld X = true) (hY : vld Y = true) :
    (U X == U Y) = Nat.beq X Y := beq_eq CFSG.KD.OrdLy.consts (hv hX) (hv hY)

set_option maxRecDepth 100000 in
theorem slpM_eq {A B C D : Nat} (vA : vld A = true) (vB : vld B = true)
    (h1 : Nat.beq (mul (mul (pw (slpR6 A B) 15) A) (pw (slpR6 A B) 52)) C = true)
    (h2 : Nat.beq (mul (mul (pw (slpR9 A B) 55) (slpR2 A B)) (pw (slpR9 A B) 12)) D = true)
    (h3 : Nat.beq (mul (pw (slpR6 A B) 15) (pw (slpR6 A B) 52)) CFSG.KD.OrdLy.ONE = true)
    (h4 : Nat.beq (mul (pw (slpR9 A B) 12) (pw (slpR9 A B) 55)) CFSG.KD.OrdLy.ONE = true) :
    slpM (U A) (U B) = (U C, U D, true) := by
  have v3 := mulV vA vB
  have v4 := mulV v3 vB
  have v5 : vld (slpR5 A B) = true := mulV v3 v4
  have v9 : vld (slpR9 A B) = true := mulV vB v5
  have v6 : vld (slpR6 A B) = true := mulV v3 v5
  have v7 : vld (slpR7 A B) = true := mulV v6 v3
  have v8 := mulV v7 v7
  have v2 : vld (slpR2 A B) = true := mulV v7 v8
  have f5 : mul (mul A B) (mul (mul A B) B) = slpR5 A B := rfl
  have f6 : mul (mul A B) (slpR5 A B) = slpR6 A B := rfl
  have f9 : mul B (slpR5 A B) = slpR9 A B := rfl
  have f7 : mul (slpR6 A B) (mul A B) = slpR7 A B := rfl
  have f2 : mul (slpR7 A B) (mul (slpR7 A B) (slpR7 A B)) = slpR2 A B := rfl
  obtain ⟨e15, w15⟩ := powE v6 15
  obtain ⟨e52, w52⟩ := powE v6 52
  obtain ⟨e12, w12⟩ := powE v9 12
  obtain ⟨e55, w55⟩ := powE v9 55
  have i1 := invE w15 w52 h3
  have i2 := invE w12 w55 h4
  unfold slpM
  simp only []
  rw [mulE vA vB, mulE v3 vB, mulE v3 v4, f5, mulE vB v5, f9, mulE v3 v5, f6, mulE v6 v3, f7,
    mulE v7 v7, mulE v7 v8, f2, e15, e12, i1, i2, mulE w15 vA, mulE (mulV w15 vA) w52,
    mulE w55 v2, mulE (mulV w55 v2) w12, mulE w15 w52, mulE w12 w55, idE,
    beqU (mulV w15 w52) vOne, beqU (mulV w12 w55) vOne, Nat.eq_of_beq_eq_true h1,
    Nat.eq_of_beq_eq_true h2, h3, h4]
  rfl

theorem get0 (a b : Mat) : (#[a, b] : Array Mat)[0]! = a := rfl

theorem get1 (a b : Mat) : (#[a, b] : Array Mat)[1]! = b := rfl

@[expose] noncomputable def cdF (C D l : Nat) : Nat := nIf(Nat.beq l 0, C, D)

theorem cdF0 (C D : Nat) : cdF C D 0 = C := rfl

theorem cdF1 (C D : Nat) : cdF C D 1 = D := rfl

theorem P_eq {X : LyE81Data} {C D : Nat} {PK : Nat → Nat} (vC : vld C = true) (vD : vld D = true)
    (hsz : X.pW.size = 7)
    (hlet : X.pW.toList.all (fun w => w.all fun x => decide (x.1 < 2)) = true)
    (hw : ∀ k < 7, wordK (cdF C D) (X.pW[k]!) = PK k) :
    (X.pW.map (evalWord #[U C, U D])).size = 7 ∧
      ∀ k < 7, (X.pW.map (evalWord #[U C, U D]))[k]! = U (PK k) ∧ vld (PK k) = true := by
  refine ⟨by rw [Array.size_map, hsz], fun k hk => ?_⟩
  have hk' : k < X.pW.size := by rw [hsz]; exact hk
  rw [getElem!_pos _ k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
    ← getElem!_pos X.pW k hk']
  have hg : ∀ x ∈ X.pW[k]!, (#[U C, U D] : Array Mat)[x.1]! = U (cdF C D x.1) ∧
      vld (cdF C D x.1) = true := by
    intro x hx
    have hl : x.1 < 2 := by
      have h1 := List.all_eq_true.1 hlet (X.pW[k]!) (by
        rw [getElem!_pos X.pW k hk']
        exact Array.getElem_mem_toList hk')
      simpa using List.all_eq_true.1 h1 x hx
    rcases (by omega : x.1 = 0 ∨ x.1 = 1) with h0 | h0
    · rw [h0, get0, cdF0]
      exact ⟨rfl, vC⟩
    · rw [h0, get1, cdF1]
      exact ⟨rfl, vD⟩
  obtain ⟨e, v⟩ := evalWord_eq hg
  rw [hw k hk] at e v
  exact ⟨e, v⟩

theorem pcCheck_of {P : Array Mat} {PK : Nat → Nat} {cubeW : Array (List (Nat × Nat))}
    {commW : Array (Array (List (Nat × Nat)))} (hsz : P.size = 7)
    (hP : ∀ k < 7, P[k]! = U (PK k) ∧ vld (PK k) = true) (h : pcK PK cubeW commW = true) :
    pcCheck 7 P cubeW commW = true := by
  have ev : ∀ w : List (Nat × Nat), (∀ x ∈ w, x.1 < 7) →
      evalWord P w = U (wordK PK w) ∧ vld (wordK PK w) = true :=
    fun w hw => evalWord_eq fun x hx => hP x.1 (hw x hx)
  unfold pcK at h
  unfold pcCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq] at h ⊢
  refine ⟨hsz, fun i hi => ?_⟩
  obtain ⟨⟨hA, hB⟩, hC⟩ := h i hi
  refine ⟨⟨hA, ?_⟩, fun j hj => ?_⟩
  · obtain ⟨e1, -⟩ := ev [(i, 3)] (by simpa using hi)
    obtain ⟨e2, -⟩ := ev (cubeW[i]!) fun x hx => (hA x hx).2
    rw [e1, e2, Nat.eq_of_beq_eq_true hB]
  · rcases hC j hj with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      obtain ⟨e1, -⟩ := ev [(i, 1), (j, 1)] (by simp [hi, hj])
      obtain ⟨e2, -⟩ := ev ((commW[i]!)[j]! ++ [(i, 1)]) fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact (h1 x hx).2
        · simp at hx
          rw [hx]
          exact hi
      rw [e1, e2, Nat.eq_of_beq_eq_true h2]

theorem ln_eq (x j : Nat) : ln x j = lane 12 x j := by
  have h1 : ln x j = (x >>> (12 * j)) &&& (2 ^ 12 - 1) := rfl
  rw [h1, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rfl

theorem vldV_spec {x : Nat} (h : vldV x = true) : CFSG.KC.LQT.SecS.VCanon 5 111 12 x := by
  unfold vldV at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hx : x >>> 1332 = 0 := Nat.eq_of_beq_eq_true h1
  refine ⟨?_, fun j hj => ?_⟩
  · rw [Nat.shiftRight_eq_div_pow] at hx
    by_contra hge
    have hle : 2 ^ 1332 ≤ x := by
      have : (12 * 111 : Nat) = 1332 := rfl
      rw [this] at hge
      omega
    have := Nat.div_pos hle (by positivity)
    omega
  · have e := allBlk_spec h2 j hj
    rw [Nat.add_eq, Nat.zero_add] at e
    rw [← ln_eq]
    exact blt_of e

theorem UV_get {x j : Nat} (hj : j < 111) : (UV x)[j]! = ln x j := by
  unfold UV
  rw [getElem!_ofFn _ hj]

theorem UV_size (x : Nat) : (UV x).size = 111 := by
  unfold UV
  simp

theorem canonV_ofFn {f : Fin 111 → Nat} (h : ∀ j, f j < 5) : canonV 5 111 (Array.ofFn f) = true := by
  unfold canonV
  rw [Bool.and_eq_true]
  refine ⟨by simp, ?_⟩
  rw [Array.all_eq_true]
  intro i hi
  simp only [Array.getElem_ofFn]
  exact decide_eq_true (h _)

theorem canonV_UV' {x : Nat} (hx : CFSG.KC.LQT.SecS.VCanon 5 111 12 x) :
    canonV 5 111 (UV x) = true := by
  unfold UV
  exact canonV_ofFn fun j => by
    rw [ln_eq]
    exact hx.2 j.val j.isLt

theorem canonV_UV {x : Nat} (hx : vldV x = true) : canonV 5 111 (UV x) = true :=
  canonV_UV' (vldV_spec hx)

theorem toVec_UV (x : Nat) : toVec 5 111 (UV x) = CFSG.KC.LQT.SecS.toVec 5 111 12 x := by
  funext j
  rw [toVec_apply, UV_get j.isLt, ln_eq]
  rfl

theorem canonV_mulVec (M : Array (Array Nat)) (v : Array Nat) :
    canonV 5 111 (mulVec 5 111 M v) = true := by
  unfold mulVec
  exact canonV_ofFn fun j => by
    unfold dot
    exact Nat.mod_lt _ (by norm_num)

theorem trK_spec {X Y : Nat} (h : trK X Y = true) :
    vld Y = true ∧ ∀ i < 111, ∀ j < 111, ln X (111 * i + j) = ln Y (111 * j + i) := by
  unfold trK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, fun i hi j hj => ?_⟩
  have e := allBlk_spec (allN_spec h2 i hi) j hj
  simp only [Nat.add_eq, Nat.mul_eq, Nat.zero_add] at e
  exact Nat.eq_of_beq_eq_true e

theorem ln_ent (X i j : Nat) :
    ln X (111 * i + j) = X / 2 ^ (1332 * i + 12 * j) % 2 ^ 12 := by
  rw [ln_eq]
  unfold lane
  have e : 12 * (111 * i + j) = 1332 * i + 12 * j := by ring
  rw [e]

theorem toMat_U (X : Nat) : toMat 5 111 (U X) = ordMat 5 111 12 1332 X := by
  ext i j
  rw [toMat_apply, unpackL_get i.isLt j.isLt]
  unfold ordMat
  rfl

theorem mulVec_UV {X Y x : Nat} (ht : trK X Y = true) (hx : vldV x = true) :
    mulVec 5 111 (U X) (UV x) = UV (vec x Y) := by
  obtain ⟨vY, hT⟩ := trK_spec ht
  have hvc := vldV_spec hx
  obtain ⟨hc', hv'⟩ := CFSG.KC.LQT.SecS.vecR_sound CFSG.KD.OrdLy.consts hvc (canonM vY)
  have hvec : vec x Y =
      vecR 5 12 1332 111 8 CFSG.KD.OrdLy.LV CFSG.KD.OrdLy.HV CFSG.KD.OrdLy.RM x Y := rfl
  rw [← hvec] at hc' hv'
  refine eq_of_toVec_eq (canonV_mulVec _ _) (canonV_UV' hc') ?_
  rw [toVec_mulVec, toVec_UV, toVec_UV, toMat_U, hv']
  have hY : ordMat 5 111 12 1332 Y = (ordMat 5 111 12 1332 X).transpose := by
    ext i j
    rw [Matrix.transpose_apply]
    unfold ordMat
    rw [← ln_ent Y i.val j.val, ← ln_ent X j.val i.val, hT j.val j.isLt i.val i.isLt]
  rw [hY, Matrix.vecMul_transpose]

theorem keyK_go (x : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.add (Nat.mul acc 5) (ln x j)) n =
    (List.range n).foldl (fun acc j => acc * 5 + ln x j) 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, ← keyK_go x n]
    rfl

theorem ofFn_range (n : Nat) (g : Nat → Nat) :
    List.ofFn (fun j : Fin n => g j.val) = (List.range n).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem keyV_UV (x : Nat) : keyV (UV x) = keyK x := by
  unfold keyV UV keyK
  rw [← Array.foldl_toList, Array.toList_ofFn, ofFn_range, List.foldl_map, keyK_go]

theorem orbAt_spec {M V PA LA : Nat → Nat} {E : Nat → Nat → Nat} {i : Nat}
    (h : orbAt M V E PA LA i = true) :
    vldV (V i) = true ∧
      (∀ k < 7, E i k < 2187 ∧ V (E i k) = vec (V i) (M k) ∧
        (E i k = 0 ∨ posK PA LA (E i k) ≤ 7 * i + k)) ∧
      (i = 0 → PA 0 = 0 ∧ LA 0 = 0) ∧
      (i ≠ 0 → PA i < i ∧ LA i < 7 ∧ E (PA i) (LA i) = i ∧
        (i ≠ 2186 → posK PA LA i < posK PA LA (i + 1))) := by
  unfold orbAt at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, fun k hk => ?_, fun hi => ?_, fun hi => ?_⟩
  · have e := allBlk_spec h2 k hk
    rw [Nat.add_eq, Nat.zero_add, strictB_eq] at e
    obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e2, e3⟩ := (bAnd_iff _ _).1 e
    refine ⟨blt_of e1, Nat.eq_of_beq_eq_true e2, ?_⟩
    rw [bIf_eq] at e3
    by_cases h0 : E i k = 0
    · exact Or.inl h0
    · have hb : Nat.beq (E i k) 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [hb] at e3
      simp only [Bool.false_eq_true, ↓reduceIte] at e3
      exact Or.inr (Nat.le_of_ble_eq_true e3)
  · subst hi
    rw [bIf_eq] at h3
    simp only [Nat.beq_refl, ↓reduceIte] at h3
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 h3
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2⟩
  · have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [bIf_eq, hb] at h3
    simp only [Bool.false_eq_true, ↓reduceIte] at h3
    obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 h3
    obtain ⟨e2, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e3, e4⟩ := (bAnd_iff _ _).1 e
    refine ⟨blt_of e1, blt_of e2, Nat.eq_of_beq_eq_true e3, fun hi' => ?_⟩
    rw [bIf_eq] at e4
    have hb' : Nat.beq i 2186 = false :=
      Bool.eq_false_iff.2 fun h => hi' (Nat.eq_of_beq_eq_true h)
    rw [hb'] at e4
    simp only [Bool.false_eq_true, ↓reduceIte] at e4
    exact blt_of e4

theorem blocks {P : Nat → Prop} (h : ∀ q < 27, ∀ l < 81, P (81 * q + l)) : ∀ i < 2187, P i :=
  CFSG.KS.LyS0K.slices h

theorem tables_of {P : Array Mat} {PK PT V PA LA SO SOI : Nat → Nat} {E : Nat → Nat → Nat}
    (hP : ∀ k < 7, P[k]! = U (PK k)) (htr : ∀ k < 7, trK (PK k) (PT k) = true)
    (horb : ∀ q < 27, orbK PT V E PA LA (81 * q) 81 = true)
    (hsort : ∀ q < 27, sortK V SO SOI (81 * q) 81 = true) :
    Tables 7 2187 (actV P) keyV (fun i => UV (V i)) E PA LA ∧
      ∀ i < 2187, vldV (V i) = true := by
  have hall : ∀ i < 2187, orbAt PT V E PA LA i = true := blocks fun q hq l hl => by
    have e := allBlk_spec (horb q hq) l hl
    rw [strictB_eq] at e
    exact e
  have hs : ∀ i < 2187, sortB (fun j => keyK (V j)) SO SOI 2187 i = true := blocks fun q hq l hl => by
    have e := allBlk_spec (hsort q hq) l hl
    rw [strictB_eq] at e
    exact e
  have hinj := CFSG.KS.SporSch.LyLoop.sortB_inj hs
  refine ⟨⟨by norm_num, fun i hi k hk => ?_, fun a ha b hb e => ?_, ?_, ?_, fun j hj1 hjN => ?_,
    fun j hj1 hjN => ?_, fun i hi k hk => ?_⟩, fun i hi => (orbAt_spec (hall i hi)).1⟩
  · obtain ⟨hv, hE, -, -⟩ := orbAt_spec (hall i hi)
    obtain ⟨e1, e2, -⟩ := hE k hk
    refine ⟨e1, ?_⟩
    unfold actV
    rw [hP k hk, mulVec_UV (htr k hk) hv, ← e2]
  · rw [keyV_UV, keyV_UV] at e
    exact hinj a ha b hb e
  · exact ((orbAt_spec (hall 0 (by norm_num))).2.2.1 rfl).1
  · exact ((orbAt_spec (hall 0 (by norm_num))).2.2.1 rfl).2
  · obtain ⟨h1, h2, h3, -⟩ := (orbAt_spec (hall j hjN)).2.2.2 (by omega)
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := (orbAt_spec (hall j (by omega))).2.2.2 (by omega)
    exact h4 (by omega)
  · obtain ⟨-, hE, -, -⟩ := orbAt_spec (hall i hi)
    exact (hE k hk).2.2

theorem orbitOK_of {P : Array Mat} {V PA LA : Nat → Nat} {E : Nat → Nat → Nat} {v : Array Nat}
    (hsz : P.size = 7)
    (T : Tables 7 2187 (actV P) keyV (fun i => UV (V i)) E PA LA)
    (hvld : ∀ i < 2187, vldV (V i) = true) (hv : v = UV (V 0)) :
    orbitOK P v (cert 7 2187 (fun i => UV (V i)) E PA LA) 2187 = true := by
  set c := cert 7 2187 (fun i => UV (V i)) E PA LA with hc
  have hpsz : c.pts.size = 2187 := by simp [hc, cert]
  have hpts : ∀ i < 2187, c.pts[i]! = UV (V i) := fun i hi => by
    simp only [hc, cert]
    exact toArray_get hi
  have hed : ∀ i < 2187, c.edges[i]! = ((List.range 7).map (E i)).toArray := fun i hi => by
    simp only [hc, cert]
    exact toArray_get (p := fun h => ((List.range 7).map (E h)).toArray) hi
  have hpar : ∀ i < 2187, c.par[i]! = PA i := fun i hi => by
    simp only [hc, cert]
    exact toArray_get hi
  have hlab : ∀ i < 2187, c.lab[i]! = LA i := fun i hi => by
    simp only [hc, cert]
    exact toArray_get hi
  have hpoint : ∀ i < 2187, arrPointOK (actV P) 7 (canonV 5 111) c i = true := by
    intro i hi
    unfold arrPointOK
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true]
    rw [hpts i hi, hed i hi, hpsz]
    refine ⟨⟨⟨canonV_UV (hvld i hi), by simp⟩, fun k hk => ?_⟩, ?_⟩
    · rw [toArray_get hk]
      obtain ⟨e1, e2⟩ := T.act i hi k hk
      refine ⟨e1, ?_⟩
      rw [hpts _ e1, e2]
    · by_cases hi0 : i = 0
      · exact Or.inl hi0
      · obtain ⟨h1, h2, h3⟩ := T.tree i (by omega) hi
        refine Or.inr ⟨⟨by rw [hpar i hi]; exact h1, by rw [hlab i hi]; exact h2⟩, ?_⟩
        rw [hpar i hi, hlab i hi, hpts _ (by omega), (T.act _ (by omega) _ h2).2, h3]
  have hkeys : (c.pts.toList.map keyV).Nodup := by
    simp only [hc, cert, List.toList_toArray, List.map_map]
    refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    rw [List.mem_range] at ha hb
    rw [Function.comp_apply, Function.comp_apply] at e
    exact T.key a ha b hb e
  have hsort : ((c.pts.toList.map keyV).mergeSort (fun a b => decide (a ≤ b))).Pairwise
      (· < ·) := by
    have hperm := List.mergeSort_perm (c.pts.toList.map keyV) (fun a b => decide (a ≤ b))
    have hsorted := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (c.pts.toList.map keyV)
    have hnd' := hperm.nodup_iff.2 hkeys
    refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.and hsorted hnd')
    intro a b _ _ hab
    simp only [decide_eq_true_eq] at hab
    omega
  unfold orbitOK arrCertOK
  rw [hsz]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨by rw [hv]; exact canonV_UV (hvld 0 (by norm_num)),
    ⟨⟨⟨by rw [hpsz]; norm_num, by rw [hpts 0 (by norm_num), hv]⟩, fun i hi => ?_⟩, hsort⟩⟩, hpsz⟩
  rw [hpsz] at hi
  exact hpoint i hi

theorem edges_get (E : Nat → Nat → Nat) (x k : Nat) :
    ((((List.range 2187).map fun h => ((List.range 7).map (E h)).toArray).toArray)[x]!)[k]! =
      edK E x k := by
  unfold edK
  rw [nIf_eq]
  by_cases hx : x < 2187
  · have hxb : Nat.blt x 2187 = true := CFSG.KS.LyS0K.blt_iff hx
    rw [toArray_get hx, hxb]
    by_cases hk : k < 7
    · have hkb : Nat.blt k 7 = true := CFSG.KS.LyS0K.blt_iff hk
      rw [toArray_get hk, hkb]
      rfl
    · have hkb : Nat.blt k 7 = false := Bool.eq_false_iff.2 fun h => hk (blt_of h)
      rw [getElem!_neg _ k (by simpa using hk), hkb]
      rfl
  · have hxb : Nat.blt x 2187 = false := Bool.eq_false_iff.2 fun h => hx (blt_of h)
    rw [getElem!_neg _ x (by simpa using hx), hxb]
    have : (default : Array Nat)[k]! = 0 :=
      getElem!_neg _ k (show ¬ k < (#[] : Array Nat).size by simp)
    rw [this]
    rfl

theorem tab_get (F : Nat → Nat) (i : Nat) : ((List.range 2187).map F).toArray[i]! = tbK F i := by
  unfold tbK
  rw [nIf_eq]
  by_cases hi : i < 2187
  · rw [toArray_get hi]
    have : Nat.blt i 2187 = true := Eq.mpr Nat.blt_eq hi
    rw [this]
    rfl
  · rw [getElem!_neg _ i (by simpa using hi)]
    have : Nat.blt i 2187 = false := Bool.eq_false_iff.2 fun h => hi (blt_of h)
    rw [this]
    rfl

theorem mulIdx_eq (E : Nat → Nat → Nat) (PA LA : Nat → Nat) : ∀ f i j,
    mulIdx (((List.range 2187).map fun h => ((List.range 7).map (E h)).toArray).toArray)
      ((List.range 2187).map PA).toArray ((List.range 2187).map LA).toArray f i j =
      mulIdxK E PA LA f i j
  | 0, _, _ => rfl
  | f + 1, i, j => by
    unfold mulIdx
    change _ = nIf(Nat.beq i 0, j, edK E (mulIdxK E PA LA f (tbK PA i) j) (tbK LA i))
    rw [nIf_eq]
    by_cases hi : i = 0
    · subst hi
      rfl
    · have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
      rw [if_neg hi, hb, tab_get, tab_get, mulIdx_eq E PA LA f, edges_get]
      rfl

theorem tabCheck_eq (V : Nat → Nat) (E : Nat → Nat → Nat) (PA LA : Nat → Nat) (idZ : Nat)
    (sets : List (List Nat)) :
    tabCheck 7 2187 (cert 7 2187 (fun i => UV (V i)) E PA LA).edges
      (cert 7 2187 (fun i => UV (V i)) E PA LA).par (cert 7 2187 (fun i => UV (V i)) E PA LA).lab
      idZ sets = tabG 7 2187 (mulIdxK E PA LA 2187) (edK E) idZ sets := by
  have e1 : mulIdx (cert 7 2187 (fun i => UV (V i)) E PA LA).edges
      (cert 7 2187 (fun i => UV (V i)) E PA LA).par (cert 7 2187 (fun i => UV (V i)) E PA LA).lab
      2187 = mulIdxK E PA LA 2187 := funext fun i => funext fun j => mulIdx_eq E PA LA 2187 i j
  have e2 : (fun x k => (((cert 7 2187 (fun i => UV (V i)) E PA LA).edges)[x]!)[k]!) = edK E :=
    funext fun x => funext fun k => edges_get E x k
  unfold tabCheck
  rw [e1]
  rw [← e2]
  rfl

end CFSG.KS.LyE81K

end
