module

public import Certificates.Data.Kernel.McLNine.Defs
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
import CFSG.Certificates.Kernel.Spor.BaseMaskGlue
import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KS.McLNine

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.McLAS CFSG.KS.Mathieu
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def PR (p : Nat) (x : Equiv.Perm (Fin 275)) : Prop :=
  canonK 275 9 (mask 9) (275 * 9) p = true ∧ TabRep (unpack 275 9 p) x

@[expose] noncomputable def wP (g : Nat → Equiv.Perm (Fin 275)) (w : List Nat) :
    Equiv.Perm (Fin 275) :=
  (w.map fun l => g (l + 4)).prod

theorem hsz : szOK 275 9 = true := by decide +kernel

theorem comp_unpackA {p q : Nat} (hp : canonK 275 9 (mask 9) (275 * 9) p = true)
    (hq : canonK 275 9 (mask 9) (275 * 9) q = true) :
    comp 275 (unpack 275 9 p) (unpack 275 9 q) = unpack 275 9 (pcomp 275 9 (mask 9) p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

variable {p q : Nat} {x y : Equiv.Perm (Fin 275)}

theorem PR.mul (hp : PR p x) (hq : PR q y) : PR (pcK p q) (x * y) := by
  refine ⟨CFSG.KC.BfsPin.canonK_pcomp hp.1 hq.1, ?_⟩
  change TabRep (unpack 275 9 (pcomp 275 9 (mask 9) p q)) (x * y)
  rw [← comp_unpackA hp.1 hq.1]
  exact hp.2.comp hq.2

theorem PR.one : PR idK 1 := by
  refine ⟨(CFSG.KC.BfsPin.PP.id hsz).1, ?_⟩
  change TabRep (unpack 275 9 (pidn 275 9)) 1
  rw [← CFSG.KC.BfsPin.idA_eq hsz]
  exact TabRep.idTab

theorem PR.pg (hp : PR p x) {i : Nat} (hi : i < 275) :
    pg 9 (mask 9) p i = (x ⟨i, hi⟩ : Nat) := by
  rw [← CFSG.KC.Misc.PairCount.unpack_get hi]
  exact hp.2.apply ⟨i, hi⟩

theorem PR.eq_iff (hp : PR p x) (hq : PR q y) : p = q ↔ x = y := by
  constructor
  · rintro rfl
    exact hp.2.perm_eq hq.2
  · rintro rfl
    exact CFSG.KS.MulH.unpack_injH hp.1 hq.1 (hp.2.tab_eq hq.2)

theorem PR.beq (hp : PR p x) (hq : PR q y) : Nat.beq p q = true ↔ x = y := by
  rw [← hp.eq_iff hq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl p⟩

theorem PR.comm (hp : PR p x) (hq : PR q y) : commK p q = true ↔ x * y = y * x :=
  (hp.mul hq).beq (hq.mul hp)

theorem PR.pow (hp : PR p x) : ∀ e : Nat, PR (pwK e p) (x ^ e)
  | 0 => by
    rw [pow_zero]
    exact PR.one
  | e + 1 => by
    change PR (strictN (pwK e p) (fun a => pcK p a)) (x ^ (e + 1))
    rw [strictN_app', pow_succ']
    exact hp.mul (PR.pow hp e)

@[expose] def Letters (w : List Nat) : Prop := ∀ l ∈ w, l = 1 ∨ l = 2

variable {F : Nat → Nat} {g : Nat → Equiv.Perm (Fin 275)}

theorem PR.letter (hF : ∀ k, 4 ≤ k → k ≤ 6 → PR (F k) (g k)) {l : Nat} (hl : l = 1 ∨ l = 2) :
    PR (ltK F l) (g (l + 4)) := by
  rcases hl with rfl | rfl
  · exact hF 5 (by norm_num) (by norm_num)
  · exact hF 6 (by norm_num) (by norm_num)

theorem PR.word (hF : ∀ k, 4 ≤ k → k ≤ 6 → PR (F k) (g k)) :
    ∀ w : List Nat, Letters w → PR (wK F w) (wP g w)
  | [], _ => PR.one
  | l :: w, h => by
    have ih := PR.word hF w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    change PR (strictN (wK F w) (fun acc => pcK (ltK F l) acc)) (wP g (l :: w))
    rw [strictN_app']
    simp only [wP, List.map_cons, List.prod_cons]
    exact (PR.letter hF (h l List.mem_cons_self)).mul ih

theorem walk_eq (hF : ∀ k, 4 ≤ k → k ≤ 6 → PR (F k) (g k)) :
    ∀ w : List Nat, Letters w → ∀ {a : Nat} (ha : a < 275), walkK F w a = (wP g w ⟨a, ha⟩ : Nat)
  | [], _, a, _ => rfl
  | l :: w, h, a, ha => by
    have ih := walk_eq hF w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) ha
    change strictN (walkK F w a) (fun q => pg 9 (mask 9) (ltK F l) q) = _
    rw [strictN_app', ih, (PR.letter hF (h l List.mem_cons_self)).pg (Fin.isLt _)]
    simp [wP, Equiv.Perm.mul_apply]

theorem wordsK_spec {G : Nat → Nat} :
    ∀ (ws : List (List Nat)) (i : Nat), wordsK F G ws i = true →
      ∀ t < ws.length, G (i + t) = wK F (ws.getD t [])
  | [], _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | w :: ws, i, h, t, ht => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    cases t with
    | zero => exact (Nat.eq_of_beq_eq_true h1).symm
    | succ t =>
      have e := wordsK_spec ws (Nat.succ i) h2 t (by simpa using ht)
      rw [show i + (t + 1) = Nat.succ i + t by omega, e]
      rfl

theorem walksK_spec {a : Nat} :
    ∀ (os : List (List Nat)) (pts : List Nat), walksK F a os pts = true →
      os.length = pts.length ∧ ∀ t < os.length, walkK F (os.getD t []) a = pts.getD t 0
  | [], [], _ => ⟨rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | [], _ :: _, h => absurd h (by simp [walksK])
  | _ :: _, [], h => absurd h (by simp [walksK])
  | w :: os, q :: qs, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hl, hs⟩ := walksK_spec os qs h2
    refine ⟨by simp [hl], fun t ht => ?_⟩
    cases t with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ t => exact hs t (by simpa using ht)

theorem sortedK_spec : ∀ pts : List Nat, sortedK pts = true → pts.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have ih := sortedK_spec xs h2
    refine List.Pairwise.cons (fun y hy => ?_) ih
    cases xs with
    | nil => exact absurd hy List.not_mem_nil
    | cons z zs =>
      have hxz : x < z := Nat.blt_eq.mp h1
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hxz
      · exact hxz.trans (List.rel_of_pairwise_cons ih hy')

theorem cntK_ofFn {n : Nat} (f : Nat → Tab) (r : Tab → Bool) :
    ((Array.ofFn (n := n) fun i => f i.val).toList.filter r).length =
      cntK n (fun i => r (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Array.toList_ofFn, List.ofFn_succ_last, List.filter_append, List.length_append]
    rw [Array.toList_ofFn] at ih
    simp only [Fin.coe_castSucc, Fin.val_last] at ih ⊢
    rw [ih]
    change _ = Bool.rec (motive := fun _ => Nat) (cntK n fun i => r (f i))
      (Nat.succ (cntK n fun i => r (f i))) (r (f n))
    cases h : r (f n) <;> simp [List.filter_cons, h]

theorem cntK_congr {n : Nat} {f f' : Nat → Bool} (h : ∀ i < n, f i = f' i) :
    cntK n f = cntK n f' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => Nat) (cntK n f) (Nat.succ (cntK n f)) (f n) =
      Bool.rec (motive := fun _ => Nat) (cntK n f') (Nat.succ (cntK n f')) (f' n)
    rw [ih fun i hi => h i (by omega), h n (by omega)]

theorem mem_centralizer_closure_iff {A : Set (Equiv.Perm (Fin 275))} {z : Equiv.Perm (Fin 275)} :
    z ∈ Subgroup.centralizer (Subgroup.closure A : Set (Equiv.Perm (Fin 275))) ↔
      ∀ a ∈ A, a * z = z * a := by
  rw [Subgroup.mem_centralizer_iff]
  refine ⟨fun h a ha => h a (Subgroup.subset_closure ha), fun h b hb => ?_⟩
  have hle : Subgroup.closure A ≤ Subgroup.centralizer ({z} : Set (Equiv.Perm (Fin 275))) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro c hc
    rw [Set.mem_singleton_iff.1 hc]
    exact (h a ha).symm
  exact ((Subgroup.mem_centralizer_iff.1 (hle hb)) z rfl).symm

theorem mcl9K_sound {G T PL POS SRT SRI : Nat → Nat} {cnt : Nat} {CW : List Nat}
    {ws : List (List Nat)} {wx wy : List Nat} {a : Nat} {os : List (List Nat)} {pts : List Nat}
    (hF : ∀ k, 4 ≤ k → k ≤ 6 → PR (F k) (g k)) (hws : ws.length = 3)
    (hwl : ∀ w ∈ ws, Letters w) (hx : Letters wx) (hy : Letters wy) (hos : ∀ w ∈ os, Letters w)
    (ha : a < 275)
    (h : mcl9K F G T PL POS SRT SRI cnt CW ws wx wy a os pts = true) :
    let A : Set (Equiv.Perm (Fin 275)) := Set.range fun j : Fin 3 => wP g (ws.getD j [])
    let pt : Fin 275 := ⟨a, ha⟩
    Nat.card (Subgroup.closure A) = 128 ∧
    Nat.card ↥(Subgroup.closure A ⊓
      Subgroup.centralizer (Subgroup.closure A : Set (Equiv.Perm (Fin 275)))) = 2 ∧
    (∀ u ∈ A, u pt = pt ∧ u * g 4 = g 4 * u) ∧
    (∀ q : Fin 275, q ≠ pt → ∃ u ∈ A, u q ≠ q) ∧
    (wP g wx pt = pt ∧ wP g wy pt = pt ∧ wP g wx * g 4 = g 4 * wP g wx ∧
      wP g wy * g 4 = g 4 * wP g wy ∧ wP g wx ^ 3 = 1 ∧ wP g wy ^ 3 = 1 ∧
      wP g wx * wP g wy = wP g wy * wP g wx ∧ wP g wx ≠ 1 ∧ wP g wy ≠ 1 ∧
      wP g wy ≠ wP g wx ∧ wP g wy ≠ wP g wx * wP g wx) ∧
    (os.length = pts.length ∧ (∀ t < os.length, (wP g (os.getD t []) pt : Nat) = pts.getD t 0) ∧
      pts.Pairwise (· < ·)) := by
  intro A pt
  obtain ⟨hw, hc, hhd, hsl, hcw, hcnt, hgen, hmov, hxy, hwalk, hsort⟩ :=
    (by simpa only [mcl9K, bAnd_iff] using h :
      wordsK F G ws 0 = true ∧ Nat.beq cnt 128 = true ∧ penumHdK idK cnt 128 T PL = true ∧
      penumSlK 275 9 (mask 9) (275 * 9) false G G 3 cnt T PL POS SRT SRI 0 cnt = true ∧
      allN cnt (fun i => cwK G (T i) (nget CW i)) = true ∧
      Nat.beq (cntK cnt (fun i => Nat.beq (nget CW i) 3)) 2 = true ∧
      genK F G a = true ∧ movK G a = true ∧
      strictB (wK F wx) (fun x => strictB (wK F wy) (fun y => xyK F a x y)) = true ∧
      walksK F a os pts = true ∧ sortedK pts = true)
  have hcnt128 : cnt = 128 := Nat.eq_of_beq_eq_true hc
  have hG : ∀ j < 3, PR (G j) (wP g (ws.getD j [])) := by
    intro j hj
    have e := wordsK_spec ws 0 hw j (by omega)
    rw [Nat.zero_add] at e
    rw [e]
    exact PR.word hF _ (by
      have hm : ws.getD j [] ∈ ws := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      exact hwl _ hm)
  have hmemA : ∀ u ∈ A, ∃ j < 3, u = wP g (ws.getD j []) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨j, j.2, rfl⟩
  let gens : Array Tab := Array.ofFn (n := 3) fun j => unpack 275 9 (G j.val)
  have hgens_get : ∀ j < 3, gens[j]! = unpack 275 9 (G j) := by
    intro j hj
    rw [getElem!_pos gens j (by simpa [gens] using hj)]
    simp [gens]
  have hgk : GensOK 275 9 3 G gens :=
    ⟨by simp [gens], fun j hj => ⟨hgens_get j hj, (hG j hj).1⟩⟩
  have hp : ∀ i < cnt, penumPtK 275 9 (mask 9) (275 * 9) false G G 3 cnt T PL POS SRT SRI i =
      true := fun i hi => CFSG.KS.BaseMask.penumSl_spec hsl (Nat.zero_le i) (by omega) hi
  obtain ⟨-, hE⟩ := penumK_left_sound (cap := 128) hsz hgk hhd hp
  have hEn : Enumerates (Subgroup.closure A) (penumRec 275 9 cnt T PL).tabs.toList := by
    refine enumerates_closure ?_ ?_ hE
    · intro u hu
      obtain ⟨j, hj, rfl⟩ := hmemA u hu
      refine ⟨j, by simpa [gens] using hj, ?_⟩
      rw [hgens_get j hj]
      exact (hG j hj).2
    · intro j hj
      have hj' : j < 3 := by simpa [gens] using hj
      refine ⟨_, ⟨⟨j, hj'⟩, rfl⟩, ?_⟩
      rw [hgens_get j hj']
      exact (hG j hj').2
  have hlen : (penumRec 275 9 cnt T PL).tabs.toList.length = cnt := by simp [penumRec]
  have hTc : ∀ i < cnt, canonK 275 9 (mask 9) (275 * 9) (T i) = true :=
    fun i hi => (CFSG.KS.MulH.penumPt_specH (hp i hi)).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEn.card, hlen, hcnt128]
  ·
    let r : Tab → Bool := fun t => decide (∀ j < 3, comp 275 t gens[j]! = comp 275 gens[j]! t)
    have hr : ∀ t z, TabRep t z → (r t = true ↔
        z ∈ Subgroup.centralizer (Subgroup.closure A : Set (Equiv.Perm (Fin 275)))) := by
      intro t z ht
      rw [mem_centralizer_closure_iff, decide_eq_true_iff]
      constructor
      · intro hc u hu
        obtain ⟨j, hj, rfl⟩ := hmemA u hu
        have hgj := (hG j hj).2
        rw [← hgens_get j hj] at hgj
        exact ((hgj.comp ht).eq_iff (ht.comp hgj)).1 (hc j hj).symm
      · intro hc j hj
        have hgj := (hG j hj).2
        rw [← hgens_get j hj] at hgj
        exact ((ht.comp hgj).eq_iff (hgj.comp ht)).2 (hc _ ⟨⟨j, hj⟩, rfl⟩).symm
    have hEc := hEn.filter r hr
    rw [inf_comm, hEc.card]
    have hrT : ∀ i < cnt, r (unpack 275 9 (T i)) = Nat.beq (nget CW i) 3 := by
      intro i hi
      have hci := hcw
      have hcwi := allN_spec hci i hi
      have hcomm : ∀ j < 3, (comp 275 (unpack 275 9 (T i)) gens[j]! =
          comp 275 gens[j]! (unpack 275 9 (T i)) ↔ commK (T i) (G j) = true) := by
        intro j hj
        rw [hgens_get j hj, comp_unpackA (hTc i hi) (hG j hj).1,
          comp_unpackA (hG j hj).1 (hTc i hi)]
        unfold commK
        constructor
        · intro e
          change Nat.beq (pcomp 275 9 (mask 9) (T i) (G j)) (pcomp 275 9 (mask 9) (G j) (T i)) =
            true
          rw [CFSG.KS.MulH.unpack_injH (CFSG.KC.BfsPin.canonK_pcomp (hTc i hi) (hG j hj).1)
            (CFSG.KC.BfsPin.canonK_pcomp (hG j hj).1 (hTc i hi)) e]
          exact Nat.beq_refl _
        · intro e
          change Nat.beq (pcomp 275 9 (mask 9) (T i) (G j)) (pcomp 275 9 (mask 9) (G j) (T i)) =
            true at e
          rw [Nat.eq_of_beq_eq_true e]
      unfold cwK at hcwi
      cases hc3 : Nat.beq (nget CW i) 3
      · rw [hc3] at hcwi
        obtain ⟨hlt, hnc⟩ := (bAnd_iff _ _).1 hcwi
        have hlt' : nget CW i < 3 := Nat.blt_eq.mp hlt
        have hnc' : commK (T i) (G (nget CW i)) = false := by
          cases e : commK (T i) (G (nget CW i))
          · rfl
          · rw [e] at hnc
            exact absurd hnc (by decide)
        simp only [r, decide_eq_false_iff_not]
        intro hall
        rw [(hcomm _ hlt').1 (hall _ hlt')] at hnc'
        exact absurd hnc' (by decide)
      · rw [hc3] at hcwi
        simp only [r, decide_eq_true_iff]
        intro j hj
        exact (hcomm j hj).2 (allN_spec hcwi j hj)
    simp only [penumRec]
    rw [cntK_ofFn (fun i => unpack 275 9 (T i)) r, cntK_congr hrT]
    exact Nat.eq_of_beq_eq_true hcnt
  ·
    intro u hu
    obtain ⟨j, hj, rfl⟩ := hmemA u hu
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hgen j hj)
    refine ⟨Fin.ext ?_, ((hG j hj).comm (hF 4 (by norm_num) (by norm_num))).1 h2⟩
    rw [← (hG j hj).pg ha]
    exact Nat.eq_of_beq_eq_true h1
  ·
    intro q hq
    have hm := allN_spec hmov q.val q.2
    have hqa : Nat.beq q.val a = false := by
      cases e : Nat.beq q.val a
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true e)) hq
    rw [hqa] at hm
    by_contra hfix
    push Not at hfix
    have hall : allN 3 (fun j => Nat.beq (pg 9 (mask 9) (G j) q.val) q.val) = true := by
      refine CFSG.KS.PackFld.allN_of_forall fun j hj => ?_
      rw [(hG j hj).pg q.2, hfix _ ⟨⟨j, hj⟩, rfl⟩]
      exact Nat.beq_refl _
    rw [hall] at hm
    exact absurd hm (by decide)
  ·
    rw [CFSG.KS.MulH.strictB_eq'', CFSG.KS.MulH.strictB_eq''] at hxy
    have pX := PR.word hF wx hx
    have pY := PR.word hF wy hy
    have p4 := hF 4 (by norm_num) (by norm_num)
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := (by simpa only [xyK, bAnd_iff] using hxy :
      Nat.beq (pg 9 (mask 9) (wK F wx) a) a = true ∧ Nat.beq (pg 9 (mask 9) (wK F wy) a) a = true ∧
      commK (wK F wx) (F 4) = true ∧ commK (wK F wy) (F 4) = true ∧
      Nat.beq (pwK 3 (wK F wx)) idK = true ∧ Nat.beq (pwK 3 (wK F wy)) idK = true ∧
      commK (wK F wx) (wK F wy) = true ∧ bIf(Nat.beq (wK F wx) idK, false, true) = true ∧
      bIf(Nat.beq (wK F wy) idK, false, true) = true ∧ bIf(Nat.beq (wK F wy) (wK F wx), false, true) = true ∧
      bIf(Nat.beq (wK F wy) (pcK (wK F wx) (wK F wx)), false, true) = true)
    have nb : ∀ {b : Bool}, bIf(b, false, true) = true → b = false := by
      intro b hb
      cases b
      · rfl
      · exact absurd hb (by decide)
    refine ⟨Fin.ext ?_, Fin.ext ?_, (pX.comm p4).1 e3, (pY.comm p4).1 e4, (pX.pow 3).beq PR.one |>.1 e5,
      (pY.pow 3).beq PR.one |>.1 e6, (pX.comm pY).1 e7, fun hh => ?_, fun hh => ?_, fun hh => ?_,
      fun hh => ?_⟩
    · rw [← pX.pg ha]
      exact Nat.eq_of_beq_eq_true e1
    · rw [← pY.pg ha]
      exact Nat.eq_of_beq_eq_true e2
    · have := (pX.beq PR.one).2 hh
      rw [nb e8] at this
      exact absurd this (by decide)
    · have := (pY.beq PR.one).2 hh
      rw [nb e9] at this
      exact absurd this (by decide)
    · have := (pY.beq pX).2 hh
      rw [nb e10] at this
      exact absurd this (by decide)
    · have := (pY.beq (pX.mul pX)).2 hh
      rw [nb e11] at this
      exact absurd this (by decide)
  ·
    obtain ⟨hl, hs⟩ := walksK_spec os pts hwalk
    refine ⟨hl, fun t ht => ?_, sortedK_spec pts hsort⟩
    have hm : os.getD t [] ∈ os := by
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem _
    rw [← walk_eq hF _ (hos _ hm) ha]
    exact hs t ht

end CFSG.KS.McLNine

end
