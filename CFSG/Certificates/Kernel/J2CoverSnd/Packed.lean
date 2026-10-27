
module

public import Certificates.Data.Kernel.J2Cover
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalNative
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Child3Inv
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.SiftEq

public section

namespace CFSG.KC.J2Cover.Snd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover

theorem pcomp_assoc' {n w p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem pcomp_id' {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) p (pidn n w) = p ∧ pcomp n w (mask w) (pidn n w) p = p := by
  obtain ⟨hn, hw, hp0, hpr⟩ := PF.canon_facts hp
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine ⟨PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_,
    PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_⟩
  · rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi]
  · rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw (hpr i hi)]

private theorem canon_pidn {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    canonK n w (mask w) (n * w) (pidn n w) = true :=
  canonK_of hn hw (PF.pidn_shr hn hw) fun i hi => by rw [PF.pg_pidn hn hw hi]; exact hi

private theorem prodK_nil (n w : Nat) : prodK n w [] = pidn n w := rfl

private theorem prodK_cons (n w X : Nat) (ws : List Nat) :
    prodK n w (X :: ws) = pcomp n w (mask w) X (prodK n w ws) := rfl

private theorem ppow_zero (n w m idn p : Nat) : ppow n w m idn p 0 = idn := rfl

private theorem ppow_succ (n w m idn p k : Nat) :
    ppow n w m idn p (k + 1) = pcomp n w m p (ppow n w m idn p k) := by
  show strictN (ppow n w m idn p k) (fun q => pcomp n w m p q) = _
  rw [PF.strictN_eqP]

private theorem canon_prodK {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    ∀ ws : List Nat, (∀ X ∈ ws, canonK n w (mask w) (n * w) X = true) →
      canonK n w (mask w) (n * w) (prodK n w ws) = true
  | [], _ => canon_pidn hn hw
  | X :: ws, hc => by
    rw [prodK_cons]
    exact canon_pcomp (hc X (by simp))
      (canon_prodK hn hw ws fun Y hY => hc Y (by simp [hY]))

private theorem canon_ppow {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {P : Nat}
    (hP : canonK n w (mask w) (n * w) P = true) :
    ∀ e, canonK n w (mask w) (n * w) (ppow n w (mask w) (pidn n w) P e) = true
  | 0 => by rw [ppow_zero]; exact canon_pidn hn hw
  | e + 1 => by rw [ppow_succ]; exact canon_pcomp hP (canon_ppow hn hw hP e)

private theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem rec_divParts (m : Nat) (g : Nat → Bool) : ∀ k : Nat,
    Nat.rec (motive := fun _ => Bool) true
      (fun d ih => Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) true
          (Bool.rec (motive := fun _ => Bool) true false (g (Nat.div m d)))
          (Bool.rec (motive := fun _ => Bool) false (Nat.beq (Nat.mod m d) 0) (Nat.blt 1 d)))
        ih) k =
    (((List.range k).filter fun d => 1 < d && m % d == 0).map (m / ·)).all fun e => !g e := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.all_append, ← ih]
    have e1 : Nat.blt 1 k = decide (1 < k) := Bool.eq_iff_iff.2 (by simp [Nat.blt_eq])
    have e2 : Nat.beq (Nat.mod m k) 0 = (m % k == 0) :=
      Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq]; exact Iff.rfl)
    show Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) true
          (Bool.rec (motive := fun _ => Bool) true false (g (Nat.div m k)))
          (Bool.rec (motive := fun _ => Bool) false (Nat.beq (Nat.mod m k) 0) (Nat.blt 1 k)))
        (Nat.rec (motive := fun _ => Bool) true _ k) = _
    rw [e1, e2]
    generalize (Nat.rec (motive := fun _ => Bool) true _ k) = a
    cases a <;> by_cases h1 : 1 < k <;> by_cases h2 : m % k = 0 <;>
      simp [h1, h2, List.filter_cons, beq_iff_eq, Bool.beq_eq_decide_eq] <;>
      cases g (m / k) <;> rfl

private theorem ordPK_eq (n w m X : Nat) :
    ordPK n w m X = (Nat.beq (ppow n w (mask w) (pidn n w) X m) (pidn n w) &&
      (divParts m).all fun e => !Nat.beq (ppow n w (mask w) (pidn n w) X e) (pidn n w)) := by
  have h := rec_divParts m (fun e => Nat.beq (ppow n w (mask w) (pidn n w) X e) (pidn n w))
    (m + 1)
  unfold ordPK
  rw [bAnd_eq]
  congr 1

private theorem apW_cons (t : Table) (l : List Table) (i : Nat) :
    apW (t :: l) i = ap t (apW l i) := rfl

private theorem apPowW_succ (W : List Table) (e i : Nat) :
    apPowW W (e + 1) i = apW W (apPowW W e i) := rfl

private theorem apW_prodK {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    ∀ ws : List Nat, (∀ X ∈ ws, canonK n w (mask w) (n * w) X = true) →
      ∀ i < n, apW (ws.map (tabP n w)) i = pg w (mask w) (prodK n w ws) i
  | [], _, i, hi => by
    have e : apW (([] : List Nat).map (tabP n w)) i = i := rfl
    rw [e, prodK_nil, PF.pg_pidn hn hw hi]
  | X :: ws, hc, i, hi => by
    have hX := hc X (by simp)
    have hws : ∀ Y ∈ ws, canonK n w (mask w) (n * w) Y = true := fun Y hY => hc Y (by simp [hY])
    have hP := (PF.canon_facts (canon_prodK hn hw ws hws)).2.2.2
    have hXr := (PF.canon_facts hX).2.2.2
    have hn32 : n < 2 ^ 32 := by omega
    rw [List.map_cons, apW_cons, apW_prodK hn hw ws hws i hi, prodK_cons, PF.pg_pcomp hn32 hi]
    exact ap_tabP (hP i hi) (Nat.lt_trans (hXr _ (hP i hi)) hn32)

private theorem apPowW_ppow {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {ws : List Nat}
    (hc : ∀ X ∈ ws, canonK n w (mask w) (n * w) X = true) :
    ∀ e, ∀ i < n, apPowW (ws.map (tabP n w)) e i =
      pg w (mask w) (ppow n w (mask w) (pidn n w) (prodK n w ws) e) i
  | 0, i, hi => by
    have e : apPowW (ws.map (tabP n w)) 0 i = i := rfl
    rw [e, ppow_zero, PF.pg_pidn hn hw hi]
  | e + 1, i, hi => by
    have hP := canon_prodK hn hw ws hc
    have hE := (PF.canon_facts (canon_ppow hn hw hP e)).2.2.2
    have hn32 : n < 2 ^ 32 := by omega
    rw [apPowW_succ, apPowW_ppow hn hw hc e i hi, apW_prodK hn hw ws hc _ (hE i hi), ppow_succ,
      PF.pg_pcomp hn32 hi]

private theorem powFixW_prodK {n w : Nat} {ws : List Nat} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (hc : ∀ X ∈ ws, canonK n w (mask w) (n * w) X = true) (e : Nat) :
    powFixW n (ws.map (tabP n w)) e =
      Nat.beq (ppow n w (mask w) (pidn n w) (prodK n w ws) e) (pidn n w) := by
  have hw0 := PF.w_pos hw
  have hE := canon_ppow hn hw (canon_prodK hn hw ws hc) e
  obtain ⟨-, -, hE0, -⟩ := PF.canon_facts hE
  rw [Bool.eq_iff_iff, powFixW, CFSG.Sporadic.Th.allIn_eq_true, Nat.beq_eq]
  constructor
  · intro H
    refine PF.eq_of_fields hw0 hE0 (PF.pidn_shr hn hw) fun i hi => ?_
    have := H i (Nat.zero_le _) hi
    rw [apPowW_ppow hn hw hc e i hi, beq_iff_eq] at this
    rw [this, PF.pg_pidn hn hw hi]
  · intro H i _ hi
    rw [apPowW_ppow hn hw hc e i hi, beq_iff_eq, H, PF.pg_pidn hn hw hi]

theorem ordW_unpack' {n w m : Nat} {ws : List Nat} (hm : 0 < m) (hne : ws ≠ [])
    (hc : ∀ X ∈ ws, canonK n w (mask w) (n * w) X = true) :
    ordW n (ws.map fun X => arrTable n (unpack n w X)) m = ordPK n w m (prodK n w ws) := by
  obtain ⟨X0, hX0⟩ := List.exists_mem_of_ne_nil ws hne
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts (hc X0 hX0)
  rw [ordPK_eq]
  change (powFixW n (ws.map (tabP n w)) m &&
    (divParts m).all (fun e => !powFixW n (ws.map (tabP n w)) e)) = _
  simp only [powFixW_prodK hn hw hc]

private theorem four_bool (a b c : Bool) (h : c = true → b = true) :
    (a && (!b && !c)) = Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) true false b) a := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem ordPK_four {n w R : Nat} (hR : canonK n w (mask w) (n * w) R = true) :
    ordPK n w 4 R = ord4K n w R := by
  have hR2 := canon_pcomp hR hR
  have p1 : ppow n w (mask w) (pidn n w) R 1 = R := by
    rw [ppow_succ, ppow_zero]
    exact (pcomp_id' hR).1
  have p2 : ppow n w (mask w) (pidn n w) R 2 = pcomp n w (mask w) R R := by
    rw [ppow_succ, p1]
  have p3 : ppow n w (mask w) (pidn n w) R 3 = pcomp n w (mask w) R (pcomp n w (mask w) R R) :=
    (ppow_succ n w (mask w) (pidn n w) R 2).trans (by rw [p2])
  have p4 : ppow n w (mask w) (pidn n w) R 4 =
      pcomp n w (mask w) (pcomp n w (mask w) R R) (pcomp n w (mask w) R R) :=
    (ppow_succ n w (mask w) (pidn n w) R 3).trans (by rw [p3, pcomp_assoc' hR hR hR2])
  have hcb : Nat.beq R (pidn n w) = true → Nat.beq (pcomp n w (mask w) R R) (pidn n w) = true := by
    intro h
    have e : R = pidn n w := Nat.eq_of_beq_eq_true h
    have := (pcomp_id' hR).1
    rw [e] at this ⊢
    rw [this]
    exact Nat.beq_refl _
  have hdp : divParts 4 = [2, 1] := by decide
  rw [ordPK_eq, p4, hdp]
  simp only [List.all_cons, List.all_nil, Bool.and_true, p1, p2]
  unfold ord4K
  rw [PF.strictB_eqP]
  exact four_bool _ _ _ hcb

theorem ord4_unpack' {n w R : Nat} (hR : canonK n w (mask w) (n * w) R = true) :
    ordTest n 4 (arrTable n (unpack n w R)) = ord4K n w R := by
  have h := ordW_unpack' (n := n) (w := w) (m := 4) (ws := [R]) (by decide) (by simp)
    (by simpa using hR)
  have e : prodK n w [R] = R := (pcomp_id' hR).1
  rw [e] at h
  exact h.trans (ordPK_four hR)

private theorem tblEq_tabP {n w A B : Nat} (hA : canonK n w (mask w) (n * w) A = true)
    (hB : canonK n w (mask w) (n * w) B = true) :
    tblEq n (tabP n w A) (tabP n w B) = Nat.beq A B := by
  obtain ⟨hn, hw, hA0, hAr⟩ := PF.canon_facts hA
  obtain ⟨-, -, hB0, hBr⟩ := PF.canon_facts hB
  have hapA : ∀ i < n, ap (tabP n w A) i = pg w (mask w) A i :=
    fun i hi => ap_tabP hi (by have := hAr i hi; omega)
  have hapB : ∀ i < n, ap (tabP n w B) i = pg w (mask w) B i :=
    fun i hi => ap_tabP hi (by have := hBr i hi; omega)
  rw [Bool.eq_iff_iff, tblEq, CFSG.Sporadic.Th.allIn_eq_true, Nat.beq_eq]
  constructor
  · intro H
    refine PF.eq_of_fields (PF.w_pos hw) hA0 hB0 fun i hi => ?_
    have := H i (Nat.zero_le _) hi
    rwa [hapA i hi, hapB i hi, beq_iff_eq] at this
  · intro H i _ hi
    subst H
    exact beq_self_eq_true _

theorem commT_unpack' {n w X Y : Nat} (hX : canonK n w (mask w) (n * w) X = true)
    (hY : canonK n w (mask w) (n * w) Y = true) :
    commT n (arrTable n (unpack n w X)) (arrTable n (unpack n w Y)) =
      Nat.beq (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X) := by
  have hn32 : n < 2 ^ 32 := by have := (PF.canon_facts hX).1; omega
  show tblEq n (compT n (tabP n w X) (tabP n w Y)) (compT n (tabP n w Y) (tabP n w X)) = _
  rw [compT_tabP hn32 (PF.canon_facts hY).2.2.2, compT_tabP hn32 (PF.canon_facts hX).2.2.2]
  exact tblEq_tabP (canon_pcomp hX hY) (canon_pcomp hY hX)

private theorem countP_range_fixK (a : Nat → Nat) : ∀ k : Nat,
    ((List.range k).countP fun i => a i == i) =
      Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
          (Nat.beq (a i) i))) k
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_fixK a k, List.countP_singleton]
    show _ = Nat.add _ (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (a k) k))
    have e : (a k == k) = Nat.beq (a k) k := Bool.eq_iff_iff.2 (by rw [beq_iff_eq, Nat.beq_eq])
    rw [e]
    cases Nat.beq (a k) k <;> rfl

theorem tblFix_unpack' {X : Nat} (hX : canonK 315 9 (mask 9) (315 * 9) X = true) :
    CFSG.ComponentClassification.J2Cover.External.tblFix (arrTable 315 (unpack 315 9 X)) =
      CFSG.KC.Misc.ArrEnum.fixK 315 9 X := by
  obtain ⟨-, -, -, hXr⟩ := PF.canon_facts hX
  have hap : ∀ i < 315, ap (arrTable 315 (unpack 315 9 X)) i = pg 9 (mask 9) X i :=
    fun i hi => ap_tabP hi (by have := hXr i hi; omega)
  unfold CFSG.ComponentClassification.J2Cover.External.tblFix CFSG.KC.Misc.ArrEnum.fixK
  refine Eq.trans ?_ (countP_range_fixK (fun i => pg 9 (mask 9) X i) 315)
  apply List.countP_congr
  intro i hi
  show (ap (arrTable 315 (unpack 315 9 X)) i == i) = true ↔ (pg 9 (mask 9) X i == i) = true
  rw [hap i (List.mem_range.1 hi)]

private theorem cntL_eq (f : Nat → Bool) : ∀ M : List Nat, cntL f M = M.countP f
  | [] => rfl
  | x :: M => by
    show strictN (cntL f M) (fun c => Bool.rec (motive := fun _ => Nat) c (Nat.succ c) (f x)) = _
    rw [PF.strictN_eqP, cntL_eq f M, List.countP_cons]
    cases f x <;> rfl

private theorem pairCntK_eq (rk : Nat → Nat → Bool) (M : List Nat) : ∀ L : List Nat,
    pairCntK L M rk = (L.map fun x => M.countP (rk x)).sum
  | [] => rfl
  | x :: L => by
    show strictN (pairCntK L M rk) (fun c => Nat.add c (cntL (rk x) M)) = _
    rw [PF.strictN_eqP, pairCntK_eq rk M L, cntL_eq, List.map_cons, List.sum_cons]
    exact Nat.add_comm _ _

private theorem foldl_add_sum {α : Type} (g : α → Nat) : ∀ (L : List α) (a : Nat),
    L.foldl (fun c x => c + g x) a = a + (L.map g).sum
  | [], a => by simp
  | x :: L, a => by
    rw [List.foldl_cons, foldl_add_sum g L, List.map_cons, List.sum_cons]
    omega

theorem pairCount_map' {n w : Nat} {L M : List Nat} {r : Table → Table → Bool}
    {rk : Nat → Nat → Bool}
    (h : ∀ x ∈ L, ∀ y ∈ M, r (arrTable n (unpack n w x)) (arrTable n (unpack n w y)) = rk x y) :
    pairCount (L.map fun X => arrTable n (unpack n w X)) (M.map fun X => arrTable n (unpack n w X))
      r = pairCntK L M rk := by
  unfold pairCount
  rw [foldl_add_sum (fun x => (M.map fun X => arrTable n (unpack n w X)).countP (r x)),
    pairCntK_eq, Nat.zero_add, List.map_map]
  congr 1
  refine List.map_congr_left fun x hx => ?_
  simp only [Function.comp_apply]
  rw [List.countP_map]
  refine List.countP_congr fun y hy => ?_
  simp only [Function.comp_apply, h x hx y hy]

theorem siftK_eq' {n w kS nb BP G : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hG : canonK n w (mask w) (n * w) G = true) :
    siftA n (rawLevels n S base) base 0 (unpack n w G) =
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G := by
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 hG
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  exact CFSG.KS.Raw.siftK_eq hb hp hl rfl (Nat.eq_of_beq_eq_true h3) h4

end CFSG.KC.J2Cover.Snd

end
