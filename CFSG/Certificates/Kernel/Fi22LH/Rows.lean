module

public import CFSG.Certificates.Kernel.Fi22LH.Bits
public import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.Acc
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.TW CFSG.KS.Fi22L
  CFSG.KC.Enum

variable {D : LHData}

theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  by_cases e : a = b
  · rw [beq_true e, decide_eq_true e]
  · rw [beq_false e, decide_eq_false e]

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  by_cases e : a < b
  · rw [blt_true e, decide_eq_true e]
  · rw [blt_false e, decide_eq_false e]

theorem ent_al (hO : OrbOK) (h : LHChecks D) {x : Nat} (hx : x < 3510) :
    ap orbL.alpha x = ent D.al x ∧ ent D.al x < 3510 ∧ ent D.al (ent D.al x) = x := by
  obtain ⟨a1, -, -, -, a5, -, a7, -⟩ := hO.2.2.2.2 x hx
  rw [h.al]
  exact ⟨a1, a5, a7⟩

theorem ent_be (hO : OrbOK) (h : LHChecks D) {x : Nat} (hx : x < 3510) :
    ap orbL.beta x = ent D.be x ∧ ent D.be x < 3510 := by
  obtain ⟨-, a2, -, -, -, a6, -, -⟩ := hO.2.2.2.2 x hx
  rw [h.be]
  exact ⟨a2, a6⟩

theorem bi_spec (h : LHChecks D) {x : Nat} (hx : x < 3510) :
    ent D.bi x < 3510 ∧ ent D.be (ent D.bi x) = x := by
  have e := allN_iff.1 h.bi x hx
  rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
  exact e

theorem bi_surj (h : LHChecks D) {y : Nat} (hy : y < 3510) : ∃ x < 3510, ent D.bi x = y := by
  let f : Fin 3510 → Fin 3510 := fun x => ⟨ent D.bi x, (bi_spec h x.2).1⟩
  have hf : Function.Injective f := by
    intro a b e
    have e' : ent D.bi a = ent D.bi b := congrArg Fin.val e
    apply Fin.ext
    rw [← (bi_spec h a.2).2, ← (bi_spec h b.2).2, e']
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hf ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Fin.val hx⟩

theorem bi_be (hO : OrbOK) (h : LHChecks D) {y : Nat} (hy : y < 3510) :
    ent D.bi (ent D.be y) = y := by
  obtain ⟨x, hx, rfl⟩ := bi_surj h hy
  rw [(bi_spec h hx).2]

theorem ent_be_inj (hO : OrbOK) (h : LHChecks D) {x y : Nat} (hx : x < 3510) (hy : y < 3510)
    (e : ent D.be x = ent D.be y) : x = y := by
  rw [← bi_be hO h hx, ← bi_be hO h hy, e]

theorem ent_bi_inj (h : LHChecks D) {x y : Nat} (hx : x < 3510) (hy : y < 3510)
    (e : ent D.bi x = ent D.bi y) : x = y := by
  rw [← (bi_spec h hx).2, ← (bi_spec h hy).2, e]

theorem tall_at (h : LHChecks D) {k : Nat} (hk : k < 3510) :
    bIf(Nat.beq k (nat_lit 0), Nat.beq (D.R (nat_lit 0)) D.al,
      rowK D.R D.al D.be D.bi D.op D.ol k) = true := by
  have hs := h.tall (k / 135) (by omega)
  unfold tallSl at hs
  have := allN_iff.1 hs (k % 135) (Nat.mod_lt _ (by decide))
  rw [strictB_eq] at this
  have e : Nat.add (Nat.mul (nat_lit 135) (k / 135)) (k % 135) = k := by
    change 135 * (k / 135) + k % 135 = k
    omega
  rw [e] at this
  exact this

theorem row_zero (h : LHChecks D) : D.R 0 = D.al := by
  have := tall_at h (k := 0) (by decide)
  rw [beq_true rfl] at this
  exact Nat.eq_of_beq_eq_true this

theorem row_succ (h : LHChecks D) {k : Nat} (hk : k < 3510) (hk0 : 0 < k) :
    ent D.op k < k ∧ ∀ x < 3510, ent (D.R k) x =
      if ent D.ol k = 1 then ent D.al (ent (D.R (ent D.op k)) (ent D.al x))
      else ent D.be (ent (D.R (ent D.op k)) (ent D.bi x)) := by
  have := tall_at h hk
  rw [beq_false (show k ≠ 0 by omega)] at this
  change rowK D.R D.al D.be D.bi D.op D.ol k = true at this
  unfold rowK at this
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, strictB_eq, strictB_eq, strictB_eq,
    strictB_eq] at this
  obtain ⟨hp, hall⟩ := this
  refine ⟨hp, fun x hx => ?_⟩
  have e := Nat.eq_of_beq_eq_true (allN_iff.1 hall x hx)
  rw [e]
  by_cases hl : ent D.ol k = 1
  · rw [if_pos hl, beq_true hl]
  · rw [if_neg hl, beq_false hl]

theorem tr_congr {n : Nat} {t : Table} {f g : Nat → Nat} (h : TR n t f) (hfg : ∀ i < n, f i = g i) :
    TR n t g :=
  ⟨h.1, fun i hi => by rw [← hfg i hi]; exact h.2 i hi⟩

theorem compT_TR' {n : Nat} {P Q : Table} {f g : Nat → Nat} (hP : TR n P f) (hQ : TR n Q g) :
    TR n (compT n P Q) fun x => f (g x) := by
  refine ⟨by simp [compT], fun i hi => ?_⟩
  obtain ⟨hq1, hq2⟩ := hQ.2 i hi
  obtain ⟨hp1, hp2⟩ := hP.2 _ hq2
  refine ⟨?_, hp2⟩
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have e : (Q[i]!).toNat = g i := hq1
  rw [e]
  exact hp1

theorem alpha_TR (hO : OrbOK) (h : LHChecks D) : TR 3510 orbL.alpha (ent D.al) :=
  ⟨hO.1, fun i hi => ⟨(ent_al hO h hi).1, (ent_al hO h hi).2.1⟩⟩

theorem beta_TR (hO : OrbOK) (h : LHChecks D) : TR 3510 orbL.beta (ent D.be) :=
  ⟨hO.2.1, fun i hi => ⟨(ent_be hO h hi).1, (ent_be hO h hi).2⟩⟩

theorem genTables_neg2 : genTables orbL (-2) = invT 3510 orbL.beta := by
  unfold genTables
  simp

theorem binv_TR (hO : OrbOK) (h : LHChecks D) : TR 3510 (genTables orbL (-2)) (ent D.bi) := by
  rw [genTables_neg2]
  exact invT_TR (by decide) (beta_TR hO h) fun i hi =>
    ⟨(bi_spec h hi).1, (bi_spec h hi).2, bi_be hO h hi⟩

theorem tauAll_size : (tauAll orbL).size = 3510 := by
  simp [tauAll]

theorem tauAll_get {k : Nat} (hk : k < 3510) : (tauAll orbL)[k]! = tabOf orbL k := by
  unfold tauAll
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem cTab_TR (hO : OrbOK) (h : LHChecks D) :
    ∀ k < 3510, TR 3510 (cTab orbL (genTables orbL (-2)) k) (ent (D.R k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [cTab, dif_neg (by omega), row_zero h]
      exact alpha_TR hO h
    · obtain ⟨-, -, a3, a4, -, -, -, a8⟩ := hO.2.2.2.2 k hk
      obtain ⟨hp, -⟩ := a8 hk0
      have hpar : ap orbL.par k = ent D.op k := by rw [a3, h.op]
      have hlab : ap orbL.lab k = ent D.ol k := by rw [a4, h.ol]
      rw [← h.op] at hp
      obtain ⟨-, hrow⟩ := row_succ h hk hk0
      have ihp := ih (ent D.op k) hp (by omega)
      rw [cTab, dif_pos ⟨hk0, by rw [hpar]; exact hp⟩, hpar, hlab]
      by_cases hl : ent D.ol k = 1
      · rw [if_pos (by rw [hl]; rfl)]
        refine tr_congr (compT_TR' (compT_TR' (alpha_TR hO h) ihp) (alpha_TR hO h)) ?_
        intro x hx
        rw [hrow x hx, if_pos hl]
      · rw [if_neg (by intro e; exact hl (beq_iff_eq.1 e))]
        refine tr_congr (compT_TR' (compT_TR' (beta_TR hO h) ihp) (binv_TR hO h)) ?_
        intro x hx
        rw [hrow x hx, if_neg hl]

theorem tauAll_TR (hO : OrbOK) (h : LHChecks D) :
    ∀ k < 3510, TR 3510 (tauAll orbL)[k]! (ent (D.R k)) := by
  intro k hk
  rw [tauAll_get hk]
  exact cTab_TR hO h k hk

theorem row_lt (hO : OrbOK) (h : LHChecks D) {k x : Nat} (hk : k < 3510) (hx : x < 3510) :
    ent (D.R k) x < 3510 :=
  ((tauAll_TR hO h k hk).2 x hx).2

theorem row_inj (hO : OrbOK) (h : LHChecks D) {k x y : Nat} (hk : k < 3510) (hx : x < 3510)
    (hy : y < 3510) (e : ent (D.R k) x = ent (D.R k) y) : x = y := by
  induction k using Nat.strong_induction_on generalizing x y with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [row_zero h] at e
      rw [← (ent_al hO h hx).2.2, ← (ent_al hO h hy).2.2, e]
    · obtain ⟨hp, hrow⟩ := row_succ h hk hk0
      rw [hrow x hx, hrow y hy] at e
      by_cases hl : ent D.ol k = 1
      · rw [if_pos hl, if_pos hl] at e
        have ha := (ent_al hO h hx).2.1
        have hb := (ent_al hO h hy).2.1
        have e1 : ent (D.R (ent D.op k)) (ent D.al x) = ent (D.R (ent D.op k)) (ent D.al y) := by
          rw [← (ent_al hO h (row_lt hO h (by omega) ha)).2.2,
            ← (ent_al hO h (row_lt hO h (by omega) hb)).2.2, e]
        have e2 := ih _ hp (by omega) ha hb e1
        rw [← (ent_al hO h hx).2.2, ← (ent_al hO h hy).2.2, e2]
      · rw [if_neg hl, if_neg hl] at e
        have ha := (bi_spec h hx).1
        have hb := (bi_spec h hy).1
        have e1 := ent_be_inj hO h (row_lt hO h (by omega) ha) (row_lt hO h (by omega) hb) e
        exact ent_bi_inj h hx hy (ih _ hp (by omega) ha hb e1)

theorem Z_testBit (h : LHChecks D) {k : Nat} (hk : k < 3510) (x : Nat) :
    (D.Z k).testBit x = (decide (x < 3510) && decide (ent (D.R k) x = x)) := by
  have hs := h.fix (k / 585) (by omega)
  unfold fixSl at hs
  have := allN_iff.1 hs (k % 585) (Nat.mod_lt _ (by decide))
  rw [strictB_eq] at this
  have e : Nat.add (Nat.mul (nat_lit 585) (k / 585)) (k % 585) = k := by
    change 585 * (k / 585) + k % 585 = k
    omega
  rw [e, strictB_eq] at this
  rw [Nat.eq_of_beq_eq_true this, testBit_bsP_zero (by decide), beq_dec]

theorem commBits_eq (hO : OrbOK) (h : LHChecks D) :
    commBits (tauAll orbL) = Array.ofFn (n := 3510) fun k => bitsOfNat (D.Z k.val) := by
  unfold commBits
  apply Array.ext (by rw [Array.size_ofFn, Array.size_ofFn])
  intro c h1 h2
  have hc : c < 3510 := by rw [Array.size_ofFn] at h1; exact h1
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  have hT := tauAll_TR hO h c hc
  refine BitsIs.eq_bitsOfNat (bitsIs_fold (fun x => ap (tauAll orbL)[c]! x == x) (fun x => x)
    3510 fun x hx _ => by omega) fun y hy => ?_
  rw [Z_testBit h hc]
  constructor
  · rintro ⟨x, hx, h1, rfl⟩
    rw [beq_iff_eq, (hT.2 x hx).1] at h1
    simp [hx, h1]
  · intro e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    refine ⟨y, e.1, ?_, rfl⟩
    rw [beq_iff_eq, (hT.2 y e.1).1]
    exact e.2

end CFSG.KS.Fi22LH
