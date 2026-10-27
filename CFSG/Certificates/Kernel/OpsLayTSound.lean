module

public import Certificates.Data.Kernel.OpsLayT
public import CFSG.Certificates.Kernel.OpsLayKSnd
import CFSG.Certificates.Kernel.OpsMcertTSound

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsMT

theorem strictB_eqT (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem getRD_node (d : Nat) (l r : RT) (x i : Nat) : getRD d (.node l x r) i =
    if i = 0 then x else if i % 2 = 1 then getRD d l ((i - 1) / 2) else getRD d r ((i - 1) / 2) :=
  brec2 (α := Nat) i x _ _

theorem getRD_setR (d : Nat) : ∀ (T : RT) (t a r : Nat),
    getRD d (setR T t a) r = if domR T t = true ∧ r = t then a else getRD d T r
  | .leaf, _, _, _ => by simp [setR, domR, getRD]
  | .node l x rt, t, a, r => by
    rw [setR_node, domR_node]
    by_cases ht0 : t = 0
    · subst ht0
      rw [if_pos rfl, getRD_node, getRD_node]
      by_cases hr : r = 0 <;> simp [hr]
    · rw [if_neg ht0]
      by_cases ht : t % 2 = 1
      · rw [if_pos ht, if_pos ht, getRD_node, getRD_node, getRD_setR d l]
        by_cases hr0 : r = 0
        · simp [hr0, ht0, Ne.symm ht0]
        · by_cases hr : r % 2 = 1
          · simp only [hr0, hr, if_false, if_true]
            by_cases hd : domR l ((t - 1) / 2) = true
            · by_cases hrt : r = t
              · subst hrt
                simp [hd]
              · have : (r - 1) / 2 ≠ (t - 1) / 2 := by omega
                simp [hd, hrt, this]
            · simp [hd, ht0]
          · have : r ≠ t := by omega
            simp [hr0, hr, this]
      · rw [if_neg ht, if_neg ht, getRD_node, getRD_node, getRD_setR d rt]
        by_cases hr0 : r = 0
        · simp [hr0, Ne.symm ht0]
        · by_cases hr : r % 2 = 1
          · have : r ≠ t := by omega
            simp [hr0, hr, this]
          · simp only [hr0, hr, if_false]
            by_cases hd : domR rt ((t - 1) / 2) = true
            · by_cases hrt : r = t
              · subst hrt
                simp [hd]
              · have : (r - 1) / 2 ≠ (t - 1) / 2 := by omega
                simp [hd, hrt, this]
            · simp [hd, ht0]

theorem getRD_mkT (d : Nat) : ∀ (fuel n : Nat) (f : Nat → Nat), n ≤ fuel → ∀ r,
    getRD d (mkT fuel n f) r = if r < n then f r else d
  | 0, n, f, h, r => by
    have : n = 0 := by omega
    subst this
    rfl
  | fuel + 1, n, f, h, r => by
    have hm : mkT (fuel + 1) n f = if n = 0 then RT.leaf else
        RT.node (mkT fuel (n / 2) fun j => f (2 * j + 1)) (f 0)
          (mkT fuel ((n - 1) / 2) fun j => f (2 * j + 2)) :=
      brecE (α := RT) n 0 _ _
    rw [hm]
    by_cases hn : n = 0
    · subst hn
      simp [getRD]
    · rw [if_neg hn, getRD_node]
      have hl := getRD_mkT d fuel (n / 2) (fun j => f (2 * j + 1)) (by omega) ((r - 1) / 2)
      have hr := getRD_mkT d fuel ((n - 1) / 2) (fun j => f (2 * j + 2)) (by omega) ((r - 1) / 2)
      by_cases hr0 : r = 0
      · subst hr0
        simp [Nat.pos_of_ne_zero hn]
      · by_cases h2 : r % 2 = 1
        · simp only [hr0, h2, if_false, if_true, hl]
          have e : 2 * ((r - 1) / 2) + 1 = r := by omega
          rw [e]
          have : (r - 1) / 2 < n / 2 ↔ r < n := by omega
          simp only [this]
        · simp only [hr0, h2, if_false, hr]
          have e : 2 * ((r - 1) / 2) + 2 = r := by omega
          rw [e]
          have : (r - 1) / 2 < (n - 1) / 2 ↔ r < n := by omega
          simp only [this]

@[expose] noncomputable def stepLT (c : Lay) (T : RT) (o : Op) : RT :=
  setR T (Op.tgt o) (stepVG c (getRD c.ONE T) o)

theorem runCT_eq (c : Lay) : ∀ (prog : List Op) (T : RT) (k : RT → Bool),
    runCT c prog T k = k (prog.foldl (stepLT c) T)
  | [], _, _ => rfl
  | o :: prog, T, k => by
    change strictB (stepVG c (getRD c.ONE T) o)
      (fun v => setK T (Op.tgt o) v fun T' => runCT c prog T' k) = _
    rw [strictB_eqT, setK_eq, runCT_eq c prog]
    rfl

def InvD (d : Nat) (T : RT) (L : List Nat) : Prop :=
  (∀ r, getRD d T r = L.getD r d) ∧ ∀ r, domR T r = decide (r < L.length)

theorem getD_set (d : Nat) (L : List Nat) (t x r : Nat) :
    (L.set t x).getD r d = if t < L.length ∧ r = t then x else L.getD r d := by
  by_cases ht : t < L.length
  · by_cases hr : r = t
    · subst hr
      simp [List.getD_eq_getElem?_getD, ht]
    · rw [if_neg (fun h => hr h.2)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hr)]
  · rw [List.set_eq_of_length_le (by omega), if_neg (fun h => ht h.1)]

theorem stepVG_getR (c : Lay) (R : List Nat) (o : Op) : stepVG c (getR c R) o = stepV c R o := by
  cases o <;> rfl

theorem invD_run (c : Lay) : ∀ (prog : List Op) {T : RT} {L : List Nat}, InvD c.ONE T L →
    InvD c.ONE (prog.foldl (stepLT c) T) (Snd.runL c prog L)
  | [], _, _, h => h
  | o :: prog, T, L, h => by
    have hg : getRD c.ONE T = getR c L := funext h.1
    have h' : InvD c.ONE (stepLT c T o) (L.set (Op.tgt o) (stepV c L o)) := by
      refine ⟨fun r => ?_, fun r => ?_⟩
      · rw [stepLT, getRD_setR, getD_set, h.1 r, h.2, hg, stepVG_getR]
        simp
      · rw [stepLT, domR_setR, h.2 r, List.length_set]
    exact invD_run c prog h'

theorem invD_init (c : Lay) (A B n : Nat) : InvD c.ONE (initRT c A B n) (initR c A B n) := by
  refine ⟨fun r => ?_, fun r => ?_⟩
  · rw [initRT, getRD_mkT c.ONE n n _ (Nat.le_refl n) r]
    simp only [initR, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hr : r < n
    · rw [if_pos hr, List.getElem?_range hr]
      simp only [Option.map_some, Option.getD_some, initF, brecE]
    · rw [if_neg hr, List.getElem?_eq_none (by simpa using hr)]
      rfl
  · rw [initRT, (mkT_spec n n _ (Nat.le_refl n) r).2]
    simp [initR]

theorem regs_tree (c : Lay) (A B n : Nat) (prog : List Op) :
    getRD c.ONE (prog.foldl (stepLT c) (initRT c A B n)) =
      getR c (Snd.runL c prog (initR c A B n)) :=
  funext (invD_run c prog (invD_init c A B n)).1

theorem evalWLG_getR (c : Lay) (R : List Nat) : ∀ w : Word, evalWLG c (getR c R) w = evalWL c R w
  | [] => rfl
  | (r, e) :: w => by
    rw [evalWLG, evalWL, evalWLG_getR c R w]

theorem factLG_getR (c : Lay) (R : List Nat) (n : Nat) :
    factLG c (getR c R) n = factL c R n := by
  funext f
  cases f <;> simp only [factLG, factL, evalWLG_getR]

theorem mcertLT_eq (c : Lay) (A B : Nat) (C : MCert) : mcertLT c A B C = mcertL c A B C := by
  unfold mcertLT mcertL
  rw [runCT_eq, Snd.runC_eq, regs_tree]
  simp only [factLG_getR]

theorem seedsLT_eq (c : Lay) (A B : Nat) (C : MCert) (rA rB : Nat) :
    seedsLT c A B C rA rB = seedsL c A B C rA rB := by
  unfold seedsLT seedsL
  rw [runCT_eq, Snd.runC_eq, regs_tree]
  simp only [factLG_getR]

end CFSG.KC.OpsLayK

end
