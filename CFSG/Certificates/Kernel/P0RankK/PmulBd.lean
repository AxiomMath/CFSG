module

public import Certificates.Data.Kernel.P0VisBd
public import CFSG.Monster.B.TwoA.Sp8.P0RankLin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.P0Vis

open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank

abbrev Bd (x : ℕ × ℕ) : Prop := x.1 < 2 ^ 16 ∧ x.2 < 2 ^ 9

theorem bd_zero : Bd (0, 0) := ⟨Nat.two_pow_pos 16, Nat.two_pow_pos 9⟩

theorem bd_of_pairOK {p : ℕ × ℕ} (h : pairOK p = true) : Bd p := by
  rw [pairOK, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
  exact ⟨lt_of_lt_of_eq h.1 (by norm_num), lt_of_lt_of_eq h.2 (by norm_num)⟩

theorem getD_prop {α : Type} (P : α → Prop) {l : List α} {d : α} (hd : P d)
    (hl : ∀ x ∈ l, P x) (i : ℕ) : P (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hd
  | some x => exact hl x (List.mem_of_getElem? h)

theorem foldl_pres {α β : Type} (P : α → Prop) (f : α → β → α) :
    ∀ (l : List β) (a : α), (∀ a, ∀ b ∈ l, P a → P (f a b)) → P a → P (l.foldl f a)
  | [], _, _, ha => ha
  | b :: l, a, hf, ha => foldl_pres P f l (f a b)
      (fun a' b' hb' => hf a' b' (List.mem_cons_of_mem _ hb')) (hf a b List.mem_cons_self ha)

theorem foldr_pres {α β : Type} (P : α → Prop) (f : β → α → α) :
    ∀ (l : List β) (a : α), (∀ b ∈ l, ∀ a, P a → P (f b a)) → P a → P (l.foldr f a)
  | [], _, _, ha => ha
  | b :: l, a, hf, ha => hf b List.mem_cons_self _
      (foldr_pres P f l a (fun b' hb' => hf b' (List.mem_cons_of_mem _ hb')) ha)

section Range

variable {dat : Data} (h : bdOK dat = true)
include h

theorem bdOK_beta : ∀ i j, (dat.beta.getD i []).getD j 0 < 2 ^ 9 := by
  simp only [bdOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  intro i j
  refine getD_prop (fun r : List ℕ => r.getD j 0 < 2 ^ 9) (Nat.two_pow_pos 9) (fun r hr => ?_) i
  exact getD_prop (· < 2 ^ 9) (Nat.two_pow_pos 9) (fun e he => lt_of_lt_of_eq (h.1.1.1.1 r hr e he)
    (by norm_num)) j

theorem bdOK_uConjL : ∀ k j, Bd ((dat.uConjL.getD k []).getD j (0, 0)) := by
  simp only [bdOK, Bool.and_eq_true, List.all_eq_true] at h
  intro k j
  refine getD_prop (fun r : List (ℕ × ℕ) => Bd (r.getD j (0, 0))) (d := []) bd_zero
    (fun r hr => ?_) k
  exact getD_prop Bd bd_zero (fun p hp => bd_of_pairOK (h.1.1.1.2 r hr p hp)) j

theorem bdOK_uConjT : ∀ k, ∀ c ∈ dat.uConjT.getD k [], c < 2 ^ 9 := by
  simp only [bdOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  intro k
  exact getD_prop (fun r : List ℕ => ∀ c ∈ r, c < 2 ^ 9) (by simp)
    (fun r hr c hc => lt_of_lt_of_eq (h.1.1.2 r hr c hc) (by norm_num)) k

theorem bdOK_uSq : ∀ k, Bd (dat.uSq.getD k (0, 0)) := by
  simp only [bdOK, Bool.and_eq_true, List.all_eq_true] at h
  intro k
  exact getD_prop Bd bd_zero (fun p hp => bd_of_pairOK (h.1.2 p hp)) k

theorem bdOK_uComm : ∀ c k, Bd ((dat.uComm.getD c []).getD k (0, 0)) := by
  simp only [bdOK, Bool.and_eq_true, List.all_eq_true] at h
  intro c k
  refine getD_prop (fun r : List (ℕ × ℕ) => Bd (r.getD k (0, 0))) (d := []) bd_zero
    (fun r hr => ?_) c
  exact getD_prop Bd bd_zero (fun p hp => bd_of_pairOK (h.2 r hr p hp)) k

theorem gam_lt (s s' : ℕ) : gam dat.beta s s' < 2 ^ 9 := by
  unfold gam
  refine foldl_pres (· < 2 ^ 9) _ _ _ (fun acc j _ hacc => ?_) (Nat.two_pow_pos 9)
  split_ifs
  · refine foldl_pres (· < 2 ^ 9) _ _ _ (fun acc' i _ hacc' => ?_) hacc
    split_ifs
    · exact Nat.xor_lt_two_pow hacc' (bdOK_beta h i j)
    · exact hacc'
  · exact hacc

theorem lmul_bd {x y : ℕ × ℕ} (hx : Bd x) (hy : Bd y) : Bd (lmul dat.beta x y) :=
  ⟨Nat.xor_lt_two_pow hx.1 hy.1,
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx.2 hy.2) (gam_lt h _ _)⟩

theorem linv_bd {x : ℕ × ℕ} (hx : Bd x) : Bd (linv dat.beta x) :=
  ⟨hx.1, Nat.xor_lt_two_pow hx.2 (gam_lt h _ _)⟩

theorem conjk_bd (k : ℕ) {x : ℕ × ℕ} : Bd (conjk dat k x) := by
  unfold conjk
  refine foldl_pres Bd _ _ _ (fun acc j _ hacc => ?_)
    ⟨Nat.two_pow_pos 16, colsAct_lt (bdOK_uConjT h k) _⟩
  split_ifs
  · exact lmul_bd h hacc (bdOK_uConjL h k j)
  · exact hacc

theorem conjkap_bd (κ : ℕ) {x : ℕ × ℕ} (hx : Bd x) : Bd (conjkap dat κ x) := by
  unfold conjkap
  refine foldr_pres Bd _ _ _ (fun k _ y hy => ?_) hx
  split_ifs
  · exact conjk_bd h k
  · exact hy

theorem foldl_conjk_bd (l : List ℕ) {z : ℕ × ℕ} (hz : Bd z) :
    Bd (l.foldl (fun y c => conjk dat c y) z) :=
  foldl_pres Bd _ l z (fun _ c _ _ => conjk_bd h c) hz

theorem moveleftR_bd (k : ℕ) : ∀ l : List ℕ, Bd (moveleftR dat k l)
  | [] => by
    simp only [moveleftR]
    exact ⟨Nat.two_pow_pos 16, Nat.two_pow_pos 9⟩
  | c :: rest => by
    simp only [moveleftR]
    exact lmul_bd h (foldl_conjk_bd h rest (bdOK_uComm h c k)) (moveleftR_bd k rest)

theorem rmulU_bd {g : (ℕ × ℕ) × ℕ} (hg : Bd g.1) (hg2 : g.2 < 2 ^ 10) {k : ℕ} (hk : k < 10) :
    Bd (rmulU dat g k).1 ∧ (rmulU dat g k).2 < 2 ^ 10 := by
  have hpow : 2 ^ k < 2 ^ 10 := Nat.pow_lt_pow_right (by norm_num) hk
  simp only [rmulU]
  split_ifs
  · exact ⟨lmul_bd h hg (foldl_conjk_bd h _
      (lmul_bd h (conjk_bd h k) (bdOK_uSq h k))), Nat.xor_lt_two_pow hg2 hpow⟩
  · exact ⟨lmul_bd h hg (foldl_conjk_bd h _ (moveleftR_bd h k _)), Nat.or_lt_two_pow hg2 hpow⟩

theorem pmul_bd {g h' : (ℕ × ℕ) × ℕ} (hg : Bd g.1) (hh : Bd h'.1) (hg2 : g.2 < 2 ^ 10) :
    Bd (pmul dat g h').1 ∧ (pmul dat g h').2 < 2 ^ 10 := by
  unfold pmul
  refine foldl_pres (fun p : (ℕ × ℕ) × ℕ => Bd p.1 ∧ p.2 < 2 ^ 10) _ _ _
    (fun p k hk hp => rmulU_bd h hp.1 hp.2 (List.mem_range.1 (List.mem_filter.1 hk).1))
    ⟨lmul_bd h hg (conjkap_bd h _ hh), hg2⟩

end Range

end CFSG.KC.P0Vis

end
