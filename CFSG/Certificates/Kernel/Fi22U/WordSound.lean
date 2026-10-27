module

public import Certificates.Data.Kernel.Fi22U.Restrict
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.Fi22U

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native Quiver.SchreierGraph

@[expose] def codesLt (j : Nat) (u : List Nat) : Prop := ∀ x ∈ u, x / 2 < j

theorem evalWord_flip {G S : Type*} [Group G] (ι : S → G) (w : List (S × Bool)) :
    evalWord ι (w.map fun x => (x.1, !x.2)).reverse = (evalWord ι w)⁻¹ := by
  induction w with
  | nil => simp
  | cons x w ih =>
    obtain ⟨s, b⟩ := x
    rw [List.map_cons, List.reverse_cons, evalWord_append, ih]
    cases b
    · rw [evalWord_cons_false]
      simp [evalWord_cons_true, evalWord_nil, mul_inv_rev]
    · rw [evalWord_cons_true]
      simp [evalWord_cons_false, evalWord_nil, mul_inv_rev]

theorem toLetters_wOf_cons {j x : Nat} (u : List Nat) (hx : x / 2 < j) :
    CFSG.Monster.B.Co2.toLetters j (wOf (x :: u)) =
      (⟨x / 2, hx⟩, decide (x % 2 = 0)) :: CFSG.Monster.B.Co2.toLetters j (wOf u) := by
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
  · have hl : wOf (x :: u) = ((x / 2 + 1 : Nat) : Int) :: wOf u := by simp [wOf, h0]
    rw [hl]
    simp only [CFSG.Monster.B.Co2.toLetters, List.filterMap_cons]
    rw [dif_pos (by simp; omega)]
    have e1 : ((x / 2 + 1 : Nat) : Int).natAbs - 1 = x / 2 := by
      rw [Int.natAbs_natCast]
      omega
    have e2 : decide (0 < ((x / 2 + 1 : Nat) : Int)) = decide (x % 2 = 0) := by
      simp only [h0, decide_true, decide_eq_true_eq]
      omega
    dsimp only
    congr 1
    exact Prod.ext (Fin.ext e1) e2
  · have hl : wOf (x :: u) = -((x / 2 + 1 : Nat) : Int) :: wOf u := by simp [wOf, h1]
    rw [hl]
    simp only [CFSG.Monster.B.Co2.toLetters, List.filterMap_cons]
    rw [dif_pos (by simp; omega)]
    have e1 : (-((x / 2 + 1 : Nat) : Int)).natAbs - 1 = x / 2 := by
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      omega
    have e2 : decide (0 < -((x / 2 + 1 : Nat) : Int)) = decide (x % 2 = 0) := by
      have : ¬ (0 < -((x / 2 + 1 : Nat) : Int)) := by omega
      simp only [this, decide_false, h1]
      decide
    dsimp only
    congr 1
    exact Prod.ext (Fin.ext e1) e2

theorem toLetters_append (j : Nat) (u v : List Nat) :
    CFSG.Monster.B.Co2.toLetters j (wOf (u ++ v)) =
      CFSG.Monster.B.Co2.toLetters j (wOf u) ++ CFSG.Monster.B.Co2.toLetters j (wOf v) := by
  simp [CFSG.Monster.B.Co2.toLetters, wOf, List.filterMap_append]

theorem toLetters_ninvC {j : Nat} : ∀ {u : List Nat}, codesLt j u →
    CFSG.Monster.B.Co2.toLetters j (wOf (ninvC u)) =
      ((CFSG.Monster.B.Co2.toLetters j (wOf u)).map fun x => (x.1, !x.2)).reverse
  | [], _ => rfl
  | x :: u, h => by
    have hx : x / 2 < j := h x List.mem_cons_self
    have hu : codesLt j u := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hf : flipC x / 2 < j := by
      unfold flipC
      split <;> omega
    have e1 : ninvC (x :: u) = ninvC u ++ [flipC x] := by simp [ninvC]
    have e2' : flipC x / 2 = x / 2 := by
      unfold flipC
      split <;> omega
    have e2 : (⟨flipC x / 2, hf⟩ : Fin j) = ⟨x / 2, hx⟩ := Fin.ext e2'
    have e3 : decide (flipC x % 2 = 0) = !decide (x % 2 = 0) := by
      by_cases hx2 : x % 2 = 0
      · have : flipC x % 2 ≠ 0 := by
          unfold flipC
          rw [if_pos hx2]
          omega
        simp [hx2, this]
      · have : flipC x % 2 = 0 := by
          unfold flipC
          rw [if_neg hx2]
          omega
        simp [hx2, this]
    have e4 : CFSG.Monster.B.Co2.toLetters j (wOf []) = [] := rfl
    rw [e1, toLetters_append, toLetters_ninvC hu, toLetters_wOf_cons [] hf, toLetters_wOf_cons u hx,
      e4, e2, e3]
    simp

theorem evalWord_ninvC {G : Type*} [Group G] {j : Nat} (ι : Fin j → G) {u : List Nat}
    (h : codesLt j u) :
    evalWord ι (CFSG.Monster.B.Co2.toLetters j (wOf (ninvC u))) =
      (evalWord ι (CFSG.Monster.B.Co2.toLetters j (wOf u)))⁻¹ := by
  rw [toLetters_ninvC h, evalWord_flip]

theorem mem_Gen_of_wordEqK {n w kS kO r : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {W : Array (List Int)} {wd : List Int} (hd : Orb.Hd n S base kO W)
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (h : CFSG.KS.Prim.wordEqK n w (mask w) (pidn n w) PS PSI kS wd r = true)
    {t : Array Nat} (ht : t = unpack n w r) {g : Equiv.Perm (Fin n)} (hg : Rep n t g) :
    g = evalWord (fun h : Fin kS => permOfArr n S[h.val]!)
        (CFSG.Monster.B.Co2.toLetters kS wd) ∧ g ∈ Orb.Gen n S kO := by
  obtain ⟨e, hl⟩ := CFSG.KS.Prim.wordEqK_sound hS hp h
  have hr := rep_wordA (gs := fun h => permOfArr n S[h]!) (j := kS)
    (fun h hh => Orb.rep_S hd (by rw [hS.1]; exact hh))
    (fun h hh => Orb.rep_Si hd (by rw [hS.1]; exact hh)) wd hl
  rw [e, ← ht] at hr
  have hge := Rep.unique hg hr
  refine ⟨hge, ?_⟩
  rw [hge]
  refine (Subgroup.closure_le _).2 ?_ (evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact Orb.S_mem_Gen hd h.val (by rw [hS.1]; exact h.2)

end CFSG.KC.Fi22U

end
