module

public import Certificates.Data.Kernel.FixBoundK.Fix

public section

namespace CFSG.KC.FixBoundK

theorem fbkM_bAnd {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem fbkM_allS {α : Type} {f : α → Bool} {l : List α} (h : allS f l = true) :
    ∀ y ∈ l, f y = true := by
  induction l with
  | nil => intro y hy; cases hy
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := fbkM_bAnd h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact ih hxs y hy

theorem fbkM_lenS {α : Type} {l : List α} (h : lenS l = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons x xs => exact absurd h (Nat.succ_ne_zero _)

theorem memberK_spec {r : Nat} {F bs Mws : List Nat} {full A sF : Nat} {fs : List Nat}
    (h : memberK r F bs Mws full A sF fs = true) :
    A &&& full = A ∧ sF &&& (A ||| zS bs A full) = sF ∧
      dualS (appS Mws (selS F sF)) fs 0 = true ∧
      popS F A * 2 ^ r * 2048 * popS F (zS bs A full) ≤
        16384 * 2 ^ lenS (appS Mws (selS F sF)) := by
  obtain ⟨h1, h2⟩ := fbkM_bAnd h
  obtain ⟨h2, h3⟩ := fbkM_bAnd h2
  obtain ⟨h3, h4⟩ := fbkM_bAnd h3
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, Nat.le_of_ble_eq_true h4⟩

theorem omegaK_spec {r : Nat} {F Mws : List Nat} {full sF : Nat} {fs : List Nat}
    (h : omegaK r F Mws full sF fs = true) :
    sF &&& full = sF ∧ dualS (appS Mws (selS F sF)) fs 0 = true ∧
      2 * 2 ^ r * 2048 * lenS F ≤ 16384 * 2 ^ lenS (appS Mws (selS F sF)) := by
  obtain ⟨h1, h2⟩ := fbkM_bAnd h
  obtain ⟨h2, h3⟩ := fbkM_bAnd h2
  exact ⟨Nat.eq_of_beq_eq_true h1, h2, Nat.le_of_ble_eq_true h3⟩

theorem fixRep_spec {p : Rep} {gens : List (List Nat)} {x : FixD} (h : fixRep p gens x = true) :
    lenS gens = p.1 ∧ lenS x.1 + lenS x.2.2.1 = 12 ∧
      (∀ y ∈ appS x.1 x.2.2.1, synS y = 0) ∧ (∀ g ∈ gens, ∀ b ∈ x.1, fixS g b = true) ∧
      dualS x.1 x.2.1 0 = true ∧ spanChk x.1 p.2.1 0 = true ∧
      (∀ l ∈ x.2.2.2, ∀ f ∈ l, par24 f = 0) ∧ ysChk gens x.2.2.2 x.2.2.1 0 = true ∧
      mwsRem gens p.2.2.2.1 = [] ∧ basicsOK x.1 p.2.2.1 = true := by
  obtain ⟨h1, h2⟩ := fbkM_bAnd h
  obtain ⟨h2, h3⟩ := fbkM_bAnd h2
  obtain ⟨h3, h4⟩ := fbkM_bAnd h3
  obtain ⟨h4, h5⟩ := fbkM_bAnd h4
  obtain ⟨h5, h6⟩ := fbkM_bAnd h5
  obtain ⟨h6, h7⟩ := fbkM_bAnd h6
  obtain ⟨h7, h8⟩ := fbkM_bAnd h7
  obtain ⟨h8, h9⟩ := fbkM_bAnd h8
  obtain ⟨h9, h10⟩ := fbkM_bAnd h9
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    fun y hy => Nat.eq_of_beq_eq_true (fbkM_allS h3 y hy),
    fun g hg => fbkM_allS (fbkM_allS h4 g hg), h5, h6,
    fun l hl f hf => Nat.eq_of_beq_eq_true (fbkM_allS (fbkM_allS h7 l hl) f hf), h8,
    fbkM_lenS (Nat.eq_of_beq_eq_true h9), h10⟩

end CFSG.KC.FixBoundK

end
