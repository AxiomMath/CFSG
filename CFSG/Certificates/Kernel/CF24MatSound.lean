module

public import Certificates.Data.Kernel.CF24Mat
public import CFSG.Certificates.Kernel.McLMultSound

public section

namespace CFSG.KC.CF24M

open CFSG.F3.Native CFSG.KS.F3L CFSG.KS.F3R CFSG.KC.Enum CFSG.KC.McLMult

theorem abL4_eq (A Ai B Bi : V) (z : Int) :
    abL4 A Ai B Bi z = if z = 1 then A else if z = -1 then Ai else if z = 2 then B else Bi := by
  rcases z with (_ | _ | _ | k) | (_ | k)
  · rfl
  · rfl
  · rfl
  · change Bi = _
    rw [Int.ofNat_eq_coe, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rfl
  · change Bi = _
    rw [Int.negSucc_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem abK4_unlane {d : Nat} (hd : 0 < d) {I A Ai B Bi : V} (hI : IdL d I) (f : Int → Array V)
    (hf : ∀ z, f z = unlane d (abL4 A Ai B Bi z)) (w : List Int) :
    w.foldr (fun l X => mul d (f l) X) (idM d) = unlane d (abK4 d (spreadE d d) I A Ai B Bi w) := by
  induction w with
  | nil => exact hI.eq
  | cons z w ih =>
    rw [List.foldr_cons, ih, hf, mul_unlane hd]
    change _ = unlane d (mulL d (spreadE d d) (abL4 A Ai B Bi z) (abK4 d (spreadE d d) I A Ai B Bi w))
    rw [mulL_eq]

theorem evalKn_unlane {d m : Nat} (hd : 0 < d) {I : V} (hI : IdL d I) {X Xi : Nat → V}
    {E Ei : Nat → Array V} (hE : ∀ k < m, E k = unlane d (X k))
    (hEi : ∀ k < m, Ei k = unlane d (Xi k)) (w : List (Fin m × Bool)) :
    w.foldr (fun l Y => mul d (if l.2 then E l.1.val else Ei l.1.val) Y) (idM d) =
      unlane d (evalKn d (spreadE d d) I X Xi w) := by
  induction w with
  | nil => exact hI.eq
  | cons l w ih =>
    obtain ⟨⟨i, hi⟩, b⟩ := l
    rw [List.foldr_cons, ih]
    cases b
    · rw [if_neg Bool.false_ne_true, hEi i hi, mul_unlane hd]
      change _ = unlane d (mulL d (spreadE d d) (Xi i) (evalKn d (spreadE d d) I X Xi w))
      rw [mulL_eq]
    · rw [if_pos rfl, hE i hi, mul_unlane hd]
      change _ = unlane d (mulL d (spreadE d d) (X i) (evalKn d (spreadE d d) I X Xi w))
      rw [mulL_eq]

theorem allK_iff {α : Type} (L : List α) (f : α → Bool) : allK L f = true ↔ ∀ a ∈ L, f a = true := by
  induction L with
  | nil => simp [allK]
  | cons a L ih =>
    change bAnd(f a, allK L f) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change bAnd(f n, allN n f) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · exact fun h => ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem invPairK_spec {d E : Nat} {I X Xi : V} (h : invPairK d E I X Xi = true) :
    Canon d X ∧ Canon d Xi ∧ mulL d E X Xi = I ∧ mulL d E Xi X = I := by
  unfold invPairK at h
  simp only [bAnd_eq, Bool.and_eq_true, eqL_iff] at h
  exact ⟨canonL_spec h.1, canonL_spec h.2.1, h.2.2.1, h.2.2.2⟩

theorem neOneK_spec {d : Nat} {I Z : V} (h : neOneK d I Z = true) : Canon d Z ∧ Z ≠ I := by
  unfold neOneK at h
  rw [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨canonL_spec h.1, fun e => by rw [← eqL_iff] at e; rw [e] at h; exact Bool.noConfusion h.2⟩

theorem matCheckK_spec {m d E : Nat} {I : V} {X Xi : Nat → V} {n : Nat}
    {rels : List (List (Fin m × Bool))} {r3 dd c : List (Fin m × Bool)}
    (h : matCheckK d E I X Xi n rels r3 dd c = true) :
    (∀ i < n, Canon d (X i) ∧ Canon d (Xi i) ∧ mulL d E (X i) (Xi i) = I ∧
      mulL d E (Xi i) (X i) = I) ∧
    (∀ w ∈ rels, evalKn d E I X Xi w = I) ∧ evalKn d E I X Xi r3 = I ∧
    (Canon d (evalKn d E I X Xi dd) ∧ evalKn d E I X Xi dd ≠ I) ∧
    (Canon d (evalKn d E I X Xi c) ∧ evalKn d E I X Xi c ≠ I) := by
  unfold matCheckK at h
  simp only [bAnd_eq, Bool.and_eq_true, allN_iff, allK_iff, eqL_iff] at h
  exact ⟨fun i hi => invPairK_spec (h.1 i hi), h.2.1, h.2.2.1, neOneK_spec h.2.2.2.1,
    neOneK_spec h.2.2.2.2⟩

theorem eqM_unlane_one {d : Nat} {I : V} (hI : IdL d I) : eqM d (unlane d I) (idM d) = true := by
  rw [← hI.eq]
  exact eqM_self (by unfold idM; simp)

theorem eqM_unlane_ne {d : Nat} {I Z : V} (hI : IdL d I) (hIc : Canon d I) (hZ : Canon d Z)
    (hne : Z ≠ I) : eqM d (unlane d Z) (idM d) = false := by
  rw [hI.eq]
  cases h : eqM d (unlane d Z) (unlane d I)
  · rfl
  · exact absurd (eqM_unlane hZ.wf hIc.wf hZ.p hZ.m hIc.p hIc.m h) hne

end CFSG.KC.CF24M

end
