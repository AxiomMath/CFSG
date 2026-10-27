module

public import Certificates.Data.Kernel.Census.PackedConjF
public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Census.E16Sound

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

theorem ppcOK_of_heads {n w : Nat} : ∀ (xs rs : List Nat) (cs : List (List Nat))
    (bs : List (Nat × Nat)),
    (∀ k ≤ xs.length, ppcHeadAt n w (xs.drop k) (rs.drop k) (cs.drop k) (bs.drop k) = true) →
    ppcOK n w xs rs cs bs = true
  | [], _, _, _, _ => by cases ‹List Nat› <;> rfl
  | x :: l, rs, cs, bs, h => by
    have h0 := h 0 (Nat.zero_le _)
    match rs, cs, bs, h0, h with
    | r :: rs', c :: cs', b :: bs', h0, h =>
      have ih := ppcOK_of_heads l rs' cs' bs' fun k hk => by
        simpa using h (k + 1) (by simp only [List.length_cons]; omega)
      simp only [List.drop_zero, ppcHeadAt, Bool.and_eq_true] at h0
      have e : ppcOK n w (x :: l) (r :: rs') (c :: cs') (b :: bs') =
          (pcHeadA n w x l r c && pcHeadB n w x l b && ppcOK n w l rs' cs' bs') := by
        simp only [ppcOK, pcHeadA, pcHeadB, Bool.and_assoc]
      rw [e, h0.1, h0.2, ih]
      rfl
    | [], _, _, h0, _ => simp [ppcHeadAt] at h0
    | _ :: _, [], _, h0, _ => simp [ppcHeadAt] at h0
    | _ :: _, _ :: _, [], h0, _ => simp [ppcHeadAt] at h0

theorem allRange_blocks {f : Nat → Bool} {a L : Nat} : ∀ {C : Nat}, (∀ i < a, f i = true) →
    (∀ c < C, (List.range' (a + c * L) L).all f = true) → ∀ i < a + C * L, f i = true
  | 0, h0, _ => by simpa using h0
  | C + 1, h0, h => by
    have ih := allRange_blocks (C := C) h0 fun c hc => h c (by omega)
    have := allRange_extend ih (h C (by omega))
    rwa [show a + C * L + L = a + (C + 1) * L by rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]]
      at this

theorem all_blocks {α : Type} {f : α → Bool} {l : List α} {B : Nat} : ∀ {C a : Nat},
    (∀ c < C, ((l.drop (a + c * B)).take B).all f = true) → l.length ≤ a + C * B →
    (l.drop a).all f = true
  | 0, a, _, hl => by rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | C + 1, a, h, hl => by
    refine all_drop_chunk (by simpa using h 0 (by omega)) (all_blocks (B := B) (C := C) (a := a + B)
      (fun c hc => ?_) (by rw [Nat.add_mul, Nat.one_mul] at hl; omega))
    have := h (c + 1) (by omega)
    rwa [show a + (c + 1) * B = a + B + c * B by rw [Nat.add_mul, Nat.one_mul]; omega] at this

theorem pwordsWalk_blocks {n w : Nat} {gens : Array Nat} {xs : List Nat}
    {ws : List (List Nat)} {B : Nat} : ∀ {C a : Nat},
    (∀ c < C, pwordsWalk n w gens ((xs.drop (a + c * B)).take B) (ws.drop (a + c * B)) = true) →
    xs.length ≤ a + C * B → pwordsWalk n w gens (xs.drop a) (ws.drop a) = true
  | 0, a, _, hl => by rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | C + 1, a, h, hl => by
    refine pwordsWalk_chunk (by simpa using h 0 (by omega)) (pwordsWalk_blocks (B := B) (C := C)
      (a := a + B) (fun c hc => ?_) (by rw [Nat.add_mul, Nat.one_mul] at hl; omega))
    have := h (c + 1) (by omega)
    rwa [show a + (c + 1) * B = a + B + c * B by rw [Nat.add_mul, Nat.one_mul]; omega] at this

theorem eqA_unpackP {n w P Q : Nat} (_hn : n < 2 ^ 32) (_hw : n ≤ 2 ^ w)
    (hP : canon1 n w P = true) (hQ : canon1 n w Q = true) :
    CFSG.Monster.B.Co2.Native.eqA n (unpackP n w P) (unpackP n w Q) = Nat.beq P Q := by
  have h := pinXL_eq (xs := #[Q]) hP (by simp [hQ])
  simp only [pinXL, CFSG.ComponentClassification.RankTwoSporadic.Cert.inXL, List.toList_toArray,
    List.map_toArray, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false] at h
  exact h.symm

end CFSG.KC.Census
