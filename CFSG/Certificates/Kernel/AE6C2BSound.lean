module

public import Certificates.Data.Kernel.AE6C2B
public import CFSG.Certificates.Kernel.Census.PackedLProof

public section

namespace CFSG.KC.AE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F
open CFSG.KC.Census (strictLA strictNA strictLA_eq strictNA_eq)

theorem strictLLA_eq {β : Sort _} (L : List (List Nat)) (k : List (List Nat) → β) :
    strictLLA L k = k L := by
  induction L generalizing k with
  | nil => rfl
  | cons l t ih =>
    change strictLA l (fun l' => strictLLA t fun r => k (l' :: r)) = k (l :: t)
    rw [strictLA_eq, ih]

theorem strictB_eqC (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem tblAux_spec {p s M T B : Nat} : ∀ (L : List Nat) (i : Nat), tblAux p s M T B L i = true →
    ∀ k (hk : k < L.length), lane9 T (keyM p M L[k]) = i + k ∧
      laneM s M B (i + k) = Nat.mod L[k] M
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | x :: L, i, h, k, hk => by
    have e : tblAux p s M T B (x :: L) i = Bool.rec false
        (Bool.rec false (strictB (Nat.succ i) (tblAux p s M T B L))
          (Nat.beq (laneM s M B i) (Nat.mod x M)))
        (Nat.beq (lane9 T (keyM p M x)) i) := rfl
    rw [e] at h
    cases h1 : Nat.beq (lane9 T (keyM p M x)) i
    · rw [h1] at h
      exact (Bool.false_ne_true h).elim
    cases h2 : Nat.beq (laneM s M B i) (Nat.mod x M)
    · rw [h1, h2] at h
      exact (Bool.false_ne_true h).elim
    rw [h1, h2] at h
    change strictB (Nat.succ i) (tblAux p s M T B L) = true at h
    rw [strictB_eqC] at h
    cases k with
    | zero =>
      rw [Nat.add_zero]
      exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
    | succ k =>
      have ih := tblAux_spec L (Nat.succ i) h k (by simpa using hk)
      have e3 : i + (k + 1) = Nat.succ i + k := by omega
      rw [List.getElem_cons_succ, e3]
      exact ih

theorem tblOK_spec {p s M T B : Nat} {L : List Nat} (h : tblOK p s M T B L = true) :
    ∀ k (hk : k < L.length), lane9 T (keyM p M L[k]) = k ∧ laneM s M B k = Nat.mod L[k] M := by
  intro k hk
  have e := tblAux_spec L 0 h k hk
  rw [Nat.zero_add] at e
  exact e

theorem memK_eq {p s M T B : Nat} {L : List Nat} (h : tblOK p s M T B L = true) (y : Nat) :
    memK p s M T B L.length y = L.any fun t => Nat.beq (Nat.mod y M) (Nat.mod t M) := by
  have hs := tblOK_spec h
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true]
  simp only [memK]
  constructor
  · intro hm
    generalize lane9 T (keyM p M y) = j at hm
    cases hb : Nat.blt j L.length
    · rw [hb] at hm
      exact (Bool.false_ne_true hm).elim
    rw [hb] at hm
    change Nat.beq (laneM s M B j) (Nat.mod y M) = true at hm
    have hjl : j < L.length := by
      rw [← Nat.blt_eq]
      exact hb
    refine ⟨L[j], List.getElem_mem hjl, ?_⟩
    rw [← (hs j hjl).2, Nat.eq_of_beq_eq_true hm]
    exact Nat.beq_refl _
  · rintro ⟨t, ht, he⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    have e := Nat.eq_of_beq_eq_true he
    have hkey : keyM p M y = keyM p M L[k] := by
      unfold keyM
      rw [e]
    have hb : Nat.blt k L.length = true := by
      rw [Nat.blt_eq]
      exact hk
    rw [hkey, (hs k hk).1, hb]
    change Nat.beq (laneM s M B k) (Nat.mod y M) = true
    rw [(hs k hk).2, e]
    exact Nat.beq_refl _

set_option exponentiation.threshold 4000 in
theorem memN_eq (L : List Nat) (y : Nat) :
    memN L y = L.any fun t => Nat.beq (Nat.mod y M5) (Nat.mod t M5) := rfl

theorem qsAllK_eq {mem : Nat → Bool} {PL G : List Nat} (h : ∀ y, mem y = memN PL y) :
    qsAllK mem PL G = qsAllN PL G := by
  unfold qsAllK qsAllN qsN
  simp only [strictNA_eq, h]

theorem rec_true {b x : Bool} (h : Bool.rec (motive := fun _ => Bool) false x b = true) :
    b = true ∧ x = true := by
  cases b
  · exact (Bool.false_ne_true h).elim
  · exact ⟨rfl, h⟩

theorem lsN_share {P Q3 L3 : List Nat} {Qs : List (List Nat)} (hQ : Qs = [P, P, P, Q3, P, P, P, P]) :
    lsN Qs L3 = [L3.filter (commAllN P), L3.filter (commAllN P), L3.filter (commAllN P),
      L3.filter (commAllN Q3), L3.filter (commAllN P), L3.filter (commAllN P),
      L3.filter (commAllN P), L3.filter (commAllN P)] := by
  subst hQ
  rfl

theorem basicF_sound {G P L3I B : List Nat} {CZ : List (List Nat)} (h : basicF G P L3I B CZ = true) :
    (c2BasicN G P (qsAllN P G) (lsRec P L3I) &&
      lsN (qsAllN P G) (l3N ((qsAllN P G).getD 3 []) B CZ) == lsRec P L3I) = true := by
  unfold basicF at h
  simp only [strictLA_eq, strictLLA_eq, strictB_eqC] at h
  obtain ⟨ht, hx⟩ := rec_true h
  have hm : ∀ y, memK keyP 3240 M5 (buildT keyP M5 P) (buildB 3240 M5 P) P.length y = memN P y :=
    fun y => (memK_eq ht y).trans (memN_eq P y).symm
  rw [qsAllK_eq (mem := memK keyP 3240 M5 (buildT keyP M5 P) (buildB 3240 M5 P) P.length) hm]
    at hx
  rw [Bool.and_eq_true, Bool.and_eq_true] at hx
  obtain ⟨⟨hq, hc⟩, hl⟩ := hx
  rw [Bool.and_eq_true, lsN_share (eq_of_beq hq)]
  exact ⟨hc, hl⟩

end CFSG.KC.AE6C2

end
