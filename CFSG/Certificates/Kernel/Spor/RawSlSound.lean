module

public import Certificates.Data.Kernel.Spor.RawSl
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem allBlk_of {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_of (fun l hl => h l (Nat.lt_succ_of_lt hl))]

theorem rec_blocks_of {f : Nat → Bool} : ∀ {q : Nat},
    (∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true
  | 0, _ => rfl
  | q + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true
    rw [h q (Nat.lt_succ_self q), rec_blocks_of (fun h' hh => h h' (Nat.lt_succ_of_lt hh))]

theorem allN_of_forall {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) :
    allN n f = true := by
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true
  have hd := Nat.div_add_mod n 64
  rw [allBlk_of (fun l hl => h _ (by rw [e6, e64, Nat.add_eq]; rw [er] at hl; omega)),
    rec_blocks_of (fun q hq => allBlk_of (fun l hl => h _ (by
      have hl' : l < 64 := hl
      rw [e6, Nat.add_eq]; rw [e64] at hq; omega)))]

theorem bIf_of_true {c t e : Bool} (hc : c = true) (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    t = true := by
  subst hc
  exact h

theorem levelK_of_sl {n w m nw pm idn kS root T R NS CH : Nat} {S SI TR TRI : Nat → Nat}
    (hh : lvHdK n w m nw idn TR kS root T R = true)
    (hs : ∀ s < NS, lvSlK n w m nw S SI TR TRI kS T R (s * CH) CH = true)
    (hN : n ≤ NS * CH) :
    levelK n w m nw pm idn S SI TR TRI kS root T R = true := by
  have hpt : ∀ k < n, lvPtK n w m nw S SI TR TRI kS T R (rcnt R) (stCnt T) (roff n nw R) k =
      true := by
    intro k hk
    have hCH : 0 < CH := by
      rcases Nat.eq_zero_or_pos CH with h0 | h0
      · rw [h0, Nat.mul_zero] at hN
        omega
      · exact h0
    have hsk : k / CH < NS := by
      rw [Nat.div_lt_iff_lt_mul hCH]
      omega
    have h1 := allN_spec (hs (k / CH) hsk) (k % CH) (Nat.mod_lt _ hCH)
    have e : Nat.add (k / CH * CH) (k % CH) = k := by
      rw [Nat.add_eq]
      exact Nat.div_add_mod' k CH
    rwa [e] at h1
  unfold lvHdK at hh
  rw [strictB_eq, strictB_eq, strictB_eq] at hh
  obtain ⟨h1, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨h2, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨h3, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨h4, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨h5, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 hh
  have hcn : rcnt R ≤ n := Nat.le_of_ble_eq_true h4
  have kk : ∀ k < rcnt R,
      lvKK n w m nw S SI TR TRI kS T R (rcnt R) (stCnt T) (roff n nw R) k = true := by
    intro k hk
    have h' := (bAnd_iff _ _).1 (hpt k (by omega))
    exact bIf_of_true (Nat.blt_eq ▸ hk) h'.2
  have kp : ∀ z < n, lvPosK w m nw R (rcnt R) z = true := by
    intro z hz
    have h' := (bAnd_iff _ _).1 (hpt z hz)
    exact bIf_of_true (Nat.blt_eq ▸ hz) h'.1
  have kB := fun k hk => ((bAnd_iff _ _).1 (kk k hk)).1
  have kD := fun k hk => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (kk k hk)).2).1
  have kE := fun k hk =>
    ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (kk k hk)).2).2).1
  have kF := fun k hk => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1
    ((bAnd_iff _ _).1 (kk k hk)).2).2).2).1
  have kH := fun k hk => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1
    ((bAnd_iff _ _).1 (kk k hk)).2).2).2).2).1
  have kI := fun k hk => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1
    ((bAnd_iff _ _).1 (kk k hk)).2).2).2).2).2
  unfold levelK
  rw [strictB_eq, strictB_eq, strictB_eq]
  refine (bAnd_iff _ _).2 ⟨h1, (bAnd_iff _ _).2 ⟨h2, (bAnd_iff _ _).2 ⟨h3, (bAnd_iff _ _).2 ⟨h4,
    (bAnd_iff _ _).2 ⟨h5, (bAnd_iff _ _).2 ⟨h6, (bAnd_iff _ _).2 ⟨allN_of_forall kB,
    (bAnd_iff _ _).2 ⟨allN_of_forall kp, (bAnd_iff _ _).2 ⟨allN_of_forall kD,
    (bAnd_iff _ _).2 ⟨allN_of_forall kE, (bAnd_iff _ _).2 ⟨allN_of_forall kF,
    (bAnd_iff _ _).2 ⟨h7, (bAnd_iff _ _).2 ⟨allN_of_forall kH, allN_of_forall kI⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CFSG.KS.Raw

end
