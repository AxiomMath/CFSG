module

public import Certificates.Data.Kernel.Co1BFixImp

public section

set_option maxRecDepth 100000

namespace CFSG.KC.Co1B

open CFSG.KC.M1F2 CFSG.KC.Enum CFSG.KLie.CT

theorem fixImp_andB (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem fixAllT_sound : ∀ {TQ : List Nat} {v : Nat}, fixAllT TQ v = true →
    ∀ t ∈ TQ, vmF 24 t v = v
  | [], _, _, t, ht => absurd ht List.not_mem_nil
  | t' :: TQ, v, h, t, ht => by
    have h' : andB (Nat.beq (vmF 24 t' v) v) (fixAllT TQ v) = true := h
    rw [fixImp_andB] at h'
    rcases List.mem_cons.1 ht with rfl | ht
    · exact Nat.eq_of_beq_eq_true h'.1
    · exact fixAllT_sound h'.2 t ht

theorem fixImpChunk_sound {T : Nat} {TQ : List Nat} {P : Nat} (h : fixImpChunkK T TQ P = true)
    {k : Nat} (hk : k < 840) (hv : vmF 24 T (pg 24 (CFSG.KS.mask 24) P k) =
      pg 24 (CFSG.KS.mask 24) P k) :
    fixAllT TQ (pg 24 (CFSG.KS.mask 24) P k) = true := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Bool) true
      (fun k acc => andB ((fun v => Bool.rec (motive := fun _ => Bool) true (fixAllT TQ v)
        (Nat.beq (vmF 24 T v) v)) (pg 24 (CFSG.KS.mask 24) P k)) acc) n : Bool) = true →
      ∀ k < n, vmF 24 T (pg 24 (CFSG.KS.mask 24) P k) = pg 24 (CFSG.KS.mask 24) P k →
        fixAllT TQ (pg 24 (CFSG.KS.mask 24) P k) = true := by
    intro n
    induction n with
    | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ n ih =>
      intro hn k hk hv
      rw [fixImp_andB] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact ih hn.2 k hk hv
      · have h1 := hn.1
        have hb : Nat.beq (vmF 24 T (pg 24 (CFSG.KS.mask 24) P k)) (pg 24 (CFSG.KS.mask 24) P k) =
            true := Nat.beq_eq_true_eq _ _ ▸ hv
        simp only [hb] at h1
        exact h1
  unfold fixImpChunkK at h
  exact key _ h k hk hv

theorem fixImpTab_sound {T : Nat} {TQ : List Nat} {F : Nat → Nat} {m : Nat}
    (h : fixImpTabK T TQ F m = true) {j k : Nat} (hj : j < m) (hk : k < 840)
    (hv : vmF 24 T (pg 24 (CFSG.KS.mask 24) (F j) k) = pg 24 (CFSG.KS.mask 24) (F j) k) :
    fixAllT TQ (pg 24 (CFSG.KS.mask 24) (F j) k) = true := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Bool) true
      (fun j acc => andB (fixImpChunkK T TQ (F j)) acc) n : Bool) = true →
      ∀ j < n, fixImpChunkK T TQ (F j) = true := by
    intro n
    induction n with
    | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ n ih =>
      intro hn j hj
      rw [fixImp_andB] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih hn.2 j hj
      · exact hn.1
  exact fixImpChunk_sound (key m h j hj) hk hv

end CFSG.KC.Co1B

end
