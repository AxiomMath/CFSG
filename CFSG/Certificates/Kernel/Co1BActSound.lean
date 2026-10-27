module

public import Certificates.Data.Kernel.Co1BAct

public section

namespace CFSG.KC.Co1B

open CFSG.KC.M1F2 (vmF strictB)
open CFSG.KC.Enum (pg)

theorem bRec_and {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem recAll_spec (f : Nat → Bool) : ∀ n, recAllB f n = true → ∀ t < n, f t = true
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | n + 1, h, t, ht => by
    obtain ⟨h1, h2⟩ := bRec_and h
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht' | rfl
    · exact recAll_spec f n h2 t ht'
    · exact h1

theorem actChunk_sound {F : Nat → Nat} {TA TB P A B : Nat} (h : actChunkK F TA TB P A B = true)
    {k : Nat} (hk : k < 840) :
    0 < pg 24 (CFSG.KS.mask 24) P k ∧ pg 20 (CFSG.KS.mask 20) A k < 98280 ∧
      pg 20 (CFSG.KS.mask 20) B k < 98280 ∧
      vmF 24 TA (pg 24 (CFSG.KS.mask 24) P k) = vAt F (pg 20 (CFSG.KS.mask 20) A k) ∧
      vmF 24 TB (pg 24 (CFSG.KS.mask 24) P k) = vAt F (pg 20 (CFSG.KS.mask 20) B k) := by
  have hp := recAll_spec _ _ h k hk
  unfold actFld at hp
  simp only [strictB_eq] at hp
  unfold actPt at hp
  obtain ⟨h1, hp⟩ := bRec_and hp
  obtain ⟨h2, hp⟩ := bRec_and hp
  obtain ⟨h3, hp⟩ := bRec_and hp
  obtain ⟨h4, h5⟩ := bRec_and hp
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5⟩

end CFSG.KC.Co1B

end
