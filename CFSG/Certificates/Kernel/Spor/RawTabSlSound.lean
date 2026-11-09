module

public import Certificates.Data.Kernel.Spor.RawTabSl
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem allN_of_sl {f : Nat → Bool} {c NS K : Nat}
    (hs : ∀ s < NS, allN K (fun d => f (Nat.add (s * K) d)) = true) (hc : c ≤ NS * K) :
    allN c f = true := by
  refine allN_of_forall fun k hk => ?_
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, Nat.mul_zero] at hc
      omega
    · exact h0
  have hsk : k / K < NS := by
    rw [Nat.div_lt_iff_lt_mul hK]
    omega
  have h1 := allN_spec (hs (k / K) hsk) (k % K) (Nat.mod_lt _ hK)
  have e : Nat.add (k / K * K) (k % K) = k := by
    rw [Nat.add_eq]
    exact Nat.div_add_mod' k K
  rwa [e] at h1

theorem allN_of_guard {c : Nat} {g : Nat → Bool}
    (h : allN c (fun a => bIf(Nat.blt a c, g a, true)) = true) : allN c g = true :=
  allN_of_forall fun a ha => by
    have h1 := allN_spec h a ha
    rw [Nat.blt_eq.mpr ha] at h1
    exact h1

theorem utabF_of_sl {n w m nw i D NS K : Nat} {LR TR U : Nat → Nat}
    (hs : ∀ s < NS, utSlF n w m nw LR TR U i D (s * K) K = true)
    (hc : rcnt (LR (Nat.succ i)) ≤ NS * K) :
    utabF n w m nw LR TR U i D = true := by
  have h := allN_of_sl (f := utRowF n w m nw LR TR U i D) hs hc
  unfold utRowF at h
  unfold utabF
  simp only [strictB_eq] at h ⊢
  exact allN_of_guard h

theorem utab4F_of_sl {n w m nw i E D NS K : Nat} {LR TR U : Nat → Nat}
    (hs : ∀ s < NS, ut4SlF n w m nw LR TR U i E D (s * K) K = true)
    (hc : rcnt (LR (Nat.succ (Nat.succ i))) ≤ NS * K) :
    utab4F n w m nw LR TR U i E D = true := by
  have h := allN_of_sl (f := ut4RowF n w m nw LR TR U i E D) hs hc
  unfold ut4RowF at h
  unfold utab4F
  simp only [strictB_eq] at h ⊢
  exact allN_of_guard h

theorem vtab4K_of_sl {n w m nw idn BP i E D NS K : Nat} {LR TRI U : Nat → Nat}
    (hs : ∀ s < NS, vt4SlF n w m nw idn LR TRI U BP i E D (s * K) K = true)
    (hc : rcnt (LR (Nat.succ i)) ≤ NS * K) :
    vtab4K n w m nw idn LR TRI U BP i E D = true := by
  have h := allN_of_sl (f := vt4RowF n w m nw idn LR TRI U BP i E D) hs hc
  unfold vt4RowF at h
  unfold vtab4K
  simp only [strictB_eq] at h ⊢
  exact allN_of_guard h

end CFSG.KS.Raw

end
