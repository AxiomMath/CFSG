module

public import CFSG.Certificates.Kernel.Co1M.OrbitMem
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.KC.Co1M

open CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def hitAt (n : Nat) (test : Nat → Bool) (m : Nat) (H : Nat → Nat) (b j : Nat) :
    Bool :=
  orB (notB (Nat.blt j n)) (orB (notB (test j)) (orbMemK m H b j))

theorem hitAt_spec {n m b j : Nat} {test : Nat → Bool} {H : Nat → Nat} (h0 : 0 < m)
    (h : hitAt n test m H b j = true) (hj : j < n) (ht : test j = true) : ∃ k < m, H k = j := by
  unfold hitAt at h
  have hb : Nat.blt j n = true := by rw [Nat.blt_eq]; exact hj
  have e1 : notB (Nat.blt j n) = false := by rw [hb]; rfl
  have e2 : notB (test j) = false := by rw [ht]; rfl
  rw [e1, e2] at h
  change orbMemK m H b j = true at h
  unfold orbMemK at h
  exact ⟨_, orbBsK_lt b 0 h0, Nat.eq_of_beq_eq_true h⟩

theorem hits_card {n N m b : Nat} {test : Nat → Bool} {H : Nat → Nat} (h0 : 0 < m) (hN : n ≤ N)
    (h : ∀ j < N, hitAt n test m H b j = true) :
    ((Finset.range n).filter fun j => test j = true).card ≤ m := by
  have hsub : (Finset.range n).filter (fun j => test j = true) ⊆ (Finset.range m).image H := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨k, hk, e⟩ := hitAt_spec h0 (h j (by omega)) hj.1 hj.2
    exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, e⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  rwa [Finset.card_range] at this

end CFSG.KC.Co1M

end
