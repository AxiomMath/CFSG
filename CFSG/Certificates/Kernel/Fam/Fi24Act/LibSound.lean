module

public import CFSG.Certificates.Kernel.Fam.Fi24Act.Lib
public import CFSG.Certificates.Kernel.LceSP.Walk

public section

namespace CFSG.Certificates.Fi24ActS

open CFSG.KC CFSG.KC.LceS CFSG.KC.Fi24Act CFSG.Certificates.LceP

theorem slotTo_spec {blk : ℕ → ℕ} {K r z : ℕ} (h : slotTo blk K r z = true) :
    (fxc (fct blk (Nat.shiftRight r 1)) = K ∧ fy (fct blk (Nat.shiftRight r 1)) = z) ∨
      (fyic (fct blk (Nat.shiftRight r 1)) = K ∧ fx (fct blk (Nat.shiftRight r 1)) = z) := by
  unfold slotTo at h
  rw [letB_eq, brec_eq] at h
  split_ifs at h
  · right
    simpa only [andB_iff, Nat.beq_eq] using h
  · left
    simpa only [andB_iff, Nat.beq_eq] using h

theorem rec_all (f : ℕ → Bool) (lo : ℕ) : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun t ih => andB ih (f (Nat.add lo t))) m = true →
      ∀ t < m, f (lo + t) = true
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | m + 1, h, t, ht => by
    change andB (Nat.rec (motive := fun _ => Bool) true
      (fun t ih => andB ih (f (Nat.add lo t))) m) (f (Nat.add lo m)) = true at h
    rw [andB_iff] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact rec_all f lo m h.1 t ht
    · exact h.2

theorem covTabL_spec {blk A T R : ℕ → ℕ} {nf c N lo m : ℕ}
    (h : covTabL blk A T R nf c N lo m = true) : lo + m ≤ N ∧ ∀ t < m,
      T (lo + t) < N ∧ Nat.shiftRight (R (lo + t)) 1 < nf ∧
        slotTo blk (Nat.lor (A (lo + t)) (Nat.shiftLeft c 20)) (R (lo + t)) (A (T (lo + t))) = true := by
  unfold covTabL at h
  rw [andB_iff, Nat.ble_eq] at h
  refine ⟨h.1, fun t ht => ?_⟩
  have := rec_all (fun i => letB (T i) (fun y => letB (R i) (fun r =>
      andB (Nat.blt y N) (andB (Nat.blt (Nat.shiftRight r (nat_lit 1)) nf)
        (slotTo blk (Nat.lor (A i) (Nat.shiftLeft c (nat_lit 20))) r (A y)))))) lo m h.2 t ht
  simpa only [letB_eq, andB_iff, Nat.blt_eq] using this

theorem covTabL_reps {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G) (rep : ℕ → G)
    {blk A T R : ℕ → ℕ} {nf c N lo m : ℕ}
    (hfacts : ∀ e < nf,
      rep (fx (fct blk e)) * lv gen (fc (fct blk e)) * (rep (fy (fct blk e)))⁻¹ ∈ H ∧
      rep (fy (fct blk e)) * lv gen (fic (fct blk e)) * (rep (fx (fct blk e)))⁻¹ ∈ H)
    (hA : ∀ t < m, A (lo + t) < 1048576) (hc : c < 256)
    (h : covTabL blk A T R nf c N lo m = true) :
    ∀ t < m, T (lo + t) < N ∧ rep (A (lo + t)) * lv gen c * (rep (A (T (lo + t))))⁻¹ ∈ H := by
  intro t ht
  obtain ⟨-, hs⟩ := covTabL_spec h
  obtain ⟨hT, hR, hsl⟩ := hs t ht
  refine ⟨hT, ?_⟩
  obtain ⟨hfw, hbw⟩ := hfacts _ hR
  have hx := hA t ht
  have hS := slotTo_spec hsl
  have hic := fic_lt blk (Nat.shiftRight (R (lo + t)) 1)
  generalize fct blk (Nat.shiftRight (R (lo + t)) 1) = E at hS hfw hbw hic
  rcases hS with ⟨hk, hy⟩ | ⟨hk, hy⟩
  · rw [fxc_eq, lor20 c hx] at hk
    have := fx_lt E
    have := fc_lt E
    have h1 : fx E = A (lo + t) := by omega
    have h2 : fc E = c := by omega
    rw [h1, h2, hy] at hfw
    exact hfw
  · rw [fyic_eq, lor20 c hx] at hk
    have := fy_lt E
    have h1 : fy E = A (lo + t) := by omega
    have h2 : fic E = c := by omega
    rw [h1, h2, hy] at hbw
    exact hbw

end CFSG.Certificates.Fi24ActS

end
