module

public import Certificates.Data.Kernel.Fi23Q.Words
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Pc3 CFSG.KS.Raw.Orb

@[expose] noncomputable def cwL (W i : Nat) : Nat := fld(W, Nat.mul (nat_lit 5) i, nat_lit 31)

@[expose] noncomputable def cwAux (n W k : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun m acc => List.cons (Nat.add (nat_lit 52)
      fld(W, Nat.mul (nat_lit 5) (Nat.sub (Nat.sub n (nat_lit 1)) m), nat_lit 31)) acc) k

theorem cwAux_mem {n W r : Nat} : ∀ k, r ∈ cwAux n W k → ∃ m < k, r = 52 + cwL W (n - 1 - m)
  | 0, h => absurd h List.not_mem_nil
  | k + 1, h => by
    change r ∈ List.cons (Nat.add 52 (cwL W (n - 1 - k))) (cwAux n W k) at h
    rcases List.mem_cons.1 h with h | h
    · exact ⟨k, Nat.lt_succ_self k, h⟩
    · obtain ⟨m, hm, e⟩ := cwAux_mem k h
      exact ⟨m, Nat.lt_succ_of_lt hm, e⟩

theorem cwR_mem {n W r : Nat} (h : r ∈ cwR n W) : ∃ i < n, r = 52 + cwL W i := by
  obtain ⟨m, hm, e⟩ := cwAux_mem (n := n) (W := W) n h
  exact ⟨n - 1 - m, by omega, e⟩

@[expose] noncomputable def nwAux (n u k : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun m acc => (fun k => (fun e =>
      Bool.rec (motive := fun _ => List Nat)
        (Bool.rec (motive := fun _ => List Nat) (List.cons k (List.cons k acc)) (List.cons k acc)
          (Nat.beq e (nat_lit 1)))
        acc (Nat.beq e (nat_lit 0))) (dg u k)) (Nat.sub (Nat.sub n (nat_lit 1)) m)) k

theorem nwAux_mem {n u r : Nat} : ∀ k, k ≤ n → r ∈ nwAux n u k → r < n
  | 0, _, h => absurd h List.not_mem_nil
  | k + 1, hk, h => by
    have ih := nwAux_mem (n := n) (u := u) (r := r) k (by omega)
    change r ∈ Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat)
        (List.cons (n - 1 - k) (List.cons (n - 1 - k) (nwAux n u k)))
        (List.cons (n - 1 - k) (nwAux n u k)) (Nat.beq (dg u (n - 1 - k)) 1))
      (nwAux n u k) (Nat.beq (dg u (n - 1 - k)) 0) at h
    revert h
    cases Nat.beq (dg u (n - 1 - k)) 0 <;> cases Nat.beq (dg u (n - 1 - k)) 1 <;> intro h <;>
      dsimp only at h
    · rcases List.mem_cons.1 h with h | h
      · omega
      rcases List.mem_cons.1 h with h | h
      · omega
      exact ih h
    · rcases List.mem_cons.1 h with h | h
      · omega
      exact ih h
    · exact ih h
    · exact ih h

theorem nwR_lt {n u r : Nat} (h : r ∈ nwR n u) : r < n :=
  nwAux_mem n (Nat.le_refl n) h

theorem clsW_spec {H G : Nat → Nat} {T : Nat → List Nat} {CR nQ q c n W : Nat}
    (h : clsW H G T CR nQ q c n W = true) :
    q < nQ ∧ c < 4 ∧ (∀ r ∈ cwR n W, ∃ l < 24, r = 52 + l) ∧
      ∀ b < 6, wv G (cwR n W) (wv H (nwR 13 (f32 CR q)) b) = wv G (T c) (wv G (cwR n W) b) := by
  unfold clsW at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, fun r hr => ?_, fun b hb =>
    Nat.eq_of_beq_eq_true (allN_iff.1 h4 b hb)⟩
  obtain ⟨i, hi, rfl⟩ := cwR_mem hr
  exact ⟨cwL W i, Nat.blt_eq.mp (allN_iff.1 h3 i hi), rfl⟩

theorem eqH_spec {H : Nat → Nat} {u v : List Nat} (h : eqH H u v = true) :
    ∀ b < 6, wv H u b = wv H v b :=
  fun b hb => Nat.eq_of_beq_eq_true (allN_iff.1 h b hb)

theorem tcB_spec {G : Nat → Nat} {r k : Nat} (h : tcB G r k = true) :
    ∀ b < 6, tb G r b = CFSG.KC.Fi23R.tA G k b :=
  fun b hb => Nat.eq_of_beq_eq_true (allN_iff.1 h b hb)

end CFSG.KC.Fi23Q

end
