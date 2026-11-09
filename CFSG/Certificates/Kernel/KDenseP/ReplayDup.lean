module

public import CFSG.Certificates.Kernel.KDenseP.ReplaySound

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense

@[expose] noncomputable def covLD (GK DP CH : Nat → Nat) (G : Nat → List Nat) (ng : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => andB (orB (andB (Nat.blt (GK k) ng) (memB k (G (GK k))))
      (andB (Nat.beq (CH k) (CH (DP k)))
        (andB (Nat.blt (GK (DP k)) ng) (memB (DP k) (G (GK (DP k))))))) acc)

theorem covLD_spec {GK DP CH : Nat → Nat} {G : Nat → List Nat} {ng : Nat} :
    ∀ (nch : Nat), covLD GK DP CH G ng nch = true → ∀ k < nch,
      (GK k < ng ∧ k ∈ G (GK k)) ∨ (CH k = CH (DP k) ∧ GK (DP k) < ng ∧ DP k ∈ G (GK (DP k)))
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | nch + 1, h, k, hk => by
    have h' : andB _ (covLD GK DP CH G ng nch) = true := h
    obtain ⟨h1, h2⟩ := rpAnd.1 h'
    by_cases hk' : k < nch
    · exact covLD_spec nch h2 k hk'
    · have e : k = nch := by omega
      subst e
      rcases rpOr.1 h1 with h | h
      · obtain ⟨a, b⟩ := rpAnd.1 h
        rw [Nat.blt_eq] at a
        exact Or.inl ⟨a, memB_spec b⟩
      · obtain ⟨a, b⟩ := rpAnd.1 h
        obtain ⟨c, d⟩ := rpAnd.1 b
        rw [Nat.blt_eq] at c
        exact Or.inr ⟨Nat.eq_of_beq_eq_true a, c, memB_spec d⟩

theorem replay_soundD {n : Nat} {run : Nat → St → St} {chk : (Nat → St) → Nat → Bool}
    (hloc : ∀ S S' c, S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) → chk S c = chk S' c)
    (hprod : ∀ S c, Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      chk S c = stEqN n (run c (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))))
    {CH PR GK DP : Nat → Nat} {G : Nat → List Nat} {S0 : Nat → St} {w ng nch : Nat}
    (hg : ∀ g < ng, grpL run chk CH PR G S0 w g = true) (hcov : covLD GK DP CH G ng nch = true) :
    ∀ k < nch, chk (rlS run CH PR S0 w) (CH k) = true := by
  have key : ∀ k, GK k < ng → k ∈ G (GK k) → chk (rlS run CH PR S0 w) (CH k) = true := by
    intro k hgk hmem
    refine rpl_spec hloc hprod (G (GK k)) S0 (fun x => Nat.blt x w) (fun x hx => ?_) (hg _ hgk) k hmem
    have hx' : Nat.blt x w = true := hx
    rw [Nat.blt_eq] at hx'
    exact (rlS_lt hx').symm
  intro k hk
  rcases covLD_spec nch hcov k hk with ⟨hgk, hmem⟩ | ⟨heq, hgk, hmem⟩
  · exact key k hgk hmem
  · rw [heq]
    exact key _ hgk hmem

end CFSG.KC.KDenseP

end
