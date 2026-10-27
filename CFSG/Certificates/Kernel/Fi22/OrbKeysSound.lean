module

public import Certificates.Data.Kernel.Fi22.Orb
public import CFSG.Certificates.Kernel.Spor.TBfsSound

public section

namespace CFSG.KS.Fi22O

open CFSG.F3.Native CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KS.TBfs

@[expose] def conjL (l : Nat) (X : Array V) : Array V :=
  if l == 1 then conjM 77 (matA ()) (matA ()) X else conjM 77 (matB ()) (matBi ()) X

@[expose] def kstep (par lab : Table) (K : Array (Array V)) (k : Nat) : Array (Array V) :=
  K.push (conjL (ap lab k) K[ap par k]!)

theorem orbKeys_eq (par lab : Table) :
    orbKeys par lab = (List.range' 1 3509).foldl (kstep par lab) #[matA ()] := by
  unfold orbKeys
  exact Array.toArray_toList

theorem fold_spec (par lab : Table) : ∀ n,
    ((List.range' 1 n).foldl (kstep par lab) #[matA ()]).size = n + 1 ∧
    ((List.range' 1 n).foldl (kstep par lab) #[matA ()])[0]! = matA () ∧
    ∀ k, 0 < k → k ≤ n → ap par k < k →
      ((List.range' 1 n).foldl (kstep par lab) #[matA ()])[k]! =
        conjL (ap lab k) ((List.range' 1 n).foldl (kstep par lab) #[matA ()])[ap par k]!
  | 0 => ⟨rfl, rfl, fun k h1 h2 _ => absurd h2 (by omega)⟩
  | n + 1 => by
    obtain ⟨hs, h0, hk⟩ := fold_spec par lab n
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 1 n).foldl (kstep par lab) #[matA ()] = F at hs h0 hk
    have e1 : 1 + 1 * n = n + 1 := by omega
    rw [e1]
    unfold kstep
    refine ⟨by rw [Array.size_push, hs], by rw [push_lt (by omega), h0], fun k h1 h2 h3 => ?_⟩
    rcases Nat.lt_or_eq_of_le h2 with h2 | rfl
    · rw [push_lt (by omega), push_lt (by omega), hk k h1 (by omega) h3]
    · rw [← hs] at h3 ⊢
      rw [push_eq, push_lt h3]

theorem orbKeys_spec (par lab : Table) :
    (orbKeys par lab).size = 3510 ∧ (orbKeys par lab)[0]! = matA () ∧
      ∀ k, 0 < k → k < 3510 → ap par k < k →
        (orbKeys par lab)[k]! = conjL (ap lab k) (orbKeys par lab)[ap par k]! := by
  rw [orbKeys_eq]
  obtain ⟨hs, h0, hk⟩ := fold_spec par lab 3509
  exact ⟨hs, h0, fun k h1 h2 h3 => hk k h1 (by omega) h3⟩

end CFSG.KS.Fi22O

end
