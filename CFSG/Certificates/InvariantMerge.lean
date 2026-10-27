module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.Certificates

variable {n m : ℕ}

@[expose] def mergeRel (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) : ℕ → Fin n → Fin n → Prop
  | 0 => Relation.EqvGen fun u v => u = b ∧ v = x
  | k + 1 =>
    match L[k]? with
    | some (i, u, v) =>
      Relation.EqvGen fun a c => mergeRel S b x L k a c ∨ (a = S i u ∧ c = S i v)
    | none => mergeRel S b x L k

@[expose] def ValidInvariantMerge (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) : Prop :=
  (∀ (k : ℕ) (hk : k < L.length), mergeRel S b x L k (L[k]'hk).2.1 (L[k]'hk).2.2) ∧
    ∀ a c, mergeRel S b x L L.length a c

theorem mergeRel_succ_of_lt {S : Fin m → Equiv.Perm (Fin n)} {b x : Fin n}
    {L : List (Fin m × Fin n × Fin n)} {k : ℕ} (hk : k < L.length) :
    mergeRel S b x L (k + 1) = Relation.EqvGen fun a c => mergeRel S b x L k a c ∨
      (a = S (L[k]'hk).1 (L[k]'hk).2.1 ∧ c = S (L[k]'hk).1 (L[k]'hk).2.2) := by
  rw [mergeRel, List.getElem?_eq_getElem hk]

theorem mergeRel_le {S : Fin m → Equiv.Perm (Fin n)} {b x : Fin n}
    {L : List (Fin m × Fin n × Fin n)} {R : Fin n → Fin n → Prop} (hR : Equivalence R)
    (hinv : ∀ i u v, R u v → R (S i u) (S i v)) (hbx : R b x) :
    ∀ k, (∀ l (hl : l < L.length), l < k → mergeRel S b x L l (L[l]'hl).2.1 (L[l]'hl).2.2) →
      ∀ a c, mergeRel S b x L k a c → R a c
  | 0, _, a, c, h => by
    refine hR.eqvGen_iff.1 (Relation.EqvGen.mono (fun u v huv => ?_) a c h)
    obtain ⟨rfl, rfl⟩ := huv
    exact hbx
  | k + 1, hval, a, c, h => by
    have ih := mergeRel_le hR hinv hbx k fun l hl hlk => hval l hl (Nat.lt_succ_of_lt hlk)
    by_cases hk : k < L.length
    · rw [mergeRel_succ_of_lt hk] at h
      refine hR.eqvGen_iff.1 (Relation.EqvGen.mono (fun u v huv => ?_) a c h)
      rcases huv with huv | ⟨rfl, rfl⟩
      · exact ih u v huv
      · exact hinv _ _ _ (ih _ _ (hval k hk (Nat.lt_succ_self k)))
    · have hnone : L[k]? = none := List.getElem?_eq_none (by omega)
      rw [mergeRel, hnone] at h
      exact ih a c h

theorem invariant_merge_soundness (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) (hv : ValidInvariantMerge S b x L)
    (R : Fin n → Fin n → Prop) (hR : Equivalence R)
    (hinv : ∀ g ∈ Subgroup.closure (Set.range S), ∀ u v, R u v → R (g u) (g v))
    (hbx : R b x) : ∀ u v, R u v := fun u v =>
  mergeRel_le hR (fun i u v h => hinv (S i) (Subgroup.subset_closure ⟨i, rfl⟩) u v h) hbx
    L.length (fun l hl _ => hv.1 l hl) u v (hv.2 u v)

end CFSG.Certificates
