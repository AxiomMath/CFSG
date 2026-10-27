
module

public import Certificates.Data.Kernel.Spor.ConjTree
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.PrimSound

public section

namespace CFSG.KS.ConjTree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore

abbrev Cn (n w p : Nat) : Prop := canonK n w (mask w) (n * w) p = true

theorem conj_unpack {n w g x gi : Nat} (hg : Cn n w g) (hx : Cn n w x) (hgi : Cn n w gi)
    (hp : permOK n w (mask w) (n * w) g gi = true) :
    conjA n (unpack n w g) (unpack n w x) = unpack n w (pconj n w g x gi) := by
  have hinv : invCand n (unpack n w g) = unpack n w gi := (invEqK_sound hp).1
  rw [conjA, hinv, compA_unpack hx hgi, compA_unpack hg (canonK_pcomp hx hgi)]
  rfl

theorem cn_pconj {n w g x gi : Nat} (hg : Cn n w g) (hx : Cn n w x) (hgi : Cn n w gi) :
    Cn n w (pconj n w g x gi) :=
  canonK_pcomp hg (canonK_pcomp hx hgi)

theorem ofFn_push {α : Type} {k : Nat} (f : Nat → α) :
    (Array.ofFn (n := k + 1) fun i => f i.val).push (f (k + 1)) =
      Array.ofFn (n := k + 2) fun i => f i.val := by
  apply Array.ext
  · simp
  · intro i h1 h2
    rw [Array.getElem_push]
    split_ifs with hi
    · simp
    · have : i = k + 1 := by simp at h1 hi; omega
      subst this
      simp

theorem treeConjN_eq {n w r N wt : Nat} {gens : Array (Array Nat)} {s₀ tree : Array Nat}
    {GS GSI T : Nat → Nat} {TF : Nat} (hr : 0 < r)
    (hgs : ∀ k < r, gens[k]! = unpack n w (GS k)) (hcg : ∀ k < r, Cn n w (GS k))
    (hcgi : ∀ k < r, Cn n w (GSI k)) (hpg : ∀ k < r, permOK n w (mask w) (n * w) (GS k) (GSI k) = true)
    (h0 : s₀ = unpack n w (T 0)) (hc0 : Cn n w (T 0)) (hr0 : ∃ X, Rep n (unpack n w (T 0)) X)
    (htree : tree = unpack N wt TF)
    (hS : ∀ i < N, pg wt (mask wt) TF i / r < i + 1 ∧
      T (i + 1) = pconj n w (GS (pg wt (mask wt) TF i % r)) (T (pg wt (mask wt) TF i / r))
        (GSI (pg wt (mask wt) TF i % r))) :
    treeConjN n r gens s₀ tree = (Array.ofFn (n := N + 1) fun i => unpack n w (T i.val)) ∧
      (∀ i < N + 1, Cn n w (T i)) ∧ ∀ i < N + 1, ∃ X, Rep n (unpack n w (T i)) X := by
  set f := fun (acc : Array (Array Nat)) (t : Nat) => acc.push (conjA n gens[t % r]! acc[t / r]!)
  have hrep : ∀ k < r, Rep n (unpack n w (GS k)) (permOfArr n (unpack n w (GS k))) ∧
      isInvA n (unpack n w (GS k)) (invCand n (unpack n w (GS k))) = true := by
    intro k hk
    have h := invEqK_sound (hpg k hk)
    rw [h.1]
    exact ⟨(rep_permOfArr h.2).1, h.2⟩
  have key : ∀ k ≤ N, ((List.range k).map (pg wt (mask wt) TF)).foldl f #[s₀] =
      (Array.ofFn (n := k + 1) fun i => unpack n w (T i.val)) ∧ (∀ i < k + 1, Cn n w (T i)) ∧
      ∀ i < k + 1, ∃ X, Rep n (unpack n w (T i)) X := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, fun i hi => by rw [show i = 0 by omega]; exact hc0,
        fun i hi => by rw [show i = 0 by omega]; exact hr0⟩
      rw [h0]
      simp
      rfl
    | succ k ih =>
      intro hk
      obtain ⟨e, hc, hx⟩ := ih (by omega)
      obtain ⟨hlt, hstep⟩ := hS k (by omega)
      set t := pg wt (mask wt) TF k
      have hmod : t % r < r := Nat.mod_lt _ hr
      have hc' : Cn n w (T (k + 1)) := by
        rw [hstep]
        exact cn_pconj (hcg _ hmod) (hc _ hlt) (hcgi _ hmod)
      have hacc : (Array.ofFn (n := k + 1) fun i => unpack n w (T i.val))[t / r]! =
          unpack n w (T (t / r)) := by
        rw [getElem!_pos _ _ (by simpa using hlt), Array.getElem_ofFn]
      have hconj : conjA n gens[t % r]! (unpack n w (T (t / r))) = unpack n w (T (k + 1)) := by
        rw [hgs _ hmod, conj_unpack (hcg _ hmod) (hc _ hlt) (hcgi _ hmod) (hpg _ hmod), hstep]
      refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
      · rw [List.range_succ, List.map_append, List.foldl_append, e, List.map_singleton,
          List.foldl_cons, List.foldl_nil]
        change (Array.ofFn (n := k + 1) fun i => unpack n w (T i.val)).push (conjA n gens[t % r]!
          (Array.ofFn (n := k + 1) fun i => unpack n w (T i.val))[t / r]!) = _
        rw [hacc, hconj]
        exact ofFn_push (fun i => unpack n w (T i))
      · rcases Nat.lt_or_ge i (k + 1) with h | h
        · exact hc i h
        · rw [show i = k + 1 by omega]
          exact hc'
      · rcases Nat.lt_or_ge i (k + 1) with h | h
        · exact hx i h
        · rw [show i = k + 1 by omega]
          obtain ⟨X, hX⟩ := hx _ hlt
          refine ⟨permOfArr n (unpack n w (GS (t % r))) *
            (X * (permOfArr n (unpack n w (GS (t % r))))⁻¹), ?_⟩
          rw [← hconj, hgs _ hmod]
          exact rep_compA (hrep _ hmod).1 (rep_compA hX
            (rep_inv_of_isInvA (hrep _ hmod).1 (hrep _ hmod).2))
  have hlist : tree.toList = (List.range N).map (pg wt (mask wt) TF) := by
    rw [htree, unpack, Array.toList_ofFn, List.ofFn_eq_map]
    apply List.ext_getElem <;> simp
  have hfold : treeConjN n r gens s₀ tree = tree.toList.foldl f #[s₀] := by
    rw [treeConjN, ← Array.foldl_toList]
  rw [hfold, hlist]
  exact key N le_rfl

end CFSG.KS.ConjTree

end
