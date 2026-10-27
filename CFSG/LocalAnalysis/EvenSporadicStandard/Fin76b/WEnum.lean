module

public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def skey (m : ℕ) (T : Table) : UInt64 := hkey m (T.extract 0 m)

@[expose] def mulClosureS (n m : ℕ) (gens : Array Table) (cap : ℕ) :
    Array Table × Array ℕ × Array ℕ := Id.run do
  let e := idT n
  let mut seen : Std.HashSet UInt64 := (∅ : Std.HashSet UInt64).insert (skey m e)
  let mut elts : Array Table := #[e]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  for h in [0:cap] do
    if h < elts.size then
      let y := elts[h]!
      for l in [0:gens.size] do
        let z := compT n y gens[l]!
        let kz := skey m z
        if !seen.contains kz then
          seen := seen.insert kz
          elts := elts.push z
          par := par.push h
          lab := lab.push l
    else break
  return (elts, par, lab)

@[expose] def hashIndexS (m : ℕ) (L : Array Table) : Std.HashMap UInt64 ℕ :=
  (List.range L.size).foldl (fun idx i => idx.insert (skey m L[i]!) i) ∅

@[expose] def memTS (n m : ℕ) (L : Array Table) (idx : Std.HashMap UInt64 ℕ) (x : Table) :
    Bool :=
  match idx[skey m x]? with
  | some i => decide (i < L.size) && tblEq n x L[i]!
  | none => false

@[expose] def closedOKS (n m : ℕ) (gens L : Array Table) : Bool :=
  let idx := hashIndexS m L
  L.all fun x => gens.all fun g => memTS n m L idx (compT n x g)

theorem memT_of_memTS {n m : ℕ} {L : Array Table} {idx : Std.HashMap UInt64 ℕ} {x : Table}
    (h : memTS n m L idx x = true) : memT n L x = true := by
  unfold memTS at h
  split at h
  · rename_i i _
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [memT, Array.any_eq_true]
    refine ⟨i, h.1, ?_⟩
    rw [← getElem!_pos L i h.1]
    exact h.2
  · exact absurd h Bool.false_ne_true

theorem closedOK_of_closedOKS {n m : ℕ} {gens L : Array Table}
    (h : closedOKS n m gens L = true) : closedOK n gens L = true := by
  unfold closedOKS at h
  rw [Array.all_eq_true] at h
  rw [closedOK, Array.all_eq_true]
  intro k hk
  have h1 := h k hk
  rw [Array.all_eq_true] at h1 ⊢
  intro l hl
  exact memT_of_memTS (h1 l hl)

variable {n : ℕ}

theorem closedOK_spec_fwd {gens : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l)) {L : Array Table}
    {e : ℕ → Equiv.Perm (Fin n)} (hL : ∀ k < L.size, Rep n L[k]! (e k))
    (h1 : ∃ k < L.size, e k = 1) (hc : closedOK n gens L = true) :
    ∀ x ∈ closure (gg '' {l | l < gens.size}), ∃ k < L.size, x = e k := by
  rw [closedOK, Array.all_eq_true] at hc
  have hstep : ∀ k < L.size, ∀ l < gens.size, ∃ k' < L.size, e k * gg l = e k' := by
    intro k hk l hl
    have h2 := hc k hk
    rw [Array.all_eq_true] at h2
    have h3 := h2 l hl
    have hk' := hL k hk
    rw [getElem!_pos L k hk] at hk'
    have hl' := hg l hl
    rw [getElem!_pos gens l hl] at hl'
    exact memT_spec hL (Rep.compT hk' hl') h3
  have hpow : ∀ l < gens.size, ∀ m : ℕ, ∀ k < L.size, ∃ k' < L.size, e k * gg l ^ m = e k' := by
    intro l hl m
    induction m with
    | zero => exact fun k hk => ⟨k, hk, by rw [pow_zero, mul_one]⟩
    | succ m ih =>
      intro k hk
      obtain ⟨k', hk', h'⟩ := ih k hk
      obtain ⟨k'', hk'', h''⟩ := hstep k' hk' l hl
      exact ⟨k'', hk'', by rw [pow_succ, ← mul_assoc, h', h'']⟩
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => obtain ⟨k, hk, hk1⟩ := h1; exact ⟨k, hk, hk1.symm⟩
  | mul_right x _ y hy ih =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨k', hk', e'⟩ := hstep k hk l hl
    exact ⟨k', hk', e'⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨k, hk, rfl⟩ := ih
    have hord := orderOf_pos (gg l)
    have hinv : (gg l)⁻¹ = gg l ^ (orderOf (gg l) - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hord, pow_orderOf_eq_one]
    obtain ⟨k', hk', e'⟩ := hpow l hl (orderOf (gg l) - 1) k hk
    exact ⟨k', hk', by rw [hinv, e']⟩

theorem enumS_spec (hn : n < 2 ^ 32) {A E : Array Table} {par lab : Array ℕ}
    (hg : ∀ x ∈ A, permOK n x = true) (htree : mulTreeOK n A E par lab = true)
    (hclosed : closedOK n A E = true) (hdist : hkeysDistinct n E.toList = true) :
    (∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!) ∧
        tablePerm n E[k]! ∈ closure (tp n '' {x | x ∈ A})) ∧
      (∀ x ∈ closure (tp n '' {x | x ∈ A}), ∃ k < E.size, Rep n E[k]! x) ∧
      Nat.card ↥(closure (tp n '' {x | x ∈ A})) = E.size := by
  set K := closure (tp n '' {x | x ∈ A})
  have hga : ∀ l < A.size, Rep n A[l]! (tp n A[l]!) ∧ tp n A[l]! ∈ K := fun l hl =>
    ⟨rep_tp (hg _ (getElem!_mem_array hl)), subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have hE := mulTreeOK_spec hn K (gg := fun l => tp n A[l]!) hga htree
  have hErep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!) ∧ tablePerm n E[k]! ∈ K := by
    intro k hk
    obtain ⟨c, hc, hrep⟩ := hE k hk
    rw [tablePerm_eq hrep]
    exact ⟨hrep, hc⟩
  have h1 : ∃ k < E.size, tablePerm n E[k]! = 1 := by
    simp only [mulTreeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
    exact ⟨0, htree.1.1, tablePerm_eq (rep_of_tblEq (Rep.idT hn) htree.1.2)⟩
  have hcov := closedOK_spec_fwd (gens := A) (gg := fun l => tp n A[l]!)
    (fun l hl => (hga l hl).1) (fun k hk => (hErep k hk).1) h1 hclosed
  have himg : (fun l => tp n A[l]!) '' {l | l < A.size} = tp n '' {x | x ∈ A} := by
    ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨A[l]!, getElem!_mem_array hl, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨l, hl, rfl⟩ := Array.getElem_of_mem hx
      exact ⟨l, hl, by
        show tp n A[l]! = tp n A[l]
        rw [getElem!_pos A l hl]⟩
  rw [himg] at hcov
  have hcov' : ∀ x ∈ K, ∃ k < E.size, Rep n E[k]! x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hcov x hx
    exact ⟨k, hk, (hErep k hk).1⟩
  refine ⟨hErep, hcov', ?_⟩
  have hnodup : (E.toList.map (tablePerm n)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm (fun k hk => (hErep k hk).1)) hdist
  have hcard := card_eq_length (fun g => g ∈ K) id Function.injective_id _ hnodup (by
    intro g
    simp only [List.mem_map, id]
    constructor
    · rintro ⟨T, hT, rfl⟩
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
      have := (hErep k hk).2
      rw [getElem!_pos E k hk] at this
      exact ⟨_, this, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨k, hk, hrep⟩ := hcov' g hg
      refine ⟨E[k]!, ?_, tablePerm_eq hrep⟩
      rw [getElem!_pos E k hk]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hk))
  rw [List.length_map, Array.length_toList] at hcard
  rw [← hcard]

end CFSG.EvenSporadicStandard.Fin76b
