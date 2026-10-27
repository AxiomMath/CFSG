module

public import Mathlib.Data.Set.Card.Arithmetic
public import CFSG.Geometry.ProjectiveSpaces.Dimension
public import Mathlib.LinearAlgebra.Projectivization.Basic

public section

namespace CFSG.Geometry.ProjectiveSpaces

open scoped LinearAlgebra.Projectivization
open Module

namespace ProjectiveSpace

universe u

variable {P : Type u} (G : ProjectiveSpace P)

theorem ncard_join {P : Type u} [Finite P] (G : ProjectiveSpace P) {s : ℕ}
    (hs : ∀ ℓ ∈ G.lines, ℓ.ncard = s + 1) {S : Set P} (hS : G.IsSubspace S)
    (hSne : S.Nonempty) {p : P} (hp : p ∉ S) : (G.join S p).ncard = s * S.ncard + 1 := by
  have hjoin : G.join S p = insert p (⋃ q ∈ S, G.line p q \ {p}) := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hq, hxq⟩ := G.mem_join.1 hx
      by_cases hxp : x = p
      · exact Set.mem_insert_iff.2 (Or.inl hxp)
      · refine Set.mem_insert_iff.2 (Or.inr ?_)
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨q, hq, hxq, hxp⟩
    · intro hx
      rcases Set.mem_insert_iff.1 hx with hxp | hx
      · rw [hxp]
        exact G.mem_join_self hSne p
      · simp only [Set.mem_iUnion, exists_prop] at hx
        obtain ⟨q, hq, hxq, -⟩ := hx
        exact G.mem_join.2 ⟨q, hq, hxq⟩
  have hpU : p ∉ ⋃ q ∈ S, G.line p q \ {p} := by
    intro hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨q, hq, hxq, hxp⟩ := hx
    exact hxp (by simp)
  have hdisj : S.PairwiseDisjoint (fun q => G.line p q \ {p}) := by
    intro q hq r hr hqr
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hxq, hxne⟩ ⟨hxr, -⟩
    have hpq : p ≠ q := fun e => hp (e ▸ hq)
    have hpr : p ≠ r := fun e => hp (e ▸ hr)
    have hxp : x ≠ p := by simpa using hxne
    have hl : G.line p q = G.line p r :=
      (G.eq_line (G.line_mem_lines hpq) (Ne.symm hxp) (G.left_mem_line p q) hxq).trans
        (G.eq_line (G.line_mem_lines hpr) (Ne.symm hxp) (G.left_mem_line p r) hxr).symm
    have hq_in : q ∈ G.line p r := by rw [← hl]; exact G.right_mem_line p q
    have hline : G.line q r = G.line p r := G.line_eq_line hqr hq_in (G.right_mem_line p r)
    have hp_in : p ∈ G.line q r := by rw [hline]; exact G.left_mem_line p r
    exact hp (hS.line_subset hq hr hp_in)
  have hcount : (⋃ q ∈ S, G.line p q \ {p}).ncard =
      ∑ᶠ q ∈ S, (G.line p q \ {p}).ncard :=
    Set.Finite.ncard_biUnion (Set.toFinite S) (fun q _ => Set.toFinite _) hdisj
  have hdiff : ∀ q ∈ S, (G.line p q \ {p}).ncard = s := by
    intro q hq
    have hpq : p ≠ q := fun e => hp (e ▸ hq)
    rw [Set.ncard_sdiff_singleton_of_mem (G.left_mem_line p q),
      hs (G.line p q) (G.line_mem_lines hpq)]
    omega
  have hsum : (∑ᶠ q ∈ S, (G.line p q \ {p}).ncard) = s * S.ncard := by
    have h1 : (∑ᶠ q ∈ S, (G.line p q \ {p}).ncard) = ∑ᶠ q ∈ S, s :=
      finsum_mem_congr rfl fun q hq => hdiff q hq
    rw [h1, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite S), Finset.sum_const,
      ← Set.ncard_eq_toFinset_card S (Set.toFinite S)]
    simp [smul_eq_mul, mul_comm]
  rw [hjoin, Set.ncard_insert_of_notMem hpU, hcount, hsum]

private noncomputable def joinStep (G : ProjectiveSpace P) (S : Set P) : Set P := by
  classical
  exact if h : ∃ p : P, p ∉ S then G.join S (Classical.choose h) else S

private noncomputable def joinSeq (G : ProjectiveSpace P) (p0 : P) : ℕ → Set P
  | 0 => {p0}
  | k + 1 => joinStep G (joinSeq G p0 k)

private theorem joinSeq_succ (G : ProjectiveSpace P) (p0 : P) (k : ℕ) :
    joinSeq G p0 (k + 1) = joinStep G (joinSeq G p0 k) := rfl

private theorem joinStep_eq (G : ProjectiveSpace P) {S : Set P} (h : ∃ p : P, p ∉ S) :
    joinStep G S = G.join S (Classical.choose h) := by
  unfold joinStep
  rw [dif_pos h]

theorem hasDimension_of_card {P : Type u} [Finite P] (G : ProjectiveSpace P)
    {s n : ℕ} (hs1 : 1 ≤ s) (hs : ∀ ℓ ∈ G.lines, ℓ.ncard = s + 1)
    (hP : Nat.card P = ∑ i ∈ Finset.range (n + 1), s ^ i) : G.HasDimension n := by
  classical
  have hs0 : 0 < s := by omega
  have hsum_strict : ∀ a b : ℕ, a < b →
      (∑ i ∈ Finset.range a, s ^ i) < ∑ i ∈ Finset.range b, s ^ i := by
    intro a b hab
    induction b generalizing a with
    | zero => omega
    | succ b ih =>
      rw [Finset.sum_range_succ]
      by_cases hab' : a < b
      · have h1 := ih a hab'
        have h2 : 0 < s ^ b := Nat.pow_pos hs0
        omega
      · have ha : a = b := by omega
        subst a
        have h2 : 0 < s ^ b := Nat.pow_pos hs0
        omega
  have hgeom : ∀ k : ℕ, s * (∑ i ∈ Finset.range (k + 1), s ^ i) + 1 =
      ∑ i ∈ Finset.range (k + 2), s ^ i := by
    intro k
    conv_rhs => rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
    simp only [pow_zero]
    rw [Finset.mul_sum]
    refine congrArg (fun t => t + 1) ?_
    exact Finset.sum_congr rfl fun i _ => by
      rw [pow_succ]
      exact mul_comm _ _
  have hPpos : 0 < Nat.card P := by
    rw [hP]
    refine Finset.sum_pos (fun i _ => Nat.pow_pos hs0) ?_
    exact Finset.nonempty_range_iff.2 (Nat.succ_ne_zero n)
  haveI : Nonempty P := Finite.card_pos_iff.mp hPpos
  let p0 : P := Classical.arbitrary P
  have key : ∀ k ≤ n, G.IsSubspace (joinSeq G p0 k) ∧ (joinSeq G p0 k).Nonempty ∧
      (joinSeq G p0 k).ncard = ∑ i ∈ Finset.range (k + 1), s ^ i ∧
      (k < n → joinSeq G p0 k ≠ Set.univ) := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        have hx' : x = p0 := by simpa [joinSeq] using hx
        have hy' : y = p0 := by simpa [joinSeq] using hy
        exact absurd (hx'.trans hy'.symm) hxy
      · exact ⟨p0, by simp [joinSeq]⟩
      · simp [joinSeq]
      · intro h0 huniv
        have hcard0 : (joinSeq G p0 0).ncard = 1 := by simp [joinSeq]
        have h1 : Nat.card P = 1 := by
          rw [← Set.ncard_univ (α := P), ← huniv, hcard0]
        have hlt := hsum_strict 1 (n + 1) (by omega)
        rw [show (∑ i ∈ Finset.range 1, s ^ i) = 1 by simp] at hlt
        omega
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := by omega
      obtain ⟨hsub, hne, hcard, hproper⟩ := ih hk'
      have hproperk : joinSeq G p0 k ≠ Set.univ := hproper (by omega)
      have hex : ∃ p : P, p ∉ joinSeq G p0 k := by
        obtain ⟨p, -, hp⟩ := Set.exists_of_ssubset (Set.ssubset_univ_iff.2 hproperk)
        exact ⟨p, hp⟩
      have hpoint : Classical.choose hex ∉ joinSeq G p0 k := Classical.choose_spec hex
      have hsucc : joinSeq G p0 (k + 1) =
          G.join (joinSeq G p0 k) (Classical.choose hex) := by
        rw [joinSeq_succ, joinStep_eq]
      have hcard_succ : (joinSeq G p0 (k + 1)).ncard =
          ∑ i ∈ Finset.range (k + 2), s ^ i := by
        rw [hsucc, G.ncard_join hs hsub hne hpoint, hcard]
        exact hgeom k
      refine ⟨?_, ?_, hcard_succ, ?_⟩
      · rw [hsucc]
        exact G.isSubspace_join hsub hpoint
      · rw [hsucc]
        exact ⟨_, G.mem_join_self hne _⟩
      · intro hkn huniv
        have h1 : Nat.card P = ∑ i ∈ Finset.range (k + 2), s ^ i := by
          rw [← Set.ncard_univ (α := P), ← huniv, hcard_succ]
        have hlt := hsum_strict (k + 2) (n + 1) (by omega)
        omega
  let S : Fin (n + 1) → Set P := fun i => joinSeq G p0 i.val
  have hchain : ∀ j, j ≤ n → ∀ i, i < j → joinSeq G p0 i ⊂ joinSeq G p0 j := by
    intro j
    induction j with
    | zero =>
      intro hj i hi
      omega
    | succ j ih =>
      intro hj i hi
      have hstep : joinSeq G p0 j ⊂ joinSeq G p0 (j + 1) := by
        have hproperj : joinSeq G p0 j ≠ Set.univ := (key j (by omega)).2.2.2 (by omega)
        have hex : ∃ p : P, p ∉ joinSeq G p0 j := by
          obtain ⟨p, -, hp⟩ := Set.exists_of_ssubset (Set.ssubset_univ_iff.2 hproperj)
          exact ⟨p, hp⟩
        have hpoint : Classical.choose hex ∉ joinSeq G p0 j := Classical.choose_spec hex
        have hsucc : joinSeq G p0 (j + 1) =
            G.join (joinSeq G p0 j) (Classical.choose hex) := by
          rw [joinSeq_succ, joinStep_eq]
        rw [hsucc]
        refine Set.ssubset_iff_subset_ne.2 ⟨G.subset_join _ _, ?_⟩
        intro heq
        have hpjoin : Classical.choose hex ∈
            G.join (joinSeq G p0 j) (Classical.choose hex) :=
          G.mem_join_self (key j (by omega)).2.1 _
        rw [← heq] at hpjoin
        exact hpoint hpjoin
      by_cases hij : i = j
      · subst i
        exact hstep
      · have hi' : i < j := by omega
        exact (ih (by omega) i hi').trans hstep
  refine ⟨⟨S, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact ⟨(key i.val (by omega)).1, (key i.val (by omega)).2.1⟩
  · intro i j hij
    exact hchain j.val (by omega) i.val (by simpa using hij)
  · have hlastcard := (key n le_rfl).2.2.1
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    dsimp only [S]
    rw [Set.ncard_univ, hP, Fin.val_last, hlastcard]
  · intro m T hT
    obtain ⟨hTsub, hTmono, hTlast⟩ := hT
    have hbound : ∀ i, (hi : i ≤ m) →
        (∑ j ∈ Finset.range (i + 1), s ^ j) ≤ (T ⟨i, by omega⟩).ncard := by
      intro i
      induction i with
      | zero =>
        intro hi
        have hpos := (hTsub ⟨0, by omega⟩).2.ncard_pos
        have hsum1 : (∑ j ∈ Finset.range 1, s ^ j) = 1 := by simp
        rw [hsum1]
        omega
      | succ i ih =>
        intro hi
        have hi' : i ≤ m := by omega
        have hmono_i : T ⟨i, by omega⟩ < T ⟨i + 1, by omega⟩ :=
          hTmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
        obtain ⟨p, hp_mem, hp_not⟩ := Set.exists_of_ssubset hmono_i
        have hjoin_le : G.join (T ⟨i, by omega⟩) p ⊆ T ⟨i + 1, by omega⟩ :=
          G.join_subset (hTsub ⟨i + 1, by omega⟩).1 (le_of_lt hmono_i) hp_mem
        have hval : (G.join (T ⟨i, by omega⟩) p).ncard =
            s * (T ⟨i, by omega⟩).ncard + 1 :=
          G.ncard_join hs (hTsub ⟨i, by omega⟩).1 (hTsub ⟨i, by omega⟩).2 hp_not
        have hle : s * (T ⟨i, by omega⟩).ncard + 1 ≤
            (T ⟨i + 1, by omega⟩).ncard := by
          rw [← hval]
          exact Set.ncard_le_ncard hjoin_le (Set.toFinite _)
        have hprev := ih hi'
        have hmul : s * (∑ j ∈ Finset.range (i + 1), s ^ j) ≤
            s * (T ⟨i, by omega⟩).ncard := Nat.mul_le_mul_left s hprev
        rw [← hgeom i]
        omega
    have hlast := hbound m le_rfl
    have hmuniv : T ⟨m, by omega⟩ = Set.univ := by
      rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m from Fin.ext rfl]
      exact hTlast
    have htop : (∑ j ∈ Finset.range (m + 1), s ^ j) ≤ Nat.card P := by
      calc (∑ j ∈ Finset.range (m + 1), s ^ j) ≤ (T ⟨m, by omega⟩).ncard := hlast
        _ = Nat.card P := by rw [hmuniv, Set.ncard_univ]
    by_contra hmn
    have hm : n < m := by omega
    have hlt := hsum_strict (n + 1) (m + 1) (by omega)
    omega

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
