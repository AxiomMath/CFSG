module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Group.End
import CFSG.FeitThompson.Representations.IntegerVectorSquaredLengthThree
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

variable {d r n : ℕ}

def signedPermVec {ι : Type*} (σ : Equiv.Perm ι) (ε u : ι → ℤ) : ι → ℤ := fun k => ε k * u (σ k)

theorem signedPermVec_apply {ι : Type*} (σ : Equiv.Perm ι) (ε u : ι → ℤ) (k : ι) :
    signedPermVec σ ε u k = ε k * u (σ k) := (rfl)

theorem signedPermVec_dotProduct {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) {ε : ι → ℤ}
    (hε : ∀ k, ε k = 1 ∨ ε k = -1) (u v : ι → ℤ) :
    signedPermVec σ ε u ⬝ᵥ signedPermVec σ ε v = u ⬝ᵥ v := by
  rw [dotProduct, dotProduct, ← Equiv.sum_comp σ fun k => u k * v k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [signedPermVec_apply, signedPermVec_apply]
  rcases hε k with h | h <;> simp [h]

theorem signedPermVec_eq_self {σ : Equiv.Perm (Fin d)} {ε w : Fin d → ℤ}
    (hσ : ∀ k : Fin d, (k : ℕ) < r → σ k = k)
    (hσ' : ∀ k : Fin d, r ≤ (k : ℕ) → r ≤ ((σ k : Fin d) : ℕ))
    (hε : ∀ k : Fin d, (k : ℕ) < r → ε k = 1)
    (hw : ∀ k : Fin d, r ≤ (k : ℕ) → w k = 0) : signedPermVec σ ε w = w := by
  funext k
  rw [signedPermVec_apply]
  by_cases hk : (k : ℕ) < r
  · rw [hσ k hk, hε k hk, one_mul]
  · rw [hw _ (hσ' k (by omega)), hw k (by omega), mul_zero]

def enumNewIdx (d r n : ℕ) : Finset (Fin d) :=
  {k : Fin d | r ≤ (k : ℕ) ∧ (k : ℕ) < r + n}

@[simp] theorem mem_enumNewIdx {k : Fin d} :
    k ∈ enumNewIdx d r n ↔ r ≤ (k : ℕ) ∧ (k : ℕ) < r + n := by simp [enumNewIdx]

theorem card_enumNewIdx (h : r + n ≤ d) : #(enumNewIdx d r n) = n := by
  refine Finset.card_eq_of_bijective (fun i hi => (⟨r + i, by omega⟩ : Fin d)) ?_ ?_ ?_
  · intro a ha
    rw [mem_enumNewIdx] at ha
    exact ⟨(a : ℕ) - r, by omega, by ext; simp; omega⟩
  · intro i hi
    refine mem_enumNewIdx.mpr ⟨Nat.le_add_right r i, ?_⟩
    change r + i < r + n
    omega
  · intro i j hi hj hij
    simpa using congrArg Fin.val hij

def enumCandidate (r n : ℕ) (S : Finset (Fin d)) (c : Fin d → ℤ) : Fin d → ℤ :=
  ∑ k ∈ S, Pi.single k (c k) + ∑ k ∈ enumNewIdx d r n, Pi.single k 1

theorem enumCandidate_apply (r n : ℕ) (S : Finset (Fin d)) (c : Fin d → ℤ) (m : Fin d) :
    enumCandidate r n S c m =
      (if m ∈ S then c m else 0) + (if m ∈ enumNewIdx d r n then 1 else 0) := by
  simp [enumCandidate, Finset.sum_pi_single]

theorem enumCandidate_congr {S : Finset (Fin d)} {c c' : Fin d → ℤ}
    (h : ∀ k ∈ S, c k = c' k) : enumCandidate r n S c = enumCandidate r n S c' := by
  funext m
  rw [enumCandidate_apply, enumCandidate_apply]
  by_cases hm : m ∈ S <;> simp [hm, h m]

theorem enumCandidate_dotProduct_self {S : Finset (Fin d)} {c : Fin d → ℤ}
    (hS : ∀ k ∈ S, (k : ℕ) < r) (hc : ∀ k ∈ S, c k = 1 ∨ c k = -1) (hn : r + n ≤ d) :
    enumCandidate r n S c ⬝ᵥ enumCandidate r n S c = #S + n := by
  have hdisj : Disjoint S (enumNewIdx d r n) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [mem_enumNewIdx] at ha'
    exact absurd (hS a ha) (by omega)
  have key : ∀ x : Fin d, enumCandidate r n S c x * enumCandidate r n S c x =
      if x ∈ S ∪ enumNewIdx d r n then 1 else 0 := by
    intro x
    rw [enumCandidate_apply]
    by_cases hx : x ∈ S
    · have hx' : x ∉ enumNewIdx d r n := Finset.disjoint_left.mp hdisj hx
      rcases hc x hx with h | h <;> simp [hx, hx', h]
    · by_cases hx' : x ∈ enumNewIdx d r n <;> simp [hx, hx']
  rw [dotProduct, Finset.sum_congr rfl fun x _ => key x, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, Finset.card_union_of_disjoint hdisj,
    card_enumNewIdx hn]
  ring

theorem enumCandidate_dotProduct_self_eq_three {S : Finset (Fin d)} {c : Fin d → ℤ}
    (hS : ∀ k ∈ S, (k : ℕ) < r) (hc : ∀ k ∈ S, c k = 1 ∨ c k = -1) (hcard : #S ≤ 3)
    (hn : r + (3 - #S) ≤ d) :
    enumCandidate r (3 - #S) S c ⬝ᵥ enumCandidate r (3 - #S) S c = 3 := by
  rw [enumCandidate_dotProduct_self hS hc hn]
  have h : ((3 - #S : ℕ) : ℤ) = 3 - (#S : ℤ) := by omega
  rw [h]; ring

theorem enumCandidate_dotProduct_of_support {S : Finset (Fin d)} {c w : Fin d → ℤ}
    (hw : ∀ k : Fin d, r ≤ (k : ℕ) → w k = 0) :
    enumCandidate r n S c ⬝ᵥ w = ∑ k ∈ S, c k * w k := by
  rw [dotProduct, Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
    show enumCandidate r n S c x * w x = (if x ∈ S then c x else 0) * w x by
      rw [enumCandidate_apply]
      by_cases hx : x ∈ enumNewIdx d r n
      · rw [mem_enumNewIdx] at hx
        simp [hw x hx.1]
      · simp [hx]]
  simp [ite_mul, Finset.sum_ite_mem]

def enumCandidates (d r : ℕ) : Set (Fin d → ℤ) :=
  {v | ∃ (S : Finset (Fin d)) (c : Fin d → ℤ), (∀ k ∈ S, (k : ℕ) < r) ∧ #S ≤ 3 ∧
    (∀ k ∈ S, c k = 1 ∨ c k = -1) ∧ r + (3 - #S) ≤ d ∧ v = enumCandidate r (3 - #S) S c}

theorem mem_enumCandidates_iff {v : Fin d → ℤ} :
    v ∈ enumCandidates d r ↔ ∃ (S : Finset (Fin d)) (c : Fin d → ℤ), (∀ k ∈ S, (k : ℕ) < r) ∧
      #S ≤ 3 ∧ (∀ k ∈ S, c k = 1 ∨ c k = -1) ∧ r + (3 - #S) ≤ d ∧
      v = enumCandidate r (3 - #S) S c := Iff.rfl

theorem finite_enumCandidates : (enumCandidates d r).Finite := by
  classical
  refine Set.Finite.subset (Set.finite_range
    (fun p : Finset (Fin d) × (Fin d → ({-1, 1} : Finset ℤ)) =>
      enumCandidate r (3 - #p.1) p.1 fun k => (p.2 k : ℤ))) ?_
  rintro v ⟨S, c, hS, hcard, hc, hlen, rfl⟩
  refine ⟨⟨S, fun k => if h : k ∈ S then ⟨c k, by rcases hc k h with h' | h' <;> simp [h']⟩
    else ⟨1, by simp⟩⟩, ?_⟩
  exact (enumCandidate_congr fun k hk => by simp [hk]).symm

theorem dotProduct_self_eq_three_of_mem_enumCandidates {v : Fin d → ℤ}
    (hv : v ∈ enumCandidates d r) : v ⬝ᵥ v = 3 := by
  obtain ⟨S, c, hS, hcard, hc, hlen, rfl⟩ := hv
  exact enumCandidate_dotProduct_self_eq_three hS hc hcard hlen

theorem enumCandidates_mono_of_castLE {d d' : ℕ} (h : d ≤ d') {v : Fin d → ℤ}
    (hv : v ∈ enumCandidates d r) :
    (fun k' : Fin d' => if hk : (k' : ℕ) < d then v ⟨k', hk⟩ else 0) ∈ enumCandidates d' r := by
  classical
  obtain ⟨S, c, hS, hcard, hc, hlen, rfl⟩ := hv
  refine ⟨S.map (Fin.castLEEmb h), fun k' => if hk : (k' : ℕ) < d then c ⟨k', hk⟩ else 0, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro k' hk'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hk'
    exact hS k hk
  · rwa [Finset.card_map]
  · intro k' hk'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hk'
    have hlt : ((Fin.castLEEmb h k : Fin d') : ℕ) < d := by simp
    simpa [hlt] using hc k hk
  · rw [Finset.card_map]; omega
  · funext k'
    rw [Finset.card_map, enumCandidate_apply]
    by_cases hk : (k' : ℕ) < d
    · rw [dif_pos hk, enumCandidate_apply]
      have hmemS : k' ∈ S.map (Fin.castLEEmb h) ↔ (⟨k', hk⟩ : Fin d) ∈ S := by
        refine ⟨fun hk' => ?_, fun hk' => Finset.mem_map.mpr ⟨⟨k', hk⟩, hk', by ext; simp⟩⟩
        obtain ⟨k, hkS, hkeq⟩ := Finset.mem_map.mp hk'
        have : k = (⟨k', hk⟩ : Fin d) := by
          ext; simpa using congrArg Fin.val hkeq
        exact this ▸ hkS
      by_cases hkS : (⟨k', hk⟩ : Fin d) ∈ S
      · rw [if_pos (hmemS.mpr hkS), if_pos hkS, dif_pos hk]
        congr 2
        simp [mem_enumNewIdx]
      · rw [if_neg (fun h' => hkS (hmemS.mp h')), if_neg hkS]
        congr 2
        simp [mem_enumNewIdx]
    · rw [dif_neg hk]
      have hkS : k' ∉ S.map (Fin.castLEEmb h) := by
        intro hk'
        obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hk'
        exact hk (by simp)
      have hkN : k' ∉ enumNewIdx d' r (3 - #S) := by
        rw [mem_enumNewIdx]
        omega
      rw [if_neg hkS, if_neg hkN, add_zero]

theorem card_add_card_le_of_forall_le (hr : r ≤ d) {A : Finset (Fin d)}
    (hA : ∀ k ∈ A, r ≤ (k : ℕ)) : r + #A ≤ d := by
  have hAsub : A ⊆ ({k : Fin d | ¬ ((k : ℕ) < r)} : Finset (Fin d)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact hA k hk
  have hcompl : #({k : Fin d | ¬ ((k : ℕ) < r)} : Finset (Fin d)) = d - r := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d)))
      (p := fun k : Fin d => (k : ℕ) < r)
    rw [Fin.card_filter_val_lt] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hle := Finset.card_le_card hAsub
  rw [hcompl] at hle
  omega

theorem exists_perm_fixing_lt (A B : Finset (Fin d))
    (hA : ∀ k ∈ A, r ≤ (k : ℕ)) (hB : ∀ k ∈ B, r ≤ (k : ℕ)) (hcard : #A = #B) :
    ∃ σ : Equiv.Perm (Fin d), (∀ k : Fin d, (k : ℕ) < r → σ k = k) ∧
      (∀ k : Fin d, r ≤ (k : ℕ) → r ≤ ((σ k : Fin d) : ℕ)) ∧
      ∀ k : Fin d, (k ∈ A ↔ σ k ∈ B) := by
  classical
  set p : Fin d → Prop := fun k => (k : ℕ) < r with hp
  set A' : Finset {k : Fin d // ¬ p k} := A.subtype (fun k => ¬ p k) with hA'
  set B' : Finset {k : Fin d // ¬ p k} := B.subtype (fun k => ¬ p k) with hB'
  have hcard' : #A' = #B' := by
    rw [hA', hB', Finset.card_subtype, Finset.card_subtype,
      Finset.filter_true_of_mem (fun k hk => by simp only [hp, not_lt]; exact hA k hk),
      Finset.filter_true_of_mem (fun k hk => by simp only [hp, not_lt]; exact hB k hk)]
    exact hcard
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq A' B' hcard'
  refine ⟨Equiv.Perm.subtypeCongr (Equiv.refl {k : Fin d // p k}) τ, ?_, ?_, ?_⟩
  · intro k hk
    rw [Equiv.Perm.subtypeCongr.apply]
    simp [hp, hk]
  · intro k hk
    have hnp : ¬ p k := by simp only [hp, not_lt]; omega
    rw [Equiv.Perm.subtypeCongr.apply, dif_neg hnp]
    have h2 := (τ ⟨k, hnp⟩).2
    simp only [hp, not_lt] at h2
    omega
  · intro k
    by_cases hk : p k
    · have hlt : (k : ℕ) < r := hk
      have hkA : k ∉ A := fun h => absurd (hA k h) (by omega)
      have heq : Equiv.Perm.subtypeCongr (Equiv.refl {k : Fin d // p k}) τ k = k := by
        rw [Equiv.Perm.subtypeCongr.apply]; simp [hk]
      rw [heq]
      have hkB : k ∉ B := fun h => absurd (hB k h) (by omega)
      simp [hkA, hkB]
    · have hval : Equiv.Perm.subtypeCongr (Equiv.refl {k : Fin d // p k}) τ k
          = ((τ ⟨k, hk⟩ : {k : Fin d // ¬ p k}) : Fin d) := by
        rw [Equiv.Perm.subtypeCongr.apply, dif_neg hk]
      rw [hval]
      constructor
      · intro hkA
        have h1 : (⟨k, hk⟩ : {k : Fin d // ¬ p k}) ∈ A' := by
          rw [hA']; exact Finset.mem_subtype.mpr hkA
        have h2 : τ ⟨k, hk⟩ ∈ B' := by
          rw [← hτ]; exact Finset.mem_map_equiv.mpr (by simpa using h1)
        rw [hB'] at h2
        exact Finset.mem_subtype.mp h2
      · intro hkB
        have h2 : τ ⟨k, hk⟩ ∈ B' := by rw [hB']; exact Finset.mem_subtype.mpr hkB
        rw [← hτ] at h2
        have h3 := Finset.mem_map_equiv.mp h2
        simp only [Equiv.symm_apply_apply] at h3
        rw [hA'] at h3
        exact Finset.mem_subtype.mp h3

theorem exists_signedPermVec_eq_enumCandidate (hr : r ≤ d) {u : Fin d → ℤ} (hu : u ⬝ᵥ u = 3) :
    ∃ (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ) (S : Finset (Fin d)),
      (∀ k : Fin d, (k : ℕ) < r → σ k = k) ∧
      (∀ k : Fin d, r ≤ (k : ℕ) → r ≤ ((σ k : Fin d) : ℕ)) ∧
      (∀ k : Fin d, (k : ℕ) < r → ε k = 1) ∧ (∀ k : Fin d, ε k = 1 ∨ ε k = -1) ∧
      (∀ k ∈ S, (k : ℕ) < r) ∧ #S ≤ 3 ∧ (∀ k ∈ S, u k = 1 ∨ u k = -1) ∧
      r + (3 - #S) ≤ d ∧
      signedPermVec σ ε u = enumCandidate r (3 - #S) S u := by
  classical
  have hTcard : #({i | u i ≠ 0} : Finset (Fin d)) = 3 :=
    card_support_eq_three_of_dotProduct_self_eq_three hu
  set S : Finset (Fin d) :=
    ({i | u i ≠ 0} : Finset (Fin d)).filter (fun i : Fin d => (i : ℕ) < r) with hSdef
  set A : Finset (Fin d) :=
    ({i | u i ≠ 0} : Finset (Fin d)).filter (fun i : Fin d => ¬ ((i : ℕ) < r)) with hAdef
  have hmemS : ∀ k : Fin d, k ∈ S ↔ (u k ≠ 0 ∧ (k : ℕ) < r) := by intro k; simp [hSdef]
  have hmemA : ∀ k : Fin d, k ∈ A ↔ (u k ≠ 0 ∧ ¬ ((k : ℕ) < r)) := by intro k; simp [hAdef]
  have hsplit : #S + #A = 3 := by
    rw [hSdef, hAdef, Finset.card_filter_add_card_filter_not, hTcard]
  have hAcard : #A = 3 - #S := by omega
  have hAle : ∀ k ∈ A, r ≤ (k : ℕ) := fun k hk => by have h := (hmemA k).mp hk; omega
  have hlen : r + #A ≤ d := card_add_card_le_of_forall_le hr hAle
  have hBcard : #(enumNewIdx d r #A) = #A := card_enumNewIdx hlen
  obtain ⟨σ, hσfix, hσge, hσAB⟩ := exists_perm_fixing_lt (r := r) (enumNewIdx d r #A) A
    (fun k hk => (mem_enumNewIdx.mp hk).1) hAle hBcard
  set ε : Fin d → ℤ := fun k =>
    if (k : ℕ) < r then 1 else if u (σ k) = 0 then 1 else u (σ k) with hεdef
  have hεlt : ∀ k : Fin d, (k : ℕ) < r → ε k = 1 := fun k hk => by simp [hεdef, hk]
  have hεsign : ∀ k : Fin d, ε k = 1 ∨ ε k = -1 := by
    intro k
    by_cases hk : (k : ℕ) < r
    · exact Or.inl (hεlt k hk)
    · by_cases h0 : u (σ k) = 0
      · left; simp [hεdef, hk, h0]
      · rcases eq_one_or_neg_one_of_dotProduct_self_eq_three hu h0 with h | h
        · left; simp [hεdef, hk, h]
        · right; simp [hεdef, hk, h]
  refine ⟨σ, ε, S, hσfix, hσge, hεlt, hεsign, fun k hk => ((hmemS k).mp hk).2, by omega,
    fun k hk => eq_one_or_neg_one_of_dotProduct_self_eq_three hu ((hmemS k).mp hk).1,
    by omega, ?_⟩
  funext k
  rw [signedPermVec_apply, enumCandidate_apply, ← hAcard]
  by_cases hk : (k : ℕ) < r
  · rw [hσfix k hk, hεlt k hk, one_mul]
    have hkB : k ∉ enumNewIdx d r #A := by rw [mem_enumNewIdx]; omega
    rw [if_neg hkB, add_zero]
    by_cases h0 : u k = 0
    · rw [if_neg fun h => ((hmemS k).mp h).1 h0, h0]
    · rw [if_pos ((hmemS k).mpr ⟨h0, hk⟩)]
  · have hkS : k ∉ S := fun h => hk ((hmemS k).mp h).2
    rw [if_neg hkS, zero_add]
    by_cases hkB : k ∈ enumNewIdx d r #A
    · rw [if_pos hkB]
      have hσA : σ k ∈ A := (hσAB k).mp hkB
      have h0 : u (σ k) ≠ 0 := ((hmemA _).mp hσA).1
      rw [hεdef]
      simp only [hk, if_false, h0, if_false]
      rcases eq_one_or_neg_one_of_dotProduct_self_eq_three hu h0 with h | h <;> simp [h]
    · rw [if_neg hkB]
      have hσA : σ k ∉ A := fun h => hkB ((hσAB k).mpr h)
      have hσge' : r ≤ ((σ k : Fin d) : ℕ) := hσge k (by omega)
      have h0 : u (σ k) = 0 := by
        by_contra h
        exact hσA ((hmemA _).mpr ⟨h, by omega⟩)
      rw [h0, mul_zero]

theorem exists_signedPerm_mem_enumCandidates {ι : Type*} (hr : r ≤ d)
    (w : ι → Fin d → ℤ) (hw : ∀ i, ∀ k : Fin d, r ≤ (k : ℕ) → w i k = 0)
    {u : Fin d → ℤ} (hu : u ⬝ᵥ u = 3) :
    ∃ (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ), (∀ k : Fin d, ε k = 1 ∨ ε k = -1) ∧
      (∀ i, signedPermVec σ ε (w i) = w i) ∧
      (∀ i, signedPermVec σ ε u ⬝ᵥ w i = u ⬝ᵥ w i) ∧
      signedPermVec σ ε u ∈ enumCandidates d r := by
  obtain ⟨σ, ε, S, hσfix, hσge, hεlt, hεsign, hSlt, hScard, hu1, hlen, heq⟩ :=
    exists_signedPermVec_eq_enumCandidate hr hu
  refine ⟨σ, ε, hεsign, fun i => signedPermVec_eq_self hσfix hσge hεlt (hw i), fun i => ?_,
    ⟨S, u, hSlt, hScard, hu1, hlen, heq⟩⟩
  rw [← signedPermVec_eq_self (r := r) hσfix hσge hεlt (hw i),
    signedPermVec_dotProduct σ hεsign, signedPermVec_eq_self (r := r) hσfix hσge hεlt (hw i)]

end CFSG.FeitThompson
