module

public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
public import Mathlib.Data.List.GetD

public section

namespace CFSG.HardMathSupport.Timmesfeld.RootAut

open TauCeti

variable {n : ℕ}

@[expose] def coordReflect (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (x : Fin n → ℤ) :
    Fin n → ℤ :=
  x - (∑ j, M i j * x j) • Pi.single i 1

inductive IsOrbitRoot (M : Matrix (Fin n) (Fin n) ℤ) : (Fin n → ℤ) → Prop
  | single (i : Fin n) : IsOrbitRoot M (Pi.single i 1)
  | reflect (i : Fin n) {x : Fin n → ℤ} : IsOrbitRoot M x → IsOrbitRoot M (coordReflect M i x)

@[expose] def ofList (l : List ℤ) : Fin n → ℤ := fun j => l.getD j 0

theorem getD_ofFn (f : Fin n → ℤ) (i : Fin n) : (List.ofFn f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem ofList_ofFn (f : Fin n → ℤ) : ofList (n := n) (List.ofFn f) = f :=
  funext fun i => getD_ofFn f i

@[expose] def reflectList (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (l : List ℤ) : List ℤ :=
  List.ofFn (coordReflect M i (ofList l))

theorem reflectList_ofFn (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (x : Fin n → ℤ) :
    reflectList M i (List.ofFn x) = List.ofFn (coordReflect M i x) := by
  rw [reflectList, ofList_ofFn]

@[expose] def orbitStep (M : Matrix (Fin n) (Fin n) ℤ) (L : List (List ℤ)) : List (List ℤ) :=
  (L ++ L.flatMap fun l => (List.finRange n).map fun i => reflectList M i l).dedup

@[expose] def orbitIter (M : Matrix (Fin n) (Fin n) ℤ) : ℕ → List (List ℤ)
  | 0 => ((List.finRange n).map fun i => List.ofFn (Pi.single i 1 : Fin n → ℤ)).dedup
  | k + 1 => orbitStep M (orbitIter M k)

theorem nodup_orbitIter (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : (orbitIter M k).Nodup := by
  cases k <;> simp only [orbitIter, orbitStep] <;> exact List.nodup_dedup _

theorem mem_orbitIter (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) {l : List ℤ}
    (hl : l ∈ orbitIter M k) : ∃ x, IsOrbitRoot M x ∧ l = List.ofFn x := by
  induction k generalizing l with
  | zero =>
    simp only [orbitIter, List.mem_dedup, List.mem_map, List.mem_finRange, true_and] at hl
    obtain ⟨i, rfl⟩ := hl
    exact ⟨_, .single i, rfl⟩
  | succ k ih =>
    simp only [orbitIter, orbitStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and] at hl
    rcases hl with hl | ⟨l', hl', i, rfl⟩
    · exact ih hl
    · obtain ⟨x, hx, rfl⟩ := ih hl'
      exact ⟨_, .reflect i hx, reflectList_ofFn M i x⟩

@[expose] def closedB (M : Matrix (Fin n) (Fin n) ℤ) (L : List (List ℤ)) : Bool :=
  ((List.finRange n).all fun i => List.ofFn (Pi.single i 1 : Fin n → ℤ) ∈ L) &&
    L.all fun l => (List.finRange n).all fun i => reflectList M i l ∈ L

theorem ofFn_mem_of_closedB {M : Matrix (Fin n) (Fin n) ℤ} {L : List (List ℤ)}
    (h : closedB M L = true) {x : Fin n → ℤ} (hx : IsOrbitRoot M x) : List.ofFn x ∈ L := by
  simp only [closedB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq] at h
  induction hx with
  | single i => exact h.1 i
  | reflect i _ ih =>
    rw [← reflectList_ofFn]
    exact h.2 _ ih i

@[expose] def orbitOK (M : Matrix (Fin n) (Fin n) ℤ) (N k : ℕ) : Bool :=
  closedB M (orbitIter M k) && (orbitIter M k).length == N

theorem ncard_orbit_of_orbitOK {M : Matrix (Fin n) (Fin n) ℤ} {N k : ℕ}
    (h : orbitOK M N k = true) : {x | IsOrbitRoot M x}.ncard = N := by
  classical
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hc, hlen⟩ := h
  have himage : List.ofFn '' {x | IsOrbitRoot M x} = {l | l ∈ orbitIter M k} := by
    ext l
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ofFn_mem_of_closedB hc hx
    · intro hl
      obtain ⟨x, hx, rfl⟩ := mem_orbitIter M k hl
      exact ⟨x, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ List.ofFn_injective, himage, ← hlen,
    ← List.toFinset_card_of_nodup (nodup_orbitIter M k)]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext l
  simp

@[expose] def mulVecList (M : Matrix (Fin n) (Fin n) ℤ) (l : List ℤ) : List ℤ :=
  List.ofFn fun i => ∑ j, M i j * l.getD j 0

@[expose] def walkList (M : Matrix (Fin n) (Fin n) ℤ) : ℕ → List ℤ
  | 0 => List.replicate n 1
  | k + 1 => mulVecList M (walkList M k)

theorem walkList_perm {M : Matrix (Fin n) (Fin n) ℤ} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j, M (σ i) (σ j) = M i j) (k : ℕ) (i : Fin n) :
    (walkList M k).getD (σ i) 0 = (walkList M k).getD i 0 := by
  induction k generalizing i with
  | zero =>
    simp only [walkList]
    rw [List.getD_replicate (x := (1 : ℤ)) (σ i).2, List.getD_replicate (x := (1 : ℤ)) i.2]
  | succ k ih =>
    simp only [walkList, mulVecList, getD_ofFn]
    rw [← Equiv.sum_comp σ]
    exact Finset.sum_congr rfl fun j _ => by rw [hσ, ih]

@[expose] def sepB (M : Matrix (Fin n) (Fin n) ℤ) (K : ℕ) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide (i = j) || (List.range K).any fun k =>
      (walkList M k).getD i 0 != (walkList M k).getD j 0 ||
        (walkList M.transpose k).getD i 0 != (walkList M.transpose k).getD j 0

theorem eq_one_of_sepB {M : Matrix (Fin n) (Fin n) ℤ} {K : ℕ} (h : sepB M K = true)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i j, M (σ i) (σ j) = M i j) : σ = 1 := by
  have hσT : ∀ i j, M.transpose (σ i) (σ j) = M.transpose i j := fun i j => hσ j i
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  by_contra hne
  simp only [sepB, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true, List.mem_range, bne_iff_ne] at h
  rcases h (σ i) i with h1 | ⟨k, -, h2 | h2⟩
  · exact hne h1
  · exact h2 (walkList_perm hσ k i)
  · exact h2 (walkList_perm hσT k i)

@[expose] def rigidTypes : List DynkinType :=
  [.A 1, .B 2, .B 3, .B 4, .B 5, .B 6, .B 7, .B 8, .C 3, .C 4, .C 5, .C 6, .C 7, .C 8,
    .E7, .E8, .F4, .G2]

@[expose] def countTypes : List DynkinType :=
  [.A 2, .A 3, .A 4, .A 5, .A 6, .A 7, .A 8, .D 4, .D 5, .D 6, .D 7, .D 8, .E6]

@[expose] def rigidOK (t : DynkinType) : Bool :=
  sepB t.cartanMatrix (2 * t.rank)

@[expose] def countOK (t : DynkinType) : Bool :=
  orbitOK t.cartanMatrix t.numRoots 30

theorem mem_rigidTypes_or_mem_countTypes {t : DynkinType} (ht : t.Valid) (hr : t.rank ≤ 8) :
    t ∈ rigidTypes ∨ t ∈ countTypes := by
  cases t with
  | A m =>
    simp only [DynkinType.valid_A, DynkinType.rank_A] at ht hr
    interval_cases m <;> simp [rigidTypes, countTypes]
  | B m =>
    simp only [DynkinType.valid_B, DynkinType.rank_B] at ht hr
    interval_cases m <;> simp [rigidTypes, countTypes]
  | C m =>
    simp only [DynkinType.valid_C, DynkinType.rank_C] at ht hr
    interval_cases m <;> simp [rigidTypes, countTypes]
  | D m =>
    simp only [DynkinType.valid_D, DynkinType.rank_D] at ht hr
    interval_cases m <;> simp [rigidTypes, countTypes]
  | E6 => simp [rigidTypes, countTypes]
  | E7 => simp [rigidTypes, countTypes]
  | E8 => simp [rigidTypes, countTypes]
  | F4 => simp [rigidTypes, countTypes]
  | G2 => simp [rigidTypes, countTypes]

theorem numRoots_of_mem_countTypes {t : DynkinType} (ht : t ∈ countTypes) :
    (2 ≤ t.rank ∧ t.numRoots = t.rank * (t.rank + 1)) ∨
      (4 ≤ t.rank ∧ t.numRoots = 2 * t.rank * (t.rank - 1)) ∨
      (t.rank = 6 ∧ t.numRoots = 72) := by
  simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

end CFSG.HardMathSupport.Timmesfeld.RootAut
