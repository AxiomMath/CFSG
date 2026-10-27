module

public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

@[expose] def f4CollCommTab : List (List (List ℕ)) := [
  [[], [26], [], [], [29], [], [31, 32], [], [], [], [], [36], [], [38, 39], [], [], [41, 42],
    [], [], [44], [], [], [], []],
  [[26], [], [], [28, 30], [], [31], [], [], [], [], [35, 37], [], [38], [], [], [], [], [43],
    [44, 45], [], [], [], [], []],
  [[], [], [], [29, 32], [31], [], [], [], [], [], [36, 39], [38], [], [], [], [], [43, 45],
    [44], [], [], [], [], [], []],
  [[], [28, 30], [29, 32], [], [], [], [], [], [], [34], [], [], [], [40], [41, 47], [42], [],
    [], [], [], [], [46], [], []],
  [[29], [], [31], [], [], [], [], [], [], [35, 40], [], [], [41], [], [43], [44, 46], [], [],
    [], [], [], [], [], []],
  [[], [31], [], [], [], [], [], [], [], [36, 42], [], [41], [], [43, 46], [44], [], [], [], [],
    [], [], [], [], []],
  [[31, 32], [], [], [], [], [], [], [], [], [37], [40], [], [43, 47], [], [], [45], [], [],
    [46], [], [], [], [], []],
  [[], [], [], [], [], [], [], [], [], [38, 45], [41, 46], [43], [44], [], [], [], [], [], [],
    [], [], [], [], []],
  [[], [], [], [], [], [], [], [], [], [39], [42], [44, 47], [], [45], [], [], [46], [], [], [],
    [], [], [], []],
  [[], [], [], [34], [35, 40], [36, 42], [37], [38, 45], [39], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [47], []],
  [[], [35, 37], [36, 39], [], [], [], [40], [41, 46], [42], [], [], [], [], [], [], [], [], [],
    [], [], [], [47], [], []],
  [[36], [], [38], [], [], [41], [], [43], [44, 47], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], []],
  [[], [38], [], [], [41], [], [43, 47], [44], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], []],
  [[38, 39], [], [], [40], [], [43, 46], [], [], [45], [], [], [], [], [], [], [], [], [], [47],
    [], [], [], [], []],
  [[], [], [], [41, 47], [43], [44], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], []],
  [[], [], [], [42], [44, 46], [], [45], [], [], [], [], [], [], [], [], [], [47], [], [], [],
    [], [], [], []],
  [[41, 42], [], [43, 45], [], [], [], [], [], [46], [], [], [], [], [], [], [47], [], [], [],
    [], [], [], [], []],
  [[], [43], [44], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], []],
  [[], [44, 45], [], [], [], [], [46], [], [], [], [], [], [], [47], [], [], [], [], [], [], [],
    [], [], []],
  [[44], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    []],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    []],
  [[], [], [], [46], [], [], [], [], [], [], [47], [], [], [], [], [], [], [], [], [], [], [],
    [], []],
  [[], [], [], [], [], [], [], [], [], [47], [], [], [], [], [], [], [], [], [], [], [], [], [],
    []],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    []]]

@[expose] def f4CollComm (a b : ℕ) : List ℕ :=
  (f4CollCommTab.getD (a - 24) []).getD (b - 24) []

theorem f4CollComm_check : f4PosPairs.all (fun e => f4CollComm e.1 e.2 ==
    ((f4OddCommutatorFactors.lookup e).getD []).map fun f => f.2.2) = true := by
  decide +kernel

theorem f4CollComm_eq {a b : ℕ} (ha : 24 ≤ a) (ha' : a ≤ 47) (hb : 24 ≤ b) (hb' : b ≤ 47)
    (hab : a ≠ b) :
    f4CollComm a b = ((f4OddCommutatorFactors.lookup (a, b)).getD []).map fun f => f.2.2 := by
  have h := List.all_eq_true.1 f4CollComm_check (a, b) (mem_f4PosPairs.2 ⟨ha, ha', hb, hb', hab⟩)
  simpa using h

@[expose] def f4CollReflTab : List (List ℕ) := [
  [1, 0, 2, 3, 4, 5, 6, 7, 15, 16, 17, 18, 19, 20, 33, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25,
    26, 34, 35, 36, 37, 38, 39, 14, 27, 28, 29, 30, 31, 32, 40, 41, 42, 43, 44, 45, 47, 46],
  [0, 2, 1, 3, 4, 8, 9, 10, 5, 6, 7, 11, 12, 14, 13, 15, 16, 17, 21, 22, 27, 18, 19, 23, 24, 28,
    29, 20, 25, 26, 30, 31, 32, 34, 33, 35, 36, 40, 41, 42, 37, 38, 39, 43, 44, 46, 45, 47],
  [0, 1, 5, 3, 6, 2, 4, 7, 8, 11, 13, 9, 12, 10, 14, 15, 18, 20, 16, 19, 17, 23, 25, 21, 26, 22,
    24, 30, 28, 31, 27, 29, 32, 33, 37, 35, 38, 34, 36, 39, 40, 43, 45, 41, 44, 42, 46, 47],
  [0, 1, 2, 4, 3, 7, 6, 5, 10, 9, 8, 12, 11, 13, 14, 17, 16, 15, 19, 18, 20, 22, 21, 24, 23, 26,
    25, 27, 29, 28, 32, 31, 30, 33, 34, 36, 35, 39, 38, 37, 42, 41, 40, 44, 43, 45, 46, 47]]

@[expose] def f4CollRefl (j p : ℕ) : ℕ :=
  (f4CollReflTab.getD j []).getD p 0

@[expose] def f4CollNode (j : ℕ) : Fin Tag.F4.rank :=
  ⟨j % 4, Nat.mod_lt _ (by decide)⟩

theorem f4CollRefl_check : ∀ j < 4, ∀ p < 48, f4CollRefl j p < 48 ∧
    List.ofFn (orbitCertRoot .F4 (f4CollRefl j p)) =
      List.ofFn (reflect .F4 (f4CollNode j) (orbitCertRoot .F4 p)) := by
  decide +kernel

@[expose] def f4CollWeylPerm (ω : List ℕ) (p : ℕ) : ℕ :=
  ω.foldr f4CollRefl p

@[expose] def f4CollStep : List ℕ → Option (List ℕ)
  | a :: b :: L =>
    if a = b then some L
    else if b < a ∧ 24 ≤ b ∧ a ≤ 47 then some (b :: a :: (f4CollComm a b ++ L))
    else (f4CollStep (b :: L)).map (a :: ·)
  | _ => none

@[expose] def f4CollNF : ℕ → List ℕ → List ℕ
  | 0, L => L
  | n + 1, L =>
    match f4CollStep L with
    | some L' => f4CollNF n L'
    | none => L

inductive F4CollMove where
  | root (g : ℕ)
  | weyl (ω : List ℕ)

@[expose] def F4CollMove.apply (n : ℕ) : F4CollMove → List ℕ → List ℕ
  | .root g, L => f4CollNF n (g :: (L ++ [g]))
  | .weyl ω, L => f4CollNF n (L.map (f4CollWeylPerm ω))

@[expose] def F4CollMove.valid : F4CollMove → List ℕ → Bool
  | .root _, _ => true
  | .weyl ω, L => ω.all (· < 4) && L.all (· < 48)

@[expose] def f4CollOK (n : ℕ) : List F4CollMove → List ℕ → List ℕ → Bool
  | [], L, L' => f4CollNF n L == f4CollNF n L'
  | m :: ms, L, L' => m.valid L && f4CollOK n ms (m.apply n L) L'

section Products

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def f4CollProd (L : List ℕ) : ModGL .F4 K :=
  (L.map fun p => f4x K p 1).prod

@[simp] theorem f4CollProd_nil : f4CollProd K [] = 1 := by
  simp [f4CollProd]

@[simp] theorem f4CollProd_cons (p : ℕ) (L : List ℕ) :
    f4CollProd K (p :: L) = f4x K p 1 * f4CollProd K L := by
  simp [f4CollProd]

theorem f4CollProd_append (L L' : List ℕ) :
    f4CollProd K (L ++ L') = f4CollProd K L * f4CollProd K L' := by
  simp [f4CollProd]

theorem f4x_one_mul_self [CharP K 2] (p : ℕ) : f4x K p 1 * f4x K p 1 = 1 := by
  rw [f4x, ← pinnedX_add, one_add_one_eq_two, CharTwo.two_eq_zero, pinnedX_zero]

variable (K) in
@[expose] noncomputable def f4CollWeylElt (ω : List ℕ) : ModGL .F4 K :=
  (ω.map fun j => weylElt .F4 K (f4CollNode j) 1).prod

theorem f4CollWeylElt_mem (ω : List ℕ) : f4CollWeylElt K ω ∈ adjointGroup .F4 K := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_adjointGroup _ 1

end Products

section Weyl

variable
  {K : Type} [Field K]

theorem weylElt_mul_f4x_mul_inv [CharP K 2] {j p : ℕ} (hj : j < 4) (hp : p < 48) (c : K) :
    weylElt .F4 K (f4CollNode j) 1 * f4x K p c * (weylElt .F4 K (f4CollNode j) 1)⁻¹ =
      f4x K (f4CollRefl j p) c := by
  obtain ⟨-, heq⟩ := f4CollRefl_check j hj p hp
  have hroot : IsRoot .F4 (orbitCertRoot .F4 p) :=
    isRoot_decodeVec_witness (by rw [show Tag.F4.witnesses.roots.length = 48 from rfl]; exact hp)
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4CollNode j) hroot
  have hε1 : ε = 1 := CharTwo.sq_injective (show ε ^ 2 = 1 ^ 2 by rw [one_pow, sq, hε])
  rw [f4x, h c, hε1, one_mul, ← List.ofFn_injective heq, f4x]

theorem f4CollWeylElt_conj [CharP K 2] :
    ∀ (ω : List ℕ), (∀ j ∈ ω, j < 4) → ∀ {p : ℕ}, p < 48 → ∀ c : K,
      f4CollWeylElt K ω * f4x K p c * (f4CollWeylElt K ω)⁻¹ = f4x K (f4CollWeylPerm ω p) c ∧
        f4CollWeylPerm ω p < 48
  | [], _, p, hp, c => by simp [f4CollWeylElt, f4CollWeylPerm, hp]
  | j :: ω, hω, p, hp, c => by
    obtain ⟨h1, h2⟩ := f4CollWeylElt_conj ω (fun i hi => hω i (List.mem_cons_of_mem _ hi)) hp c
    have hj := hω j List.mem_cons_self
    refine ⟨?_, (f4CollRefl_check j hj _ h2).1⟩
    have e : f4CollWeylElt K (j :: ω) = weylElt .F4 K (f4CollNode j) 1 * f4CollWeylElt K ω := by
      simp [f4CollWeylElt]
    rw [e, show f4CollWeylPerm (j :: ω) p = f4CollRefl j (f4CollWeylPerm ω p) from rfl,
      ← weylElt_mul_f4x_mul_inv hj h2, ← h1]
    group

theorem f4CollWeylElt_conj_prod [CharP K 2] {ω : List ℕ} (hω : ∀ j ∈ ω, j < 4) :
    ∀ (L : List ℕ), (∀ p ∈ L, p < 48) →
      f4CollWeylElt K ω * f4CollProd K L * (f4CollWeylElt K ω)⁻¹ =
        f4CollProd K (L.map (f4CollWeylPerm ω))
  | [], _ => by simp
  | p :: L, hL => by
    rw [List.map_cons, f4CollProd_cons, f4CollProd_cons,
      ← f4CollWeylElt_conj_prod hω L fun q hq => hL q (List.mem_cons_of_mem _ hq),
      ← (f4CollWeylElt_conj ω hω (hL p List.mem_cons_self) 1).1]
    group

end Weyl

section Collection

variable
  {K : Type} [Field K]

theorem f4x_one_mul_f4x_one_of_lt [CharP K 2] {a b : ℕ} (hb : 24 ≤ b) (hba : b < a)
    (ha : a ≤ 47) :
    f4x K a 1 * f4x K b 1 = f4x K b 1 * f4x K a 1 * f4CollProd K (f4CollComm a b) := by
  have hc := f4_even_positive_root_commutator_table.{0}.2.2.2.2 K a b (by omega) ha hb (by omega)
    (by omega) 1 1
  simp only [one_pow, mul_one] at hc
  have hcomm : ⁅f4x K a 1, f4x K b 1⁆ = f4CollProd K (f4CollComm a b) := by
    rw [f4CollComm_eq (by omega) ha hb (by omega) (by omega), f4CollProd, List.map_map]
    exact hc
  rw [← hcomm, commutatorElement_def, inv_eq_of_mul_eq_one_right (f4x_one_mul_self a),
    inv_eq_of_mul_eq_one_right (f4x_one_mul_self b)]
  calc f4x K a 1 * f4x K b 1
      = f4x K b 1 * (f4x K a 1 * f4x K a 1) * (f4x K b 1 * (f4x K a 1 * f4x K b 1)) := by
        rw [f4x_one_mul_self a, mul_one, ← mul_assoc, f4x_one_mul_self b, one_mul]
    _ = f4x K b 1 * f4x K a 1 * (f4x K a 1 * f4x K b 1 * f4x K a 1 * f4x K b 1) := by
        simp only [mul_assoc]

theorem f4CollProd_of_step [CharP K 2] :
    ∀ {L L' : List ℕ}, f4CollStep L = some L' → f4CollProd K L' = f4CollProd K L
  | [], _, h => by simp [f4CollStep] at h
  | [_], _, h => by simp [f4CollStep] at h
  | a :: b :: L, L', h => by
    simp only [f4CollStep] at h
    split_ifs at h with h1 h2
    · cases h
      subst h1
      rw [f4CollProd_cons, f4CollProd_cons, ← mul_assoc, f4x_one_mul_self, one_mul]
    · cases h
      obtain ⟨hba, hb, ha⟩ := h2
      rw [f4CollProd_cons, f4CollProd_cons, f4CollProd_append, f4CollProd_cons,
        f4CollProd_cons]
      conv_rhs => rw [← mul_assoc, f4x_one_mul_f4x_one_of_lt hb hba ha]
      simp only [mul_assoc]
    · obtain ⟨L'', hL'', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [f4CollProd_cons, f4CollProd_of_step hL'', ← f4CollProd_cons]

theorem f4CollProd_collect [CharP K 2] :
    ∀ (n : ℕ) (L : List ℕ), f4CollProd K (f4CollNF n L) = f4CollProd K L
  | 0, _ => rfl
  | n + 1, L => by
    rw [f4CollNF]
    split
    · next L' h => rw [f4CollProd_collect n L', f4CollProd_of_step h]
    · rfl

theorem F4CollMove.exists_conj [CharP K 2] (n : ℕ) (m : F4CollMove) (L : List ℕ)
    (h : m.valid L = true) :
    ∃ e ∈ adjointGroup .F4 K, e * f4CollProd K L * e⁻¹ = f4CollProd K (m.apply n L) := by
  cases m with
  | root g =>
    refine ⟨f4x K g 1, pinnedX_mem_adjointGroup _ _, ?_⟩
    rw [F4CollMove.apply, f4CollProd_collect, f4CollProd_cons, f4CollProd_append,
      inv_eq_of_mul_eq_one_right (f4x_one_mul_self g), f4CollProd_cons, f4CollProd_nil, mul_one,
      mul_assoc]
  | weyl ω =>
    simp only [F4CollMove.valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨f4CollWeylElt K ω, f4CollWeylElt_mem ω, by
      rw [F4CollMove.apply, f4CollProd_collect, f4CollWeylElt_conj_prod h.1 L h.2]⟩

theorem exists_conj_of_f4CollOK [CharP K 2] (n : ℕ) :
    ∀ (ms : List F4CollMove) (L L' : List ℕ), f4CollOK n ms L L' = true →
      ∃ g ∈ adjointGroup .F4 K, g * f4CollProd K L * g⁻¹ = f4CollProd K L'
  | [], L, L', h => by
    refine ⟨1, one_mem _, ?_⟩
    rw [f4CollOK, beq_iff_eq] at h
    rw [one_mul, inv_one, mul_one, ← f4CollProd_collect n L, h, f4CollProd_collect]
  | m :: ms, L, L', h => by
    rw [f4CollOK, Bool.and_eq_true] at h
    obtain ⟨e, he, heL⟩ := m.exists_conj (K := K) n L h.1
    obtain ⟨g, hg, hgL⟩ := exists_conj_of_f4CollOK n ms _ L' h.2
    refine ⟨g * e, mul_mem hg he, ?_⟩
    rw [← hgL, ← heL]
    group

end Collection

end CFSG.SeitzReduction
