module

public import CFSG.HardMathSupport.U4FF.ClassComb
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Combinatorics.Colex

public section

namespace CFSG.HardMathSupport.U4FF

theorem digits_sum_range_add_one (m : ℕ) : ∑ j ∈ Finset.range m, 2 ^ j + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem digits_sum_lt_pow {m : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.range m) :
    ∑ j ∈ C, 2 ^ j < 2 ^ m := by
  have h1 : ∑ j ∈ C, 2 ^ j ≤ ∑ j ∈ Finset.range m, 2 ^ j := Finset.sum_le_sum_of_subset hC
  have h2 := digits_sum_range_add_one m
  omega

theorem digits_sum_lt_sub_one {m : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.range m)
    (hne : C ≠ Finset.range m) : ∑ j ∈ C, 2 ^ j < 2 ^ m - 1 := by
  obtain ⟨i, hi, hiC⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hC, hne⟩)
  have h1 : ∑ j ∈ C, 2 ^ j ≤ ∑ j ∈ (Finset.range m).erase i, 2 ^ j :=
    Finset.sum_le_sum_of_subset (fun j hj => Finset.mem_erase.mpr
      ⟨fun h => hiC (h ▸ hj), hC hj⟩)
  have h2 : ∑ j ∈ (Finset.range m).erase i, 2 ^ j + 2 ^ i = ∑ j ∈ Finset.range m, 2 ^ j :=
    Finset.sum_erase_add _ _ hi
  have h3 := digits_sum_range_add_one m
  have h4 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  omega

theorem digits_eq_of_sum_eq {C C' : Finset ℕ} (h : ∑ j ∈ C, 2 ^ j = ∑ j ∈ C', 2 ^ j) :
    C = C' := by
  have h1 := congrArg (fun k => k.bitIndices.toFinset) h
  simpa only [Finset.toFinset_bitIndices_sum_two_pow] using h1

theorem exists_set_sum (m : ℕ) : ∀ e : ℕ, e < 2 ^ m →
    ∃ C : Finset ℕ, C ⊆ Finset.range m ∧ ∑ j ∈ C, 2 ^ j = e := by
  induction m with
  | zero =>
    intro e he
    rw [pow_zero] at he
    exact ⟨∅, Finset.empty_subset _, by rw [Finset.sum_empty]; omega⟩
  | succ k ih =>
    intro e he
    by_cases hlt : e < 2 ^ k
    · obtain ⟨C, hC, hs⟩ := ih e hlt
      refine ⟨C, fun x hx => Finset.mem_range.mpr ?_, hs⟩
      have := Finset.mem_range.mp (hC hx)
      omega
    · have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      obtain ⟨C, hC, hs⟩ := ih (e - 2 ^ k) (by omega)
      have hk : k ∉ C := fun h => by
        have := Finset.mem_range.mp (hC h)
        omega
      refine ⟨insert k C, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]
          exact Finset.mem_range.mpr (Nat.lt_succ_self k)
        · have := Finset.mem_range.mp (hC h)
          exact Finset.mem_range.mpr (by omega)
      · rw [Finset.sum_insert hk, hs]
        omega

theorem sum_ite_two_pow_eq_zero_iff (m : ℕ) (g : ℕ → Bool) :
    ∑ j ∈ Finset.range m, (if g j then 2 ^ j else 0) = 0 ↔
      ∀ j ∈ Finset.range m, g j = false := by
  rw [Finset.sum_eq_zero_iff]
  refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
  · by_contra hg
    have hg' : g j = true := by simpa using hg
    have := h j hj
    simp [hg'] at this
  · simp [h j hj]

theorem sum_ite_two_pow_eq_top_iff (m : ℕ) (g : ℕ → Bool) :
    ∑ j ∈ Finset.range m, (if g j then 2 ^ j else 0) = 2 ^ m - 1 ↔
      ∀ j ∈ Finset.range m, g j = true := by
  have hpt : ∀ j, (if g j then 2 ^ j else 0) + (if g j then 0 else 2 ^ j) = 2 ^ j := by
    intro j
    by_cases hg : g j = true <;> simp [hg]
  have hsum : ∑ j ∈ Finset.range m, (if g j then 2 ^ j else 0) +
      ∑ j ∈ Finset.range m, (if g j then 0 else 2 ^ j) = 2 ^ m - 1 := by
    rw [← Finset.sum_add_distrib]
    simp only [hpt]
    have h := digits_sum_range_add_one m
    omega
  have hz : ∑ j ∈ Finset.range m, (if g j then 0 else 2 ^ j) = 0 ↔
      ∀ j ∈ Finset.range m, g j = true := by
    rw [Finset.sum_eq_zero_iff]
    refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
    · by_contra hg
      have hg' : g j = false := by simpa using hg
      have := h j hj
      simp [hg'] at this
    · simp [h j hj]
  constructor
  · intro h
    exact hz.mp (by omega)
  · intro h
    have := hz.mpr h
    omega

theorem forall_range_two_mul_iff (n : ℕ) (P : ℕ → Prop) :
    (∀ j ∈ Finset.range (2 * n), P j) ↔ ∀ i : Fin n, P i ∧ P (n + i) := by
  constructor
  · intro h i
    have hi := i.isLt
    exact ⟨h i (Finset.mem_range.mpr (by omega)), h (n + i) (Finset.mem_range.mpr (by omega))⟩
  · intro h j hj
    rcases lt_or_ge j n with hjn | hjn
    · exact (h ⟨j, hjn⟩).1
    · have hj2 : j < 2 * n := Finset.mem_range.mp hj
      have h' : P (n + (j - n)) := (h ⟨j - n, by omega⟩).2
      have e : n + (j - n) = j := by omega
      rw [e] at h'
      exact h'

theorem digits_image_shift_eq {m d : ℕ} (hm : 1 ≤ m) {C : Finset ℕ}
    (hC : C ⊆ Finset.range m)
    (hmod : 2 ^ d * ∑ j ∈ C, 2 ^ j ≡ ∑ j ∈ C, 2 ^ j [MOD 2 ^ m - 1]) :
    C.image (fun i => (i + d) % m) = C := by
  have hinj : Set.InjOn (fun i => (i + d) % m) C := by
    intro i hi j hj h
    have hi' := Finset.mem_range.mp (hC hi)
    have hj' := Finset.mem_range.mp (hC hj)
    have h' : (i + d) % m = (j + d) % m := h
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' d h') hi' hj'
  have hcard : (C.image (fun i => (i + d) % m)).card = C.card :=
    Finset.card_image_of_injOn hinj
  have hsub : C.image (fun i => (i + d) % m) ⊆ Finset.range m := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  by_cases hfull : C = Finset.range m
  · have hcardC : C.card = m := by rw [hfull, Finset.card_range]
    have himg : C.image (fun i => (i + d) % m) = Finset.range m :=
      Finset.eq_of_subset_of_card_le hsub
        (le_of_eq (by rw [hcard, hcardC, Finset.card_range]))
    rw [himg, hfull]
  · have hne : C.image (fun i => (i + d) % m) ≠ Finset.range m := by
      intro h
      apply hfull
      apply Finset.eq_of_subset_of_card_le hC
      have h' := congrArg Finset.card h
      rw [hcard, Finset.card_range] at h'
      rw [Finset.card_range]
      omega
    have hval : ∑ j ∈ C.image (fun i => (i + d) % m), 2 ^ j ≡
        2 ^ d * ∑ j ∈ C, 2 ^ j [MOD 2 ^ m - 1] := by
      rw [Finset.sum_image hinj, Finset.mul_sum]
      refine Nat.ModEq.sum fun j _ => ?_
      have h1 : 2 ^ m ≡ 1 [MOD 2 ^ m - 1] := Nat.modEq_sub Nat.one_le_two_pow
      calc 2 ^ ((j + d) % m) = 2 ^ ((j + d) % m) * 1 ^ ((j + d) / m) := by
            rw [one_pow, mul_one]
        _ ≡ 2 ^ ((j + d) % m) * (2 ^ m) ^ ((j + d) / m) [MOD 2 ^ m - 1] :=
            (Nat.ModEq.refl _).mul (h1.symm.pow _)
        _ = 2 ^ d * 2 ^ j := by
            rw [← pow_mul, ← pow_add, Nat.mod_add_div, pow_add, mul_comm]
    have hsum : ∑ j ∈ C.image (fun i => (i + d) % m), 2 ^ j = ∑ j ∈ C, 2 ^ j :=
      Nat.ModEq.eq_of_lt_of_lt (hval.trans hmod)
        (digits_sum_lt_sub_one hsub hne) (digits_sum_lt_sub_one hC hfull)
    exact digits_eq_of_sum_eq hsum

theorem digits_mem_shift_iff {m d : ℕ} (hm : 1 ≤ m) {C : Finset ℕ} (hC : C ⊆ Finset.range m)
    (hmod : 2 ^ d * ∑ j ∈ C, 2 ^ j ≡ ∑ j ∈ C, 2 ^ j [MOD 2 ^ m - 1]) {k : ℕ} (hk : k < m) :
    (k + d) % m ∈ C ↔ k ∈ C := by
  have himg := digits_image_shift_eq hm hC hmod
  constructor
  · intro h
    have h' : (k + d) % m ∈ C.image (fun i => (i + d) % m) := by
      rw [himg]
      exact h
    obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp h'
    have hmod' : y ≡ k [MOD m] := Nat.ModEq.add_right_cancel' d hyk
    have hyk' : y = k := Nat.ModEq.eq_of_lt_of_lt hmod' (Finset.mem_range.mp (hC hy)) hk
    rw [← hyk']
    exact hy
  · intro h
    have h' : (k + d) % m ∈ C.image (fun i => (i + d) % m) :=
      Finset.mem_image_of_mem _ h
    rw [himg] at h'
    exact h'

namespace Lbl

variable {n : ℕ}

@[expose] def digA (l : Lbl n) (j : ℕ) : Bool :=
  if h : j < n then l.a ⟨j, h⟩
  else if h' : j < 2 * n then l.c ⟨j - n, by omega⟩ else false

@[expose] def digB (l : Lbl n) (j : ℕ) : Bool :=
  if h : j < n then l.b ⟨j, h⟩ else false

@[expose] def e1 (l : Lbl n) : ℕ :=
  (∑ i : Fin n, if l.a i then 2 ^ (i : ℕ) else 0) +
    ∑ i : Fin n, if l.c i then 2 ^ (n + (i : ℕ)) else 0

@[expose] def e2 (l : Lbl n) : ℕ := ∑ i : Fin n, if l.b i then 2 ^ (i : ℕ) else 0

@[expose] def setA (l : Lbl n) : Finset ℕ :=
  (Finset.range (2 * n)).filter (fun j => l.digA j = true)

@[expose] def setB (l : Lbl n) : Finset ℕ :=
  (Finset.range n).filter (fun j => l.digB j = true)

@[expose] def ofSets (CA CB : Finset ℕ) : Lbl n :=
  ⟨fun i => decide ((i : ℕ) ∈ CA), fun i => decide ((i : ℕ) ∈ CB),
    fun i => decide (n + (i : ℕ) ∈ CA)⟩

theorem digA_of_lt {l : Lbl n} {j : ℕ} (h : j < n) : l.digA j = l.a ⟨j, h⟩ := by
  unfold digA
  rw [dif_pos h]

theorem digA_of_mid {l : Lbl n} {j : ℕ} (h1 : n ≤ j) (h2 : j < 2 * n) :
    l.digA j = l.c ⟨j - n, by omega⟩ := by
  have h3 : ¬ j < n := by omega
  unfold digA
  rw [dif_neg h3, dif_pos h2]

theorem digA_of_le {l : Lbl n} {j : ℕ} (h : 2 * n ≤ j) : l.digA j = false := by
  have h1 : ¬ j < n := by omega
  have h2 : ¬ j < 2 * n := by omega
  unfold digA
  rw [dif_neg h1, dif_neg h2]

theorem digB_of_lt {l : Lbl n} {j : ℕ} (h : j < n) : l.digB j = l.b ⟨j, h⟩ := by
  unfold digB
  rw [dif_pos h]

theorem digB_of_le {l : Lbl n} {j : ℕ} (h : n ≤ j) : l.digB j = false := by
  have h1 : ¬ j < n := by omega
  unfold digB
  rw [dif_neg h1]

theorem digA_fin (l : Lbl n) (i : Fin n) : l.digA i = l.a i := digA_of_lt i.isLt

theorem digA_fin_hi (l : Lbl n) (i : Fin n) : l.digA (n + i) = l.c i := by
  have h1 : n ≤ n + (i : ℕ) := Nat.le_add_right n i
  have h2 : n + (i : ℕ) < 2 * n := by
    have := i.isLt
    omega
  rw [digA_of_mid h1 h2]
  congr 1
  apply Fin.ext
  show n + (i : ℕ) - n = (i : ℕ)
  omega

theorem digB_fin (l : Lbl n) (i : Fin n) : l.digB i = l.b i := digB_of_lt i.isLt

theorem mem_setA {l : Lbl n} {j : ℕ} : j ∈ l.setA ↔ j < 2 * n ∧ l.digA j = true := by
  simp only [setA, Finset.mem_filter, Finset.mem_range]

theorem mem_setB {l : Lbl n} {j : ℕ} : j ∈ l.setB ↔ j < n ∧ l.digB j = true := by
  simp only [setB, Finset.mem_filter, Finset.mem_range]

theorem setA_subset (l : Lbl n) : l.setA ⊆ Finset.range (2 * n) := fun j hj =>
  Finset.mem_range.mpr (mem_setA.mp hj).1

theorem setB_subset (l : Lbl n) : l.setB ⊆ Finset.range n := fun j hj =>
  Finset.mem_range.mpr (mem_setB.mp hj).1

theorem digA_true_iff_mem {l : Lbl n} {j : ℕ} (hj : j < 2 * n) :
    l.digA j = true ↔ j ∈ l.setA :=
  ⟨fun h => mem_setA.mpr ⟨hj, h⟩, fun h => (mem_setA.mp h).2⟩

theorem digB_true_iff_mem {l : Lbl n} {j : ℕ} (hj : j < n) :
    l.digB j = true ↔ j ∈ l.setB :=
  ⟨fun h => mem_setB.mpr ⟨hj, h⟩, fun h => (mem_setB.mp h).2⟩

theorem e1_eq_sum_ite (l : Lbl n) :
    l.e1 = ∑ j ∈ Finset.range (2 * n), if l.digA j then 2 ^ j else 0 := by
  unfold e1
  rw [two_mul, Finset.sum_range_add]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun j => if l.digA j then 2 ^ j else 0) n]
    exact Finset.sum_congr rfl fun i _ => by simp only [digA_fin]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => if l.digA (n + j) then 2 ^ (n + j) else 0) n]
    exact Finset.sum_congr rfl fun i _ => by simp only [digA_fin_hi]

theorem e2_eq_sum_ite (l : Lbl n) :
    l.e2 = ∑ j ∈ Finset.range n, if l.digB j then 2 ^ j else 0 := by
  unfold e2
  rw [← Fin.sum_univ_eq_sum_range (fun j => if l.digB j then 2 ^ j else 0) n]
  exact Finset.sum_congr rfl fun i _ => by simp only [digB_fin]

theorem e1_eq_sum_setA (l : Lbl n) : l.e1 = ∑ j ∈ l.setA, 2 ^ j := by
  rw [e1_eq_sum_ite, setA, Finset.sum_filter]

theorem e2_eq_sum_setB (l : Lbl n) : l.e2 = ∑ j ∈ l.setB, 2 ^ j := by
  rw [e2_eq_sum_ite, setB, Finset.sum_filter]

theorem e1_lt (l : Lbl n) : l.e1 < 2 ^ (2 * n) := by
  rw [e1_eq_sum_setA]
  exact digits_sum_lt_pow (setA_subset l)

theorem e2_lt (l : Lbl n) : l.e2 < 2 ^ n := by
  rw [e2_eq_sum_setB]
  exact digits_sum_lt_pow (setB_subset l)

theorem digA_ofSets (CA CB : Finset ℕ) {j : ℕ} (hj : j < 2 * n) :
    (ofSets CA CB : Lbl n).digA j = decide (j ∈ CA) := by
  by_cases hjn : j < n
  · exact (digA_of_lt (l := (ofSets CA CB : Lbl n)) hjn).trans rfl
  · rw [digA_of_mid (l := (ofSets CA CB : Lbl n)) (by omega : n ≤ j) hj]
    show decide (n + (j - n) ∈ CA) = decide (j ∈ CA)
    rw [(by omega : n + (j - n) = j)]

theorem digB_ofSets (CA CB : Finset ℕ) {j : ℕ} (hj : j < n) :
    (ofSets CA CB : Lbl n).digB j = decide (j ∈ CB) :=
  (digB_of_lt (l := (ofSets CA CB : Lbl n)) hj).trans rfl

theorem setA_ofSets {CA CB : Finset ℕ} (hCA : CA ⊆ Finset.range (2 * n)) :
    (ofSets CA CB : Lbl n).setA = CA := by
  ext j
  rw [mem_setA]
  constructor
  · rintro ⟨hj, h⟩
    rw [digA_ofSets CA CB hj, decide_eq_true_eq] at h
    exact h
  · intro hj
    have hj2 : j < 2 * n := Finset.mem_range.mp (hCA hj)
    refine ⟨hj2, ?_⟩
    rw [digA_ofSets CA CB hj2, decide_eq_true_eq]
    exact hj

theorem setB_ofSets {CA CB : Finset ℕ} (hCB : CB ⊆ Finset.range n) :
    (ofSets CA CB : Lbl n).setB = CB := by
  ext j
  rw [mem_setB]
  constructor
  · rintro ⟨hj, h⟩
    rw [digB_ofSets CA CB hj, decide_eq_true_eq] at h
    exact h
  · intro hj
    have hj2 : j < n := Finset.mem_range.mp (hCB hj)
    refine ⟨hj2, ?_⟩
    rw [digB_ofSets CA CB hj2, decide_eq_true_eq]
    exact hj

theorem exists_of_e {n : ℕ} {e₁ e₂ : ℕ} (h1 : e₁ < 2 ^ (2 * n)) (h2 : e₂ < 2 ^ n) :
    ∃ l : Lbl n, l.e1 = e₁ ∧ l.e2 = e₂ := by
  obtain ⟨CA, hCA, hsA⟩ := exists_set_sum (2 * n) e₁ h1
  obtain ⟨CB, hCB, hsB⟩ := exists_set_sum n e₂ h2
  refine ⟨ofSets CA CB, ?_, ?_⟩
  · rw [e1_eq_sum_setA, setA_ofSets hCA, hsA]
  · rw [e2_eq_sum_setB, setB_ofSets hCB, hsB]

theorem ext_of_e {l l' : Lbl n} (h1 : l.e1 = l'.e1) (h2 : l.e2 = l'.e2) : l = l' := by
  have hA : l.setA = l'.setA :=
    digits_eq_of_sum_eq (by rw [← e1_eq_sum_setA l, ← e1_eq_sum_setA l']; exact h1)
  have hB : l.setB = l'.setB :=
    digits_eq_of_sum_eq (by rw [← e2_eq_sum_setB l, ← e2_eq_sum_setB l']; exact h2)
  have hA' : ∀ j, l.digA j = l'.digA j := by
    intro j
    rw [Bool.eq_iff_iff]
    by_cases hj : j < 2 * n
    · have hmem : j ∈ l.setA ↔ j ∈ l'.setA := by rw [hA]
      rw [mem_setA, mem_setA] at hmem
      exact ⟨fun h => (hmem.mp ⟨hj, h⟩).2, fun h => (hmem.mpr ⟨hj, h⟩).2⟩
    · rw [digA_of_le (l := l) (j := j) (by omega), digA_of_le (l := l') (j := j) (by omega)]
  have hB' : ∀ j, l.digB j = l'.digB j := by
    intro j
    rw [Bool.eq_iff_iff]
    by_cases hj : j < n
    · have hmem : j ∈ l.setB ↔ j ∈ l'.setB := by rw [hB]
      rw [mem_setB, mem_setB] at hmem
      exact ⟨fun h => (hmem.mp ⟨hj, h⟩).2, fun h => (hmem.mpr ⟨hj, h⟩).2⟩
    · rw [digB_of_le (l := l) (j := j) (by omega), digB_of_le (l := l') (j := j) (by omega)]
  have ha : ∀ i : Fin n, l.a i = l'.a i := fun i => by
    have h := hA' (i : ℕ)
    rwa [digA_fin, digA_fin] at h
  have hb : ∀ i : Fin n, l.b i = l'.b i := fun i => by
    have h := hB' (i : ℕ)
    rwa [digB_fin, digB_fin] at h
  have hc : ∀ i : Fin n, l.c i = l'.c i := fun i => by
    have h := hA' (n + (i : ℕ))
    rwa [digA_fin_hi, digA_fin_hi] at h
  obtain ⟨a, b, c⟩ := l
  obtain ⟨a', b', c'⟩ := l'
  simp only [Lbl.mk.injEq]
  exact ⟨funext ha, funext hb, funext hc⟩

theorem e1_eq_zero_iff (l : Lbl n) : l.e1 = 0 ↔ ∀ i, l.a i = false ∧ l.c i = false := by
  rw [e1_eq_sum_ite, sum_ite_two_pow_eq_zero_iff (2 * n) l.digA, forall_range_two_mul_iff]
  simp only [digA_fin, digA_fin_hi]

theorem e1_eq_top_iff (l : Lbl n) :
    l.e1 = 2 ^ (2 * n) - 1 ↔ ∀ i, l.a i = true ∧ l.c i = true := by
  rw [e1_eq_sum_ite, sum_ite_two_pow_eq_top_iff (2 * n) l.digA, forall_range_two_mul_iff]
  simp only [digA_fin, digA_fin_hi]

theorem e2_eq_zero_iff (l : Lbl n) : l.e2 = 0 ↔ ∀ i, l.b i = false := by
  rw [e2_eq_sum_ite, sum_ite_two_pow_eq_zero_iff n l.digB]
  refine ⟨fun h i => ?_, fun h j hj => ?_⟩
  · have := h i (Finset.mem_range.mpr i.isLt)
    rwa [digB_fin] at this
  · rw [digB_of_lt (Finset.mem_range.mp hj)]
    exact h ⟨j, Finset.mem_range.mp hj⟩

theorem e2_eq_top_iff (l : Lbl n) : l.e2 = 2 ^ n - 1 ↔ ∀ i, l.b i = true := by
  rw [e2_eq_sum_ite, sum_ite_two_pow_eq_top_iff n l.digB]
  refine ⟨fun h i => ?_, fun h j hj => ?_⟩
  · have := h i (Finset.mem_range.mpr i.isLt)
    rwa [digB_fin] at this
  · rw [digB_of_lt (Finset.mem_range.mp hj)]
    exact h ⟨j, Finset.mem_range.mp hj⟩

theorem bitA_eq_digA [NeZero n] (l : Lbl n) (j : ℕ) :
    l.bitA j = l.digA (j % (2 * n)) := by
  have hn : 0 < n := NeZero.pos n
  have hlt : j % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
  unfold bitA digA
  by_cases h : j % (2 * n) < n
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, dif_pos hlt]

theorem bitB_eq_digB [NeZero n] (l : Lbl n) (j : ℕ) :
    l.bitB j = l.digB (j % n) := by
  have hn : 0 < n := NeZero.pos n
  unfold bitB digB
  rw [dif_pos (Nat.mod_lt j hn)]

theorem rotInv_of_modEq [NeZero n] (l : Lbl n) (d : ℕ)
    (h1 : 2 ^ d * l.e1 ≡ l.e1 [MOD 2 ^ (2 * n) - 1])
    (h2 : 2 ^ d * l.e2 ≡ l.e2 [MOD 2 ^ n - 1]) : l.RotInv d := by
  have hn : 0 < n := NeZero.pos n
  have hA : ∀ k < 2 * n, (k + d) % (2 * n) ∈ l.setA ↔ k ∈ l.setA := by
    intro k hk
    refine digits_mem_shift_iff (m := 2 * n) (by omega) l.setA_subset ?_ hk
    rw [← e1_eq_sum_setA]
    exact h1
  have hB : ∀ k < n, (k + d) % n ∈ l.setB ↔ k ∈ l.setB := by
    intro k hk
    refine digits_mem_shift_iff (m := n) (by omega) l.setB_subset ?_ hk
    rw [← e2_eq_sum_setB]
    exact h2
  unfold RotInv
  intro j
  refine ⟨?_, ?_⟩
  · rw [bitA_eq_digA, bitA_eq_digA, ← Nat.mod_add_mod j (2 * n) d, Bool.eq_iff_iff,
      digA_true_iff_mem (Nat.mod_lt _ (by omega) : (j % (2 * n) + d) % (2 * n) < 2 * n),
      digA_true_iff_mem (Nat.mod_lt _ (by omega) : j % (2 * n) < 2 * n)]
    exact hA _ (Nat.mod_lt _ (by omega))
  · rw [bitB_eq_digB, bitB_eq_digB, ← Nat.mod_add_mod j n d, Bool.eq_iff_iff,
      digB_true_iff_mem (Nat.mod_lt _ hn : (j % n + d) % n < n),
      digB_true_iff_mem (Nat.mod_lt _ hn : j % n < n)]
    exact hB _ (Nat.mod_lt _ hn)

end Lbl

end CFSG.HardMathSupport.U4FF
