module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

def maskOf (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ i

theorem testBit_maskOf (S : Finset ℕ) (j : ℕ) :
    (maskOf S).testBit j = decide (j ∈ S) := by
  unfold maskOf
  have h := Finset.toFinset_bitIndices_sum_two_pow S
  have h2 : (∑ i ∈ S, 2 ^ i).testBit j ↔ j ∈ S := by
    rw [← Nat.mem_bitIndices, ← List.mem_toFinset, h]
  cases hb : (∑ i ∈ S, 2 ^ i).testBit j <;> by_cases hj : j ∈ S <;> simp [hb, hj] at h2 ⊢

theorem maskOf_lt {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) : maskOf S < 2 ^ n := by
  have h1 : maskOf S ≤ ∑ i ∈ Finset.range n, 2 ^ i :=
    Finset.sum_le_sum_of_subset hS
  have h2 : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
    rw [Nat.geomSum_eq (le_refl 2)]
    simp
  have h3 := Nat.one_le_two_pow (n := n)
  omega

theorem bitCount_succ (n mask : ℕ) :
    bitCount (n + 1) mask = bitCount n mask + if mask.testBit n then 1 else 0 := by
  unfold bitCount
  rw [List.range_succ, List.foldl_append]
  by_cases h : mask.testBit n <;> simp [h]

theorem bitCount_eq_card (n mask : ℕ) :
    bitCount n mask = ((Finset.range n).filter fun i => mask.testBit i).card := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih =>
    rw [bitCount_succ, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : mask.testBit n <;> simp [h]

theorem bitCount_maskOf {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) :
    bitCount n (maskOf S) = S.card := by
  rw [bitCount_eq_card]
  have hfilter : ((Finset.range n).filter fun i => (maskOf S).testBit i) = S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, testBit_maskOf, decide_eq_true_eq]
    constructor
    · rintro ⟨-, hi⟩
      exact hi
    · intro hi
      exact ⟨Finset.mem_range.mp (hS hi), by simp [hi]⟩
  rw [hfilter]

theorem maskAllTrue_maskOf {B : Array Bool} {S : Finset ℕ} {n : ℕ}
    (hS : S ⊆ Finset.range n) (hB : ∀ i ∈ S, B[i]! = true) :
    maskAllTrue B (maskOf S) n = true := by
  unfold maskAllTrue
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  rw [testBit_maskOf]
  by_cases hmem : i ∈ S
  · simp [hmem, hB i hmem]
  · simp [hmem]

theorem maskClosed_maskOf {M : Array (Array ℕ)} {S : Finset ℕ} {n : ℕ}
    (hS : S ⊆ Finset.range n)
    (hclosed : ∀ i ∈ S, ∀ j ∈ S, (M[i]!)[j]! ∈ S) :
    maskClosed M (maskOf S) n = true := by
  unfold maskClosed
  rw [List.all_eq_true]
  intro i hi
  by_cases hiS : i ∈ S
  · simp only [testBit_maskOf, hiS, decide_true, Bool.not_true, Bool.false_or]
    rw [List.all_eq_true]
    intro j hj
    by_cases hjS : j ∈ S
    · simp [testBit_maskOf, hjS, hclosed i hiS j hjS]
    · simp [testBit_maskOf, hjS]
  · simp [testBit_maskOf, hiS]

theorem normalizesMask_maskOf {row : Array ℕ} {S : Finset ℕ} {n : ℕ}
    (hrow : ∀ i ∈ S, row[i]! ∈ S) :
    normalizesMask row (maskOf S) n = true := by
  unfold normalizesMask
  rw [List.all_eq_true]
  intro i _
  by_cases hiS : i ∈ S
  · simp [testBit_maskOf, hiS, hrow i hiS]
  · simp [testBit_maskOf, hiS]

theorem maskOf_subset_range {S : Finset ℕ} {n : ℕ} (hS : S ⊆ Finset.range n) :
    maskOf S ∈ Finset.range (2 ^ n) :=
  Finset.mem_range.mpr (maskOf_lt hS)

private def idxFold (A : Array ℕ) (m : ℕ) : Std.HashMap ℕ ℕ :=
  (List.range m).foldl (fun (r : Std.HashMap ℕ ℕ) i => r.insert (A[i]!) i) {}

private theorem idxMapOf_eq_idxFold (A : Array ℕ) : idxMapOf A = idxFold A A.size := rfl

private theorem idxFold_succ (A : Array ℕ) (m : ℕ) :
    idxFold A (m + 1) = (idxFold A m).insert (A[m]!) m := by
  unfold idxFold
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem idxFold_spec (A : Array ℕ) :
    ∀ m ≤ A.size, ∀ p < m,
      (idxFold A m).getD (A[p]!) A.size < m ∧
        A[(idxFold A m).getD (A[p]!) A.size]! = A[p]! := by
  intro m
  induction m with
  | zero => intro _ p hp; omega
  | succ m ih =>
    intro hm p hp
    rw [idxFold_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
    · have hprev := ih (by omega) p hp
      have hins := Std.HashMap.getD_insert (m := idxFold A m) (k := A[m]!) (a := A[p]!)
        (v := m) (fallback := A.size)
      by_cases hbeq : A[m]! == A[p]!
      · rw [if_pos hbeq] at hins
        rw [hins]
        exact ⟨by omega, by rwa [beq_iff_eq] at hbeq⟩
      · rw [if_neg hbeq] at hins
        rw [hins]
        exact ⟨by omega, hprev.2⟩
    · rw [Std.HashMap.getD_insert_self]
      exact ⟨by omega, rfl⟩

theorem idxMapOf_getD_spec (A : Array ℕ) {p : ℕ} (hp : p < A.size) :
    (idxMapOf A).getD (A[p]!) A.size < A.size ∧
      A[(idxMapOf A).getD (A[p]!) A.size]! = A[p]! := by
  rw [idxMapOf_eq_idxFold]
  exact idxFold_spec A A.size le_rfl p hp

theorem codePow.go_zero (a acc : ℕ) : codePow.go a 0 acc = acc := by
  rw [codePow.go.eq_def]

theorem codePow.go_succ (a n acc : ℕ) :
    codePow.go a (n + 1) acc = codePow.go a n (Code.mul acc a) := by
  rw [codePow.go.eq_def]

theorem codePow_eq_go (a n : ℕ) : codePow a n = codePow.go a n Code.one := by
  rw [codePow.eq_def]

theorem codePow_go_mul (a n acc : ℕ) :
    codePow.go a n (Code.mul acc a) = Code.mul (codePow.go a n acc) a := by
  induction n generalizing acc with
  | zero => rw [codePow.go_zero, codePow.go_zero]
  | succ n ih =>
    rw [codePow.go_succ, codePow.go_succ]
    exact ih (Code.mul acc a)

theorem codePow_succ {a : ℕ} (ha : a < 2 ^ 36) (n : ℕ) :
    codePow a (n + 1) = Code.mul (codePow a n) a := by
  have h1 : Code.mul Code.one a = a := EnumCert.code_one_mul_of_lt ha
  have hgo := codePow_go_mul a n Code.one
  rw [h1] at hgo
  calc
    codePow a (n + 1) = codePow.go a (n + 1) Code.one := codePow_eq_go a (n + 1)
    _ = codePow.go a n (Code.mul Code.one a) := codePow.go_succ a n Code.one
    _ = codePow.go a n a := by rw [h1]
    _ = Code.mul (codePow.go a n Code.one) a := hgo
    _ = Code.mul (codePow a n) a := by rw [codePow_eq_go]

namespace EnumCert

variable {gens : List ℕ} {E : List ℕ}

theorem code_pow (h : EnumCert gens E) {x : V₀ ≃ₗ[ZMod 2] V₀}
    (hx : x ∈ codeSubgroup gens) (n : ℕ) :
    h.code (x ^ n) = codePow (h.code x) n := by
  induction n with
  | zero =>
    rw [pow_zero, h.code_one, codePow_eq_go, codePow.go_zero]
  | succ n ih =>
    rw [pow_succ, h.code_mul (Subgroup.pow_mem (codeSubgroup gens) hx n) hx, ih,
      codePow_succ (h.lt _ (h.code_mem hx))]

theorem pow2K_iff (h : EnumCert gens E) {x : V₀ ≃ₗ[ZMod 2] V₀}
    (hx : x ∈ codeSubgroup gens) :
    pow2K (h.code x) = true ↔ x ^ 16 = 1 := by
  have hcode : h.code (x ^ 16) = codePow (h.code x) 16 := h.code_pow hx 16
  constructor
  · intro hp
    have hp' : codePow (h.code x) 16 = Code.one := by
      simpa [pow2K, beq_iff_eq] using hp
    have hx16 := h.hasCode_code (Subgroup.pow_mem (codeSubgroup gens) hx 16)
    rw [hcode, hp'] at hx16
    exact Code.HasCode.eq_of_equiv hx16 Code.hasCode_one
  · intro hp
    simp only [pow2K, beq_iff_eq]
    rw [← hcode, hp, h.code_one]

theorem pow2K_eq_false_iff (h : EnumCert gens E) {x : V₀ ≃ₗ[ZMod 2] V₀}
    (hx : x ∈ codeSubgroup gens) :
    pow2K (h.code x) = false ↔ x ^ 16 ≠ 1 := by
  rw [Bool.eq_false_iff]
  exact not_congr (pow2K_iff h hx)

theorem elem_one (h : EnumCert gens E) : h.elem Code.one = 1 := by
  rw [← h.code_one]
  exact h.elem_code (Subgroup.one_mem _)

theorem elem_mul (h : EnumCert gens E) {c d : ℕ} (hc : c ∈ E) (hd : d ∈ E) :
    h.elem (Code.mul c d) = h.elem c * h.elem d := by
  have hmem : h.elem c * h.elem d ∈ codeSubgroup gens :=
    Subgroup.mul_mem (H := codeSubgroup gens) (h.elem_mem hc) (h.elem_mem hd)
  rw [← h.elem_code hmem, h.code_mul (h.elem_mem hc) (h.elem_mem hd),
    h.code_elem hc, h.code_elem hd]

theorem elem_inv (h : EnumCert gens E) {c d : ℕ} (hc : c ∈ E) (hd : d ∈ E)
    (hmul : Code.mul c d = Code.one) : h.elem d = (h.elem c)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← h.elem_mul hc hd, hmul, h.elem_one]

theorem elem_inj (h : EnumCert gens E) {c d : ℕ} (hc : c ∈ E) (hd : d ∈ E)
    (heq : h.elem c = h.elem d) : c = d := by
  rw [← h.code_elem hc, ← h.code_elem hd, heq]

end EnumCert

theorem idxMapOf_getD_mem {A : Array ℕ} {x : ℕ} (hx : x ∈ A) :
    (idxMapOf A).getD x A.size < A.size ∧ A[(idxMapOf A).getD x A.size]! = x := by
  obtain ⟨p, hp, hpx⟩ := Array.mem_iff_getElem.mp hx
  have hpx' : A[p]! = x := by
    rw [array_getElem!_eq_getElem_of_lt hp]
    exact hpx
  have h := idxMapOf_getD_spec A hp
  rw [hpx'] at h
  exact h

example {A : Array ℕ} {x : ℕ} (h : x ∈ A.toList) : x ∈ A := Array.mem_toList_iff.mp h
example {A : Array ℕ} {x : ℕ} (h : x ∈ A) : x ∈ A.toList := Array.mem_toList_iff.mpr h

theorem hasCode_inv_of_mul_eq_one {g : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) a) (hmul : Code.mul a b = Code.one) :
    Code.HasCode ((g⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) b := by
  obtain ⟨H, hH⟩ := exists_equiv_of_mul_eq_one (EnumCert.code_mul_comm_one hmul)
  have hHg : H = g⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have hm0 := Code.HasCode.mul hg hH
    rw [hmul] at hm0
    exact Code.HasCode.eq_of_equiv hm0 Code.hasCode_one
  rwa [hHg] at hH

theorem foldl_push_any {α β : Type*} (l : List β) (f : β → Option α) (acc : Array α)
    (p : α → Bool) :
    (l.foldl (fun acc b => (f b).elim acc (fun a => acc.push a)) acc).any p =
      (acc.any p || l.any fun b => (f b).elim false (fun a => p a)) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    cases hb : f b with
    | none => simp [hb, List.any_cons]
    | some a => simp [hb, Array.any_push, List.any_cons, Bool.or_assoc]

theorem foldl_push_any_ite {α β : Type*} (l : List β) (cond : β → Bool) (val : β → α)
    (acc : Array α) (p : α → Bool) :
    (l.foldl (fun acc b => if cond b then acc else acc.push (val b)) acc).any p =
      (acc.any p || l.any fun b => (!cond b && p (val b))) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    by_cases hb : cond b
    · simp [hb, List.any_cons]
    · simp [hb, List.any_cons, Array.any_push, Bool.or_assoc]

theorem testBit_one_shift (i j : ℕ) : (1 <<< j).testBit i = decide (i = j) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  exact Bool.decide_congr eq_comm

theorem testBit_or_pow (m j i : ℕ) :
    (m ||| (1 <<< j)).testBit i = (m.testBit i || decide (i = j)) := by
  rw [Nat.testBit_lor, testBit_one_shift]
theorem foldl_or_pow_testBit (n mask : ℕ) (f : ℕ → Bool) (j : ℕ) :
    ((List.range n).foldl (fun m i => if f i then m ||| (1 <<< i) else m) mask).testBit j =
      (mask.testBit j || (j < n && f j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hfn : f n
    · rw [if_pos hfn, testBit_or_pow, ih]
      by_cases hj : j < n
      · have hjn : j ≠ n := by omega
        have hlt : j < n + 1 := by omega
        simp [hj, hjn, hlt]
      · by_cases hjn : j = n
        · simp [hjn, hfn]
        · have hlt : ¬ j < n + 1 := by omega
          simp [hj, hjn, hlt]
    · rw [if_neg hfn, ih]
      by_cases hj : j < n
      · have hlt : j < n + 1 := by omega
        simp [hj, hlt]
      · by_cases hjn : j = n
        · simp [hjn, hfn]
        · have hlt : ¬ j < n + 1 := by omega
          simp [hj, hjn, hlt]


theorem centralMaskTable_testBit (A K : Array ℕ) {h i : ℕ} (hh : h < K.size)
    (hi : i < A.size) :
    ((centralMaskTable A K)[h]!).testBit i = true ↔
      (Code.mul (K[h]!) (A[i]!) == Code.mul (A[i]!) (K[h]!)) = true := by
  unfold centralMaskTable
  rw [array_getElem!_eq_getElem_of_lt (by simpa using hh)]
  simp only [Array.getElem_ofFn]
  rw [foldl_or_pow_testBit]
  simp [hi]

end CFSG.GF2Type.Smith1979W3.Cert690

end
