module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerUnitaryBasic
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOrbit

public section

namespace CFSG.AGLEmbedding

open CFSG.Fischer CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Matrix

@[expose] def mulD (s d : ℕ) : ℕ :=
  ((s % 2) * (d % 2) + (s / 2) * (d / 2)) % 2 +
    2 * (((s % 2) * (d / 2) + (s / 2) * (d % 2) + (s / 2) * (d / 2)) % 2)

@[expose] def smulN : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, s, c => mulD s (c % 4) + 4 * smulN n s (c / 4)

@[expose] def addN : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => ((a % 4) ^^^ (b % 4)) + 4 * addN n (a / 4) (b / 4)

@[expose] def nzCnt : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, c => (if c % 4 = 0 then 0 else 1) + nzCnt n (c / 4)

@[expose] def applyP (n : ℕ) (cols : List ℕ) (c : ℕ) : ℕ :=
  (List.range n).foldl (fun acc j => addN n acc (smulN n ((c / 4 ^ j) % 4) (cols.getD j 0))) 0

@[expose] def colsOf {n : ℕ} (A : Matrix (Fin n) (Fin n) F4) : List ℕ :=
  (List.range n).map fun j => if h : j < n then codeOf (fun i => A i ⟨j, h⟩) else 0

theorem code_val_lt (x : F4) : x.code.val < 4 := x.code.2

theorem codeOf_succ {n : ℕ} (v : Fin (n + 1) → F4) :
    codeOf v = (v 0).code.val + 4 * codeOf (Fin.tail v) := rfl

theorem codeOf_mod {n : ℕ} (v : Fin (n + 1) → F4) : codeOf v % 4 = (v 0).code.val := by
  have := code_val_lt (v 0)
  rw [codeOf_succ]
  omega

theorem codeOf_div {n : ℕ} (v : Fin (n + 1) → F4) : codeOf v / 4 = codeOf (Fin.tail v) := by
  have := code_val_lt (v 0)
  rw [codeOf_succ]
  omega

theorem codeOf_zero : ∀ {n : ℕ}, codeOf (0 : Fin n → F4) = 0
  | 0 => rfl
  | n + 1 => by
    rw [codeOf_succ]
    have : (0 : Fin (n + 1) → F4) 0 = 0 := rfl
    rw [this]
    have h2 : Fin.tail (0 : Fin (n + 1) → F4) = 0 := rfl
    rw [h2, codeOf_zero]
    rfl

theorem mulD_eq (x y : F4) : mulD x.code.val y.code.val = (x * y).code.val := rfl

theorem xor_val_eq : ∀ a b : Fin 4, (a ^^^ b).val = a.val ^^^ b.val := by decide +kernel

theorem add_code_val (x y : F4) : (x + y).code.val = x.code.val ^^^ y.code.val := by
  have := xor_val_eq x.code y.code
  exact this

theorem codeOf_smul : ∀ {n : ℕ} (s : F4) (v : Fin n → F4),
    codeOf (s • v) = smulN n s.code.val (codeOf v)
  | 0, _, _ => rfl
  | n + 1, s, v => by
    rw [codeOf_succ, smulN, codeOf_mod, codeOf_div]
    have h1 : (s • v) 0 = s * v 0 := rfl
    have h2 : Fin.tail (s • v) = s • Fin.tail v := rfl
    rw [h1, h2, codeOf_smul s (Fin.tail v), mulD_eq]

theorem codeOf_add : ∀ {n : ℕ} (v w : Fin n → F4),
    codeOf (v + w) = addN n (codeOf v) (codeOf w)
  | 0, _, _ => rfl
  | n + 1, v, w => by
    rw [codeOf_succ, addN, codeOf_mod, codeOf_mod, codeOf_div, codeOf_div]
    have h1 : (v + w) 0 = v 0 + w 0 := rfl
    have h2 : Fin.tail (v + w) = Fin.tail v + Fin.tail w := rfl
    rw [h1, h2, codeOf_add (Fin.tail v) (Fin.tail w), add_code_val]

theorem digit_codeOf : ∀ {n : ℕ} (v : Fin n → F4) (j : Fin n),
    (codeOf v / 4 ^ j.val) % 4 = (v j).code.val
  | 0, _, j => j.elim0
  | n + 1, v, j => by
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Fin.val_zero, pow_zero, Nat.div_one]
      exact codeOf_mod v
    · simp only [Fin.val_succ, pow_succ']
      rw [← Nat.div_div_eq_div_mul, codeOf_div]
      exact digit_codeOf (Fin.tail v) j'


theorem mulVec_eq_sum_col {n : ℕ} (A : Matrix (Fin n) (Fin n) F4) (v : Fin n → F4) :
    A *ᵥ v = ∑ j : Fin n, v j • (fun i => A i j) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

@[expose] def colTerm {n : ℕ} (A : Matrix (Fin n) (Fin n) F4) (v : Fin n → F4) (j : ℕ) :
    Fin n → F4 :=
  if h : j < n then v ⟨j, h⟩ • (fun i => A i ⟨j, h⟩) else 0

theorem foldl_colsOf {n : ℕ} (A : Matrix (Fin n) (Fin n) F4) (v : Fin n → F4) :
    ∀ m, m ≤ n →
      (List.range m).foldl (fun acc j =>
        addN n acc (smulN n ((codeOf v / 4 ^ j) % 4) ((colsOf A).getD j 0))) 0 =
        codeOf (∑ j ∈ Finset.range m, colTerm A v j)
  | 0, _ => by simp [codeOf_zero]
  | m + 1, hm => by
    have hm' : m < n := hm
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_colsOf A v m hm'.le, Finset.sum_range_succ, codeOf_add]
    congr 1
    simp only [colTerm, hm', ↓reduceDIte]
    rw [codeOf_smul, digit_codeOf v ⟨m, hm'⟩]
    congr 1
    simp [colsOf, List.getD_eq_getElem?_getD, hm']

theorem codeOf_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) F4) (v : Fin n → F4) :
    codeOf (A *ᵥ v) = applyP n (colsOf A) (codeOf v) := by
  unfold applyP
  rw [foldl_colsOf A v n le_rfl, mulVec_eq_sum_col, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [colTerm, j.2]

theorem code_val_eq_zero_iff (x : F4) : x.code.val = 0 ↔ x = 0 := by
  rcases x with ⟨c⟩
  constructor
  · intro h
    have : c = 0 := Fin.ext h
    subst this
    rfl
  · intro h
    have : c = 0 := congrArg F4.code h
    subst this
    rfl

theorem norm_eq_ite (x : F4) : x ^ 2 * x = if x = 0 then 0 else 1 := by
  split_ifs with h
  · subst h
    decide +kernel
  · exact norm_one4 x h

theorem hermF_self : ∀ {n : ℕ} (v : Fin n → F4), hermF v v = ((nzCnt n (codeOf v) : ℕ) : F4)
  | 0, v => by simp [hermF, nzCnt]
  | n + 1, v => by
    have h := hermF_self (Fin.tail v)
    unfold hermF at h ⊢
    rw [Fin.sum_univ_succ, nzCnt, codeOf_mod, codeOf_div, Nat.cast_add, ← h, norm_eq_ite]
    congr 1
    by_cases hv : v 0 = 0
    · have h0 : (0 : F4).code.val = 0 := rfl
      simp [hv, h0]
    · have : ¬ (v 0).code.val = 0 := fun h0 => hv ((code_val_eq_zero_iff _).1 h0)
      simp [hv, this]

theorem cast_eq_zero_iff_even (k : ℕ) : (k : F4) = 0 ↔ k % 2 = 0 := by
  rw [CharP.cast_eq_zero_iff F4 2 k]
  omega


@[expose] def CompleteAt (n mask c : ℕ) : Prop :=
  c ≠ 0 → nzCnt n c % 2 = 0 →
    mask.testBit c = true ∨ mask.testBit (smulN n 2 c) = true ∨
      mask.testBit (smulN n 3 c) = true

@[expose] def CompleteMaskP (n mask : ℕ) : Prop :=
  ∀ a < 2 ^ n, ∀ b < 2 ^ n, CompleteAt n mask (a * 2 ^ n + b)

instance (n mask c : ℕ) : Decidable (CompleteAt n mask c) := by
  unfold CompleteAt
  infer_instance

instance (n mask : ℕ) : Decidable (CompleteMaskP n mask) := by
  unfold CompleteMaskP
  infer_instance

theorem CompleteMaskP.of_lt {n mask : ℕ} (h : CompleteMaskP n mask) {c : ℕ} (hc : c < 4 ^ n) :
    CompleteAt n mask c := by
  have h2 : 4 ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  have ha : c / 2 ^ n < 2 ^ n := Nat.div_lt_of_lt_mul (by rw [← h2]; exact hc)
  have hb : c % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have := h _ ha _ hb
  rwa [Nat.div_add_mod'] at this

variable {n : ℕ}

theorem inM_of_bfsP (M : Subgroup (SUid conj4 n)) (mats : List (Matrix (Fin n) (Fin n) F4))
    (hmats : ∀ A ∈ mats, IsSU A ∧ suOf A ∈ M) {start : Fin n → F4} (hstart : InM M start)
    (steps : List (ℕ × ℕ)) {mask : ℕ}
    (hmask : bfsAux (fun g c => applyP n (colsOf (mats.getD g 1)) c) steps
      (1 <<< codeOf start) = some mask) :
    ∀ c, mask.testBit c = true → ∃ v, codeOf v = c ∧ InM M v := by
  refine bfsAux_sound (R := fun c => ∃ v, codeOf v = c ∧ InM M v) _ ?_ steps _ mask ?_ hmask
  · rintro g c ⟨v, rfl, hv⟩
    have hA : IsSU (mats.getD g 1) ∧ suOf (mats.getD g 1) ∈ M := by
      by_cases hg : g < mats.length
      · exact hmats _ (by
          rw [List.getD_eq_getElem _ _ hg]
          exact List.getElem_mem hg)
      · rw [List.getD_eq_default _ _ (not_lt.1 hg)]
        exact ⟨isSU_one, by rw [suOf_one]; exact M.one_mem⟩
    refine ⟨mats.getD g 1 *ᵥ v, codeOf_mulVec _ _, ?_⟩
    have := hv.smul hA.2
    rwa [suOf_smul hA.1] at this
  · intro c hc
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hc
    have : codeOf start = c := by simpa using hc
    exact ⟨start, this, hstart⟩

theorem inM_of_completeP {M : Subgroup (SUid conj4 n)} {mask : ℕ}
    (hM : ∀ c, mask.testBit c = true → ∃ v, codeOf v = c ∧ InM M v)
    (hc : CompleteMaskP n mask) :
    ∀ a : Fin n → F4, a ≠ 0 → herm conj4 a a = 0 → InM M a := by
  intro a ha0 ha
  have hne : codeOf a ≠ 0 := by
    intro h
    apply ha0
    rw [← vecOf_codeOf a, h, ← codeOf_zero (n := n), vecOf_codeOf]
  have hev : nzCnt n (codeOf a) % 2 = 0 := by
    rw [herm_conj4, hermF_self] at ha
    exact (cast_eq_zero_iff_even _).1 ha
  have key : ∀ b : Fin n → F4, mask.testBit (codeOf b) = true → InM M b := by
    intro b hb
    obtain ⟨v, hv, hMv⟩ := hM _ hb
    have : v = b := by rw [← vecOf_codeOf v, ← vecOf_codeOf b, hv]
    exact this ▸ hMv
  rcases hc.of_lt (codeOf_lt a) hne hev with h | h | h
  · exact key a h
  · have h2 := key ((⟨2⟩ : F4) • a) (by rw [codeOf_smul]; exact h)
    have := h2.scale (c := ⟨3⟩) (by decide +kernel)
    rwa [smul_smul, show (⟨3⟩ : F4) * ⟨2⟩ = 1 by decide +kernel, one_smul] at this
  · have h2 := key ((⟨3⟩ : F4) • a) (by rw [codeOf_smul]; exact h)
    have := h2.scale (c := ⟨2⟩) (by decide +kernel)
    rwa [smul_smul, show (⟨2⟩ : F4) * ⟨3⟩ = 1 by decide +kernel, one_smul] at this

theorem eq_top_of_bfsP (hn : 2 ≤ n) (hn3 : n ≠ 3) (M : Subgroup (SUid conj4 n))
    (mats : List (Matrix (Fin n) (Fin n) F4)) (hmats : ∀ A ∈ mats, IsSU A ∧ suOf A ∈ M)
    {start : Fin n → F4} (hstart : InM M start) (steps : List (ℕ × ℕ)) {mask : ℕ}
    (hmask : bfsAux (fun g c => applyP n (colsOf (mats.getD g 1)) c) steps
      (1 <<< codeOf start) = some mask) (hc : CompleteMaskP n mask) : M = ⊤ := by
  have hT := T_le_of_inM M (inM_of_completeP (inM_of_bfsP M mats hmats hstart steps hmask) hc)
  rw [eq_top_iff]
  intro g _
  apply hT
  rw [T_eq_top isUnitaryInvolution_conj4 hn (fun h => absurd h hn3)]
  exact Subgroup.mem_top g

end CFSG.AGLEmbedding
