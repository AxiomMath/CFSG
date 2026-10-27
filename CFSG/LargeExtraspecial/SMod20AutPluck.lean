module

public import Certificates.Certificate21104
import all CFSG.Fischer.F4
public import CFSG.Fischer.Unitary
public import CFSG.Fischer.UnitaryCode

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix

theorem sub_eq_add_F4 (x y : F4) : x - y = x + y := by
  revert x y
  decide

theorem code_vecOfCode (c : ℕ) (i : Fin 6) : (vecOfCode c i).code.val = coord c i.val := rfl

theorem hermC_vecOfCode (c d : ℕ) :
    hermC c d = (hermStd (vecOfCode c) (vecOfCode d)).code.val := by
  unfold hermC hermStd
  rw [foldl_xor_six, code_sum_six]
  simp only [pow_two, code_mul]
  rfl

theorem det3_code (A : Matrix (Fin 3) (Fin 3) F4) :
    det3 (A 0 0).code.val (A 0 1).code.val (A 0 2).code.val (A 1 0).code.val (A 1 1).code.val
      (A 1 2).code.val (A 2 0).code.val (A 2 1).code.val (A 2 2).code.val = A.det.code.val := by
  have e : A.det = A 0 0 * (A 1 1 * A 2 2 + A 1 2 * A 2 1) +
      A 0 1 * (A 1 0 * A 2 2 + A 1 2 * A 2 0) + A 0 2 * (A 1 0 * A 2 1 + A 1 1 * A 2 0) := by
    rw [det_fin_three]
    simp only [sub_eq_add_F4]
    ring
  rw [e]
  simp only [code_add, code_mul]
  rfl

@[expose] def tripleVec (T : ℕ × ℕ × ℕ) : Fin 3 → W :=
  ![vecOfCode T.1, vecOfCode T.2.1, vecOfCode T.2.2]

@[expose] def triTab : Fin 20 → Fin 3 → Fin 6 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 1, 4], ![0, 1, 5], ![0, 2, 3], ![0, 2, 4], ![0, 2, 5],
    ![0, 3, 4], ![0, 3, 5], ![0, 4, 5], ![1, 2, 3], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4],
    ![1, 3, 5], ![1, 4, 5], ![2, 3, 4], ![2, 3, 5], ![2, 4, 5], ![3, 4, 5]]

theorem tri_get (t : Fin 20) :
    tri[t.val]! = ((triTab t 0).val, (triTab t 1).val, (triTab t 2).val) := by
  revert t
  decide

@[expose] def pluckMat (v : Fin 3 → W) (t : Fin 20) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of fun a b => v b (triTab t a)

theorem pluck_eq (T : ℕ × ℕ × ℕ) (t : Fin 20) :
    pluck T t = (pluckMat (tripleVec T) t).det.code.val := by
  unfold pluck
  rw [tri_get t]
  rw [← det3_code]
  rfl

theorem pluckMat_mul (v : Fin 3 → W) (B : Matrix (Fin 3) (Fin 3) F4) (t : Fin 20) :
    pluckMat (fun b => ∑ a, B a b • v a) t = pluckMat v t * B := by
  ext a b
  simp only [pluckMat, Matrix.of_apply, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem mul_cube_cancel (a b c : F4) {d : F4} (hd : d ≠ 0) : a * d * (b * d) * (c * d) =
    a * b * c := by
  have h : ∀ x : F4, x ≠ 0 → x * x * x = 1 := by decide
  calc a * d * (b * d) * (c * d) = a * b * c * (d * d * d) := by ring
    _ = a * b * c := by rw [h d hd, mul_one]

theorem code_ne_zero_iff (x : F4) : x.code.val ≠ 0 ↔ x ≠ 0 := not_congr (code_eq_zero_iff x)

theorem find_lt (T : ℕ × ℕ × ℕ) :
    ((List.range 20).find? fun t => pluck T t != 0).getD 0 < 20 := by
  cases h : (List.range 20).find? fun t => pluck T t != 0 with
  | none => simp
  | some t =>
    have := List.mem_of_find?_eq_some h
    simpa using this

theorem wedgeCode_eq_of_mul (T T' : ℕ × ℕ × ℕ) (B : Matrix (Fin 3) (Fin 3) F4)
    (hT : tripleVec T' = fun b => ∑ a, B a b • tripleVec T a) (hB : B.det ≠ 0) :
    wedgeCode T' = wedgeCode T := by
  have hP : ∀ t : Fin 20, pluck T' t = ((pluckMat (tripleVec T) t).det * B.det).code.val := by
    intro t
    rw [pluck_eq, hT, pluckMat_mul, det_mul]
  have hfind : ((List.range 20).find? fun t => pluck T' t != 0) =
      ((List.range 20).find? fun t => pluck T t != 0) := by
    apply List.find?_congr
    intro t ht
    have ht' : t < 20 := List.mem_range.1 ht
    have h1 : pluck T' t = ((pluckMat (tripleVec T) ⟨t, ht'⟩).det * B.det).code.val :=
      hP ⟨t, ht'⟩
    have h2 : pluck T t = (pluckMat (tripleVec T) ⟨t, ht'⟩).det.code.val := pluck_eq T ⟨t, ht'⟩
    rw [h1, h2, Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, code_ne_zero_iff, code_ne_zero_iff]
    exact ⟨fun h => left_ne_zero_of_mul h, fun h => mul_ne_zero h hB⟩
  have hlt := find_lt T
  set t₀ := ((List.range 20).find? fun t => pluck T t != 0).getD 0 with ht₀
  have hscal : wedgeScalar T' = (((pluckMat (tripleVec T) ⟨19 - t₀, by omega⟩).det * B.det) *
      ((pluckMat (tripleVec T) ⟨t₀, hlt⟩).det * B.det)).code.val := by
    unfold wedgeScalar
    rw [hfind, ← ht₀]
    show f4mul (pluck T' (19 - t₀)) (pluck T' t₀) = _
    have h1 : pluck T' (19 - t₀) =
        ((pluckMat (tripleVec T) ⟨19 - t₀, by omega⟩).det * B.det).code.val :=
      hP ⟨19 - t₀, by omega⟩
    have h2 : pluck T' t₀ = ((pluckMat (tripleVec T) ⟨t₀, hlt⟩).det * B.det).code.val :=
      hP ⟨t₀, hlt⟩
    rw [h1, h2, ← code_mul]
  have hscal0 : wedgeScalar T = ((pluckMat (tripleVec T) ⟨19 - t₀, by omega⟩).det *
      (pluckMat (tripleVec T) ⟨t₀, hlt⟩).det).code.val := by
    unfold wedgeScalar
    rw [← ht₀]
    show f4mul (pluck T (19 - t₀)) (pluck T t₀) = _
    have h1 : pluck T (19 - t₀) = (pluckMat (tripleVec T) ⟨19 - t₀, by omega⟩).det.code.val :=
      pluck_eq T ⟨19 - t₀, by omega⟩
    have h2 : pluck T t₀ = (pluckMat (tripleVec T) ⟨t₀, hlt⟩).det.code.val := pluck_eq T ⟨t₀, hlt⟩
    rw [h1, h2, ← code_mul]
  unfold wedgeCode
  apply List.foldl_ext
  intro acc k hk
  have hk' : k < 20 := by have := List.mem_range.1 hk; omega
  have h1 : pluck T' k = ((pluckMat (tripleVec T) ⟨k, hk'⟩).det * B.det).code.val := hP ⟨k, hk'⟩
  have h2 : pluck T k = (pluckMat (tripleVec T) ⟨k, hk'⟩).det.code.val := pluck_eq T ⟨k, hk'⟩
  rw [hscal, hscal0, h1, h2, ← code_mul, ← code_mul, mul_cube_cancel _ _ _ hB]

@[expose] def planeVec (i : ℕ) : Fin 3 → W := tripleVec (wB i)

theorem chkW_parts :
    (∀ j < 891, wtIdx[wtArr[j]!]! = j) ∧ ∀ j < 891, modelOK j = true := by
  have h := Certificates.certificate21104
  unfold chkW at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem wtArr_get_eq {j : ℕ} (hj : j < 891) : wtArr[j]! = wt j := by
  unfold wtArr
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem wt_injective {i j : ℕ} (hi : i < 891) (hj : j < 891)
    (h : wt i = wt j) : i = j := by
  have hi' := chkW_parts.1 i hi
  have hj' := chkW_parts.1 j hj
  rw [wtArr_get_eq hi] at hi'
  rw [wtArr_get_eq hj, ← h] at hj'
  rw [← hi', hj']

theorem modelOK_parts {j : ℕ} (h : modelOK j = true) :
    hermC (wB j).1 (wB j).1 = 0 ∧ hermC (wB j).2.1 (wB j).2.1 = 0 ∧
      hermC (wB j).2.2 (wB j).2.2 = 0 ∧ hermC (wB j).1 (wB j).2.1 = 0 ∧
      hermC (wB j).1 (wB j).2.2 = 0 ∧ hermC (wB j).2.1 (wB j).2.2 = 0 ∧
      wedgeScalar (wB j) ≠ 0 := by
  unfold modelOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.2⟩

theorem exists_pluckMat_det_ne_zero (T : ℕ × ℕ × ℕ) (h : wedgeScalar T ≠ 0) :
    ∃ t : Fin 20, (pluckMat (tripleVec T) t).det ≠ 0 := by
  have hlt := find_lt T
  refine ⟨⟨_, hlt⟩, fun h0 => h ?_⟩
  unfold wedgeScalar
  show f4mul (pluck T (19 - ((List.range 20).find? fun t => pluck T t != 0).getD 0))
    (pluck T (((List.range 20).find? fun t => pluck T t != 0).getD 0)) = 0
  have h2 : pluck T (((List.range 20).find? fun t => pluck T t != 0).getD 0) =
      (pluckMat (tripleVec T) ⟨_, hlt⟩).det.code.val := pluck_eq T ⟨_, hlt⟩
  rw [h2, h0, code_zero]
  simp [f4mul]

theorem eq_of_span_eq {i j : ℕ} (hi : i < 891) (hj : j < 891)
    (h : Submodule.span F4 (Set.range (planeVec i)) =
      Submodule.span F4 (Set.range (planeVec j))) : i = j := by
  have hmem : ∀ b : Fin 3, ∃ c : Fin 3 → F4, ∑ a, c a • planeVec i a = planeVec j b := by
    intro b
    have : planeVec j b ∈ Submodule.span F4 (Set.range (planeVec i)) := by
      rw [h]
      exact Submodule.subset_span ⟨b, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun F4).1 this
  choose c hc using hmem
  set B : Matrix (Fin 3) (Fin 3) F4 := Matrix.of fun a b => c b a with hBdef
  have hT : tripleVec (wB j) = fun b => ∑ a, B a b • tripleVec (wB i) a := by
    funext b
    exact (hc b).symm
  have hB : B.det ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ :=
      exists_pluckMat_det_ne_zero (wB j) (modelOK_parts (chkW_parts.2 j hj)).2.2.2.2.2.2
    apply ht
    rw [hT, pluckMat_mul, det_mul, h0, mul_zero]
  have hw := wedgeCode_eq_of_mul (wB i) (wB j) B hT hB
  exact wt_injective hi hj hw.symm

end CFSG.LargeExtraspecial.SMod20.Aut
