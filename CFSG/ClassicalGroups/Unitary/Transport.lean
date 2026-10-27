module

public import CFSG.ClassicalGroups.Unitary.Elements

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem transport (hσ : ∀ c, σ (σ c) = c) {m n : ℕ} (φ : (Fin m → K) →ₗ[K] (Fin n → K))
    (hφ : ∀ u v, herm σ (φ u) (φ v) = herm σ u v) {g : SUid σ m} (hg : g ∈ T σ m) :
    ∃ g' ∈ T σ n, (∀ u, g' • φ u = φ (g • u)) ∧
      ∀ v, (∀ u, herm σ (φ u) v = 0) → g' • v = v := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, c, ha, hc, h⟩ := hg
    obtain ⟨g', hg', h'⟩ := exists_mem_T_tv hσ (a := φ a) (by rw [hφ, ha]) hc
    refine ⟨g', hg', fun u => ?_, fun v hv => ?_⟩
    · rw [h', h, map_add, map_smul, hφ]
    · rw [h', hv, mul_zero, zero_smul, add_zero]
  | one => exact ⟨1, (T σ n).one_mem, fun u => by simp, fun v _ => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨g', hg', h1, h2⟩ := ihg
    obtain ⟨h', hh', h3, h4⟩ := ihh
    refine ⟨g' * h', (T σ n).mul_mem hg' hh', fun u => ?_, fun v hv => ?_⟩
    · rw [mul_smul, h3, h1, mul_smul]
    · rw [mul_smul, h4 v hv, h2 v hv]
  | inv g _ ihg =>
    obtain ⟨g', hg', h1, h2⟩ := ihg
    refine ⟨g'⁻¹, (T σ n).inv_mem hg', fun u => ?_, fun v hv => ?_⟩
    · rw [inv_smul_eq_iff, h1, smul_inv_smul]
    · rw [inv_smul_eq_iff, h2 v hv]

variable {n : ℕ}

variable (K n) in
abbrev e0 : Fin (n + 1) → K := Pi.single 0 1

variable (n) in
@[expose] def consL : (Fin n → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun u := Fin.cons 0 u
  map_add' u v := by
    funext i
    cases i using Fin.cases <;> simp
  map_smul' c u := by
    funext i
    cases i using Fin.cases <;> simp

@[simp] theorem consL_apply (u : Fin n → K) : consL n u = (Fin.cons 0 u : Fin (n + 1) → K) :=
  rfl

theorem herm_consL (u v : Fin n → K) : herm σ (consL n u) (consL n v) = herm σ u v := by
  rw [consL_apply, consL_apply, herm_cons, map_zero, zero_mul, zero_add]

theorem herm_single_zero (w : Fin (n + 1) → K) : herm σ (e0 K n) w = w 0 := by
  rw [herm_single_left, map_one, one_mul]

theorem herm_consL_single_zero (u : Fin n → K) :
    herm σ (consL n u) (e0 K n) = 0 := by
  rw [herm_single_right, consL_apply, Fin.cons_zero, map_zero, zero_mul]

theorem eq_smul_single_add_consL (v : Fin (n + 1) → K) :
    v = v 0 • e0 K n + consL n (Fin.tail v) := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.tail]

@[expose] def blkMat (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Matrix (Fin n) (Fin n) K :=
  M.submatrix Fin.succ Fin.succ

theorem smul_consL_of_fix {M : SUid σ (n + 1)} (hM : M • (e0 K n) = e0 K n) (u : Fin n → K) :
    M • consL n u =
      consL n (blkMat ((M : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ u) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    have h := herm_smul_smul σ M (e0 K n) (consL n u)
    rw [hM, herm_single_zero, herm_single_zero] at h
    rw [h]
    simp only [consL_apply, Fin.cons_zero]
  | succ j =>
    simp only [consL_apply, Fin.cons_succ, smul_def]
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, mul_zero, zero_add,
      Fin.cons_succ, blkMat, submatrix_apply]

theorem blkMat_det {M : SUid σ (n + 1)}
    (hM : M • (e0 K n) = e0 K n) :
    (blkMat ((M : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)).det = 1 := by
  set A := ((M : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) with hA
  have hcol : ∀ i, A i 0 = (e0 K n) i := by
    intro i
    have := congrFun hM i
    rw [smul_def, ← hA, mulVec_single_one] at this
    simpa using this
  have hdet : A.det = 1 := ((mem_SUid_iff σ).mp M.2).1
  rw [det_succ_column_zero, Fin.sum_univ_succ] at hdet
  simp only [hcol, e0, Fin.val_zero, pow_zero, Pi.single_eq_same, mul_one, one_mul,
    Fin.succAbove_zero, Fin.val_succ] at hdet
  rw [Finset.sum_eq_zero (fun j _ => by simp), add_zero] at hdet
  exact hdet

@[expose] noncomputable def blk (M : SUid σ (n + 1))
    (hM : M • (e0 K n) = e0 K n) : SUid σ n :=
  mkSU σ (blkMat ((M : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K))
    (blkMat_det hM) (fun x y => by
      rw [← herm_consL (σ := σ), ← herm_consL (σ := σ) x y, ← smul_consL_of_fix hM,
        ← smul_consL_of_fix hM, herm_smul_smul])

theorem smul_consL_eq_consL_blk {M : SUid σ (n + 1)}
    (hM : M • (e0 K n) = e0 K n) (u : Fin n → K) :
    M • consL n u = consL n (blk M hM • u) :=
  smul_consL_of_fix hM u

theorem mem_T_of_blk_mem_T (hσ : ∀ c, σ (σ c) = c) {M : SUid σ (n + 1)}
    (hM : M • (e0 K n) = e0 K n) (h : blk M hM ∈ T σ n) :
    M ∈ T σ (n + 1) := by
  obtain ⟨g', hg', h1, h2⟩ := transport hσ (consL n) (fun u v => herm_consL u v) h
  have he : g' • (e0 K n) = e0 K n :=
    h2 _ fun u => herm_consL_single_zero u
  have : g' = M := by
    apply ext_smul
    intro v
    rw [eq_smul_single_add_consL v, smul_add, smul_add, smul_comm, he, smul_comm, hM, h1,
      smul_consL_eq_consL_blk hM]
  rw [← this]
  exact hg'

end CFSG.ClassicalGroups.Unitary
