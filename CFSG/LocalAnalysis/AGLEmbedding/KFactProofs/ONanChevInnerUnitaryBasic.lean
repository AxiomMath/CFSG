module

public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.AGLEmbedding

open CFSG.Fischer CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary Matrix

noncomputable abbrev conj4 : F4 ≃+* F4 := unitaryInvolution F4 2 1

theorem card_F4 : Nat.card F4 = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, F4.card]
  norm_num

theorem conj4_apply (x : F4) : conj4 x = x ^ 2 := by
  rw [unitaryInvolution_apply]
  norm_num

theorem isUnitaryInvolution_conj4 : IsUnitaryInvolution conj4 :=
  isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) card_F4

@[expose] def hermF {n : ℕ} (x y : Fin n → F4) : F4 := ∑ i, x i ^ 2 * y i

theorem herm_conj4 {n : ℕ} (x y : Fin n → F4) : herm conj4 x y = hermF x y := by
  simp only [herm, hermF, conj4_apply]

@[expose] def conjTrF {n : ℕ} (M : Matrix (Fin n) (Fin n) F4) : Matrix (Fin n) (Fin n) F4 :=
  Matrix.of fun i j => M j i ^ 2

theorem conjTr_conj4 {n : ℕ} (M : Matrix (Fin n) (Fin n) F4) : conjTr conj4 M = conjTrF M := by
  ext i j
  simp only [conjTr, conjTrF, Matrix.transpose_apply, Matrix.map_apply, conj4_apply,
    Matrix.of_apply]

@[expose] def vecOf : (n : ℕ) → ℕ → (Fin n → F4)
  | 0, _ => fun i => i.elim0
  | n + 1, c => Fin.cons (⟨⟨c % 4, Nat.mod_lt _ (by norm_num)⟩⟩ : F4) (vecOf n (c / 4))

@[expose] def codeOf : {n : ℕ} → (Fin n → F4) → ℕ
  | 0, _ => 0
  | _ + 1, v => (v 0).code.val + 4 * codeOf (Fin.tail v)

theorem vecOf_codeOf : ∀ {n : ℕ} (v : Fin n → F4), vecOf n (codeOf v) = v
  | 0, v => funext fun i => i.elim0
  | n + 1, v => by
    have h4 : (v 0).code.val < 4 := (v 0).code.2
    have h1 : (codeOf v) % 4 = (v 0).code.val := by
      simp only [codeOf]
      omega
    have h2 : (codeOf v) / 4 = codeOf (Fin.tail v) := by
      simp only [codeOf]
      omega
    simp only [vecOf]
    rw [h2, vecOf_codeOf (Fin.tail v)]
    have h3 : (⟨⟨codeOf v % 4, Nat.mod_lt _ (by norm_num)⟩⟩ : F4) = v 0 := by
      cases hv : v 0
      simp only [hv] at h1
      congr
    rw [h3]
    exact Fin.cons_self_tail v

theorem codeOf_lt : ∀ {n : ℕ} (v : Fin n → F4), codeOf v < 4 ^ n
  | 0, v => by simp [codeOf]
  | n + 1, v => by
    have h4 : (v 0).code.val < 4 := (v 0).code.2
    have := codeOf_lt (Fin.tail v)
    simp only [codeOf, pow_succ]
    omega

variable {n : ℕ}

@[expose] def IsSU (M : Matrix (Fin n) (Fin n) F4) : Prop := M.det = 1 ∧ conjTrF M * M = 1

instance (M : Matrix (Fin n) (Fin n) F4) : Decidable (IsSU M) := by
  unfold IsSU
  infer_instance

@[expose] noncomputable def suMk (M : Matrix (Fin n) (Fin n) F4) (h : IsSU M) : SUid conj4 n :=
  mkSU conj4 M h.1 (fun x y => by
    rw [herm_mulVec, conjTr_conj4, h.2, Matrix.one_mulVec])

@[expose] noncomputable def suOf (M : Matrix (Fin n) (Fin n) F4) : SUid conj4 n :=
  open scoped Classical in if h : IsSU M then suMk M h else 1

theorem suOf_smul {M : Matrix (Fin n) (Fin n) F4} (h : IsSU M) (v : Fin n → F4) :
    suOf M • v = M *ᵥ v := by
  classical
  simp only [suOf, h, dite_true]
  rfl

theorem isSU_one : IsSU (1 : Matrix (Fin n) (Fin n) F4) := by
  refine ⟨Matrix.det_one, ?_⟩
  ext i j
  simp [conjTrF, Matrix.one_apply, eq_comm]

theorem suOf_one : suOf (1 : Matrix (Fin n) (Fin n) F4) = 1 := by
  apply ext_smul
  intro v
  rw [suOf_smul isSU_one, one_smul, Matrix.one_mulVec]

@[expose] def InM (M : Subgroup (SUid conj4 n)) (a : Fin n → F4) : Prop :=
  ∃ t ∈ M, ∀ v, t • v = v + (1 * herm conj4 a v) • a

theorem InM.smul {M : Subgroup (SUid conj4 n)} {a : Fin n → F4} (h : InM M a)
    {g : SUid conj4 n} (hg : g ∈ M) : InM M (g • a) := by
  obtain ⟨t, ht, hta⟩ := h
  exact ⟨g * t * g⁻¹, M.mul_mem (M.mul_mem hg ht) (M.inv_mem hg), conj_smul_of_tv g t hta⟩

theorem norm_one4 : ∀ c : F4, c ≠ 0 → c ^ 2 * c = 1 := by decide +kernel

theorem InM.scale {M : Subgroup (SUid conj4 n)} {a : Fin n → F4} (h : InM M a) {c : F4}
    (hc : c ≠ 0) : InM M (c • a) := by
  obtain ⟨t, ht, hta⟩ := h
  refine ⟨t, ht, fun v => ?_⟩
  have hcc : conj4 c * c = 1 := by
    rw [conj4_apply]
    exact norm_one4 c hc
  have hs : (1 * (conj4 c * herm conj4 a v)) * c = 1 * herm conj4 a v := by
    linear_combination (herm conj4 a v) * hcc
  rw [hta, herm_smul_left, smul_smul, hs]

theorem T_le_of_inM (M : Subgroup (SUid conj4 n))
    (h : ∀ a : Fin n → F4, a ≠ 0 → herm conj4 a a = 0 → InM M a) : T conj4 n ≤ M := by
  rw [T, Subgroup.closure_le]
  rintro g ⟨a, c, ha, hc, hg⟩
  by_cases hc0 : c = 0
  · have : g = 1 := ext_smul conj4 fun v => by
      rw [hg, hc0, zero_mul, zero_smul, add_zero, one_smul]
    rw [this]
    exact M.one_mem
  by_cases ha0 : a = 0
  · have : g = 1 := ext_smul conj4 fun v => by
      rw [hg, ha0, smul_zero, add_zero, one_smul]
    rw [this]
    exact M.one_mem
  have hc1 : c = 1 := by
    have key : ∀ c : F4, c + c ^ 2 = 0 → c ≠ 0 → c = 1 := by decide +kernel
    exact key c (by rw [← conj4_apply]; exact hc) hc0
  obtain ⟨t, ht, hta⟩ := h a ha0 ha
  have : g = t := ext_smul conj4 fun v => by rw [hg, hta, hc1]
  rw [this]
  exact ht

end CFSG.AGLEmbedding
