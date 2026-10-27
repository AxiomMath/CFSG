module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open Matrix CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K]

section Elementary

private def N (a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  (a : Matrix (Fin 4) (Fin 4) K) - 1

private lemma N_apply (a : GL (Fin 4) K) (i j : Fin 4) :
    N a i j = (a : Matrix (Fin 4) (Fin 4) K) i j - (if i = j then 1 else 0) := by
  simp [N, Matrix.sub_apply, Matrix.one_apply]

private lemma N_apply_of_ne {a : GL (Fin 4) K} {i j : Fin 4} (h : i ≠ j) :
    N a i j = (a : Matrix (Fin 4) (Fin 4) K) i j := by
  rw [N_apply, if_neg h, sub_zero]

private lemma N_diag (a : GL (Fin 4) K) (i : Fin 4) :
    N a i i = (a : Matrix (Fin 4) (Fin 4) K) i i - 1 := by
  rw [N_apply, if_pos rfl]

private lemma N_eq_zero_of_le {a : GL (Fin 4) K}
    (hU : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular)
    (hd : ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    {i j : Fin 4} (hij : j ≤ i) : N a i j = 0 := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · rw [N_apply_of_ne (ne_of_gt hlt), hU hlt]
  · rw [N_diag, hd, sub_self]

private lemma N_one : N (1 : GL (Fin 4) K) = 0 := by
  ext i j
  simp [N]

private lemma eq_one_add_N (a : GL (Fin 4) K) :
    (a : Matrix (Fin 4) (Fin 4) K) = 1 + N a := by
  rw [N]
  abel

variable [CharP K 2]

private lemma N_add_self (a : GL (Fin 4) K) : N a + N a = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

private lemma val_sq (a : GL (Fin 4) K) :
    ((a * a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 + N a * N a := by
  rw [Units.val_mul, eq_one_add_N]
  calc (1 + N a) * (1 + N a) = 1 + (N a + N a) + N a * N a := by noncomm_ring
  _ = 1 + N a * N a := by rw [N_add_self, add_zero]

private lemma N_mul_self {a : GL (Fin 4) K} (hsq : a * a = 1) : N a * N a = 0 := by
  have h : ((a * a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [hsq]
    rfl
  rw [val_sq] at h
  exact add_left_cancel (by simpa using h : (1 : Matrix (Fin 4) (Fin 4) K) + N a * N a = 1 + 0)

omit [CharP K 2] in
private lemma N_mul_eq (a b : GL (Fin 4) K) :
    N (a * b) = N a + N b + N a * N b := by
  rw [N, Units.val_mul, eq_one_add_N a, eq_one_add_N b]
  noncomm_ring

omit [CharP K 2] in
private lemma comm_N {a b : GL (Fin 4) K} (h : a * b = b * a) :
    N a * N b = N b * N a := by
  have h' : (1 + N a) * (1 + N b) = (1 + N b) * (1 + N a) := by
    rw [← eq_one_add_N a, ← eq_one_add_N b, ← Units.val_mul, ← Units.val_mul, h]
  have e1 : (1 + N a) * (1 + N b) = (1 + (N a + N b)) + N a * N b := by noncomm_ring
  have e2 : (1 + N b) * (1 + N a) = (1 + (N a + N b)) + N b * N a := by
    noncomm_ring
  rw [e1, e2] at h'
  exact add_left_cancel h'

omit [CharP K 2] in
private lemma mul_entry_01 {X Y : Matrix (Fin 4) (Fin 4) K}
    (hX : ∀ i j, j ≤ i → X i j = 0) (hY : ∀ i j, j ≤ i → Y i j = 0) :
    (X * Y) 0 1 = 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  rw [hX 0 0 le_rfl, hY 1 1 le_rfl, hY 2 1 (by decide), hY 3 1 (by decide)]
  ring

omit [CharP K 2] in
private lemma mul_entry_02 {X Y : Matrix (Fin 4) (Fin 4) K}
    (hX : ∀ i j, j ≤ i → X i j = 0) (hY : ∀ i j, j ≤ i → Y i j = 0) :
    (X * Y) 0 2 = X 0 1 * Y 1 2 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  rw [hX 0 0 le_rfl, hY 2 2 le_rfl, hY 3 2 (by decide)]
  ring

omit [CharP K 2] in
private lemma mul_entry_03 {X Y : Matrix (Fin 4) (Fin 4) K}
    (hX : ∀ i j, j ≤ i → X i j = 0) (hY : ∀ i j, j ≤ i → Y i j = 0) :
    (X * Y) 0 3 = X 0 1 * Y 1 3 + X 0 2 * Y 2 3 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  rw [hX 0 0 le_rfl, hY 3 3 le_rfl]
  ring

omit [CharP K 2] in
private lemma mul_entry_13 {X Y : Matrix (Fin 4) (Fin 4) K}
    (hX : ∀ i j, j ≤ i → X i j = 0) (hY : ∀ i j, j ≤ i → Y i j = 0) :
    (X * Y) 1 3 = X 1 2 * Y 2 3 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  rw [hX 1 0 (by decide), hX 1 1 le_rfl, hY 3 3 le_rfl]
  ring

omit [CharP K 2] in
private lemma mul_entry_23 {X Y : Matrix (Fin 4) (Fin 4) K}
    (hX : ∀ i j, j ≤ i → X i j = 0) (hY : ∀ i j, j ≤ i → Y i j = 0) :
    (X * Y) 2 3 = 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  rw [hX 2 0 (by decide), hX 2 1 (by decide), hX 2 2 le_rfl, hY 3 3 le_rfl]
  ring

omit [CharP K 2] in
private lemma comm_entry_02 {a b : GL (Fin 4) K}
    (hNa : ∀ i j, j ≤ i → N a i j = 0) (hNb : ∀ i j, j ≤ i → N b i j = 0)
    (hNM : N a * N b = N b * N a) :
    N a 0 1 * N b 1 2 = N b 0 1 * N a 1 2 := by
  have h := congrArg (fun X : Matrix (Fin 4) (Fin 4) K => X 0 2) hNM
  rwa [mul_entry_02 hNa hNb, mul_entry_02 hNb hNa] at h

omit [CharP K 2] in
private lemma comm_entry_13 {a b : GL (Fin 4) K}
    (hNa : ∀ i j, j ≤ i → N a i j = 0) (hNb : ∀ i j, j ≤ i → N b i j = 0)
    (hNM : N a * N b = N b * N a) :
    N a 1 2 * N b 2 3 = N b 1 2 * N a 2 3 := by
  have h := congrArg (fun X : Matrix (Fin 4) (Fin 4) K => X 1 3) hNM
  rwa [mul_entry_13 hNa hNb, mul_entry_13 hNb hNa] at h

omit [CharP K 2] in
private lemma comm_entry_03 {a b : GL (Fin 4) K}
    (hNa : ∀ i j, j ≤ i → N a i j = 0) (hNb : ∀ i j, j ≤ i → N b i j = 0)
    (hNM : N a * N b = N b * N a) :
    N a 0 1 * N b 1 3 + N a 0 2 * N b 2 3 =
      N b 0 1 * N a 1 3 + N b 0 2 * N a 2 3 := by
  have h := congrArg (fun X : Matrix (Fin 4) (Fin 4) K => X 0 3) hNM
  rwa [mul_entry_03 hNa hNb, mul_entry_03 hNb hNa] at h

end Elementary

section Alternating

variable [CharP K 2]

private lemma alt_apply_comm {B : Matrix (Fin 4) (Fin 4) K} (hB : B ∈ altSubgroup 4 K)
    (i j : Fin 4) : B i j = B j i := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) hB.1
  rw [Matrix.transpose_apply, Matrix.neg_apply, CharTwo.neg_eq] at h
  exact h.symm

private def beta : LinearMap.BilinForm K (Fin 4 → K) :=
  LinearMap.mk₂ K (fun x y : Fin 4 → K => x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1)
    (by intro x y z; simp only [Pi.add_apply]; ring)
    (by intro c x y; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intro x y z; simp only [Pi.add_apply]; ring)
    (by intro c x y; simp only [Pi.smul_apply, smul_eq_mul]; ring)

omit [CharP K 2] in
private lemma beta_apply (x y : Fin 4 → K) :
    beta x y = x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1 := rfl

omit [CharP K 2] in
private lemma beta_nondegenerate :
    LinearMap.Nondegenerate (beta : LinearMap.BilinForm K (Fin 4 → K)) := by
  constructor
  · intro x hx
    funext i
    fin_cases i
    · simpa [beta_apply] using hx ![0, 0, 1, 0]
    · simpa [beta_apply] using hx ![0, 0, 0, 1]
    · simpa [beta_apply] using hx ![1, 0, 0, 0]
    · simpa [beta_apply] using hx ![0, 1, 0, 0]
  · intro y hy
    funext i
    fin_cases i
    · simpa [beta_apply] using hy ![0, 0, 1, 0]
    · simpa [beta_apply] using hy ![0, 0, 0, 1]
    · simpa [beta_apply] using hy ![1, 0, 0, 0]
    · simpa [beta_apply] using hy ![0, 1, 0, 0]

omit [CharP K 2] in
private lemma congr_entry_13 {a B : Matrix (Fin 4) (Fin 4) K}
    (ha : a.IsUpperTriangular) (hd : ∀ i, a i i = 1) (hBd : ∀ i, B i i = 0) :
    (a * B * aᵀ) 1 3 = B 1 3 + a 1 2 * B 2 3 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_four, Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  simp [ha (by decide : (0:Fin 4) < 1), ha (by decide : (0:Fin 4) < 3),
    ha (by decide : (1:Fin 4) < 3), ha (by decide : (2:Fin 4) < 3), hd, hBd]

omit [CharP K 2] in
private lemma congr_entry_03 {a B : Matrix (Fin 4) (Fin 4) K}
    (ha : a.IsUpperTriangular) (hd : ∀ i, a i i = 1) (hBd : ∀ i, B i i = 0) :
    (a * B * aᵀ) 0 3 = B 0 3 + a 0 1 * B 1 3 + a 0 2 * B 2 3 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_four, Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  simp [ha (by decide : (0:Fin 4) < 3), ha (by decide : (1:Fin 4) < 3),
    ha (by decide : (2:Fin 4) < 3), hd, hBd]

private lemma congr_entry_02 {a B : Matrix (Fin 4) (Fin 4) K}
    (ha : a.IsUpperTriangular) (hd : ∀ i, a i i = 1)
    (hB : B ∈ altSubgroup 4 K) (hBd : ∀ i, B i i = 0) :
    (a * B * aᵀ) 0 2 = B 0 2 + a 0 1 * B 1 2 + a 0 3 * B 2 3 +
      a 2 3 * (B 0 3 + a 0 1 * B 1 3 + a 0 2 * B 2 3) := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_four, Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  simp [ha (by decide : (0:Fin 4) < 2), ha (by decide : (1:Fin 4) < 2),
    hd, hBd, alt_apply_comm hB 3 2]
  ring

private lemma congr_entry_12 {a B : Matrix (Fin 4) (Fin 4) K}
    (ha : a.IsUpperTriangular) (hd : ∀ i, a i i = 1)
    (hB : B ∈ altSubgroup 4 K) (hBd : ∀ i, B i i = 0) (h12 : a 1 2 = 0) :
    (a * B * aᵀ) 1 2 = B 1 2 + a 1 3 * B 2 3 + a 2 3 * B 1 3 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_four, Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  simp [ha (by decide : (0:Fin 4) < 1), ha (by decide : (0:Fin 4) < 2),
    ha (by decide : (1:Fin 4) < 2), hd, hBd, alt_apply_comm hB 3 2, h12]
  ring

private lemma congr_entry_01_case1 {a B : Matrix (Fin 4) (Fin 4) K}
    (ha : a.IsUpperTriangular) (hd : ∀ i, a i i = 1)
    (hB : B ∈ altSubgroup 4 K) (hBd : ∀ i, B i i = 0)
    (h01 : a 0 1 = 0) (h23 : B 2 3 = 0) :
    (a * B * aᵀ) 0 1 = B 0 1 + a 1 2 * B 0 2 + a 1 3 * B 0 3 +
      a 0 2 * B 1 2 + a 0 3 * B 1 3 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_four, Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  simp [ha (by decide : (0:Fin 4) < 1), hd, hBd, alt_apply_comm hB 2 1,
    alt_apply_comm hB 3 1, alt_apply_comm hB 3 2, h01, h23]
  ring

private lemma congr_entry_01_case2 {a B : Matrix (Fin 4) (Fin 4) K}
    (ha : a.IsUpperTriangular) (hd : ∀ i, a i i = 1)
    (hB : B ∈ altSubgroup 4 K) (hBd : ∀ i, B i i = 0) (h12 : a 1 2 = 0) :
    (a * B * aᵀ) 0 1 = B 0 1 + a 0 2 * B 1 2 + a 0 3 * B 1 3 + a 1 3 * B 0 3 +
      a 1 3 * (a 0 1 * B 1 3 + a 0 2 * B 2 3) := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_four, Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  simp [ha (by decide : (0:Fin 4) < 1), hd, hBd, alt_apply_comm hB 2 1,
    alt_apply_comm hB 3 1, alt_apply_comm hB 3 2, h12]
  ring

end Alternating

section Fixed

variable [CharP K 2]

private def fixedBy (P : Subgroup (GL (Fin 4) K)) (B : Matrix (Fin 4) (Fin 4) K) : Prop :=
  B ∈ altSubgroup 4 K ∧
    ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B

private def fixedByOne (a : GL (Fin 4) K) (B : Matrix (Fin 4) (Fin 4) K) : Prop :=
  B ∈ altSubgroup 4 K ∧
    (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B

omit [CharP K 2] in
private lemma N_eq_zero_of_mem {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    {a : GL (Fin 4) K} (ha : a ∈ P) : ∀ i j, j ≤ i → N a i j = 0 :=
  fun _ _ hij => N_eq_zero_of_le (hU a ha).1 (hU a ha).2 hij

private lemma alt_eq_of_upper_entries {B C : Matrix (Fin 4) (Fin 4) K}
    (hB : B ∈ altSubgroup 4 K) (hC : C ∈ altSubgroup 4 K)
    (h01 : B 0 1 = C 0 1) (h02 : B 0 2 = C 0 2) (h03 : B 0 3 = C 0 3)
    (h12 : B 1 2 = C 1 2) (h13 : B 1 3 = C 1 3) (h23 : B 2 3 = C 2 3) : B = C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [alt_apply_comm hB 1 0, alt_apply_comm hB 2 0, alt_apply_comm hB 3 0,
      alt_apply_comm hB 2 1, alt_apply_comm hB 3 1, alt_apply_comm hB 3 2,
      alt_apply_comm hC 1 0, alt_apply_comm hC 2 0, alt_apply_comm hC 3 0,
      alt_apply_comm hC 2 1, alt_apply_comm hC 3 1, alt_apply_comm hC 3 2,
      hB.2, hC.2]

private def p1 {P : Subgroup (GL (Fin 4) K)} (a : P) : Fin 4 → K :=
  ![N (a : GL (Fin 4) K) 0 2, N (a : GL (Fin 4) K) 0 3,
    N (a : GL (Fin 4) K) 1 2, N (a : GL (Fin 4) K) 1 3]

private def p2 {P : Subgroup (GL (Fin 4) K)} (a : P) : Fin 4 → K :=
  ![N (a : GL (Fin 4) K) 0 1, N (a : GL (Fin 4) K) 0 2,
    N (a : GL (Fin 4) K) 1 3, N (a : GL (Fin 4) K) 2 3]

omit [CharP K 2] in
private lemma p1_injective {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (h01 : ∀ a ∈ P, N a 0 1 = 0) (h23 : ∀ a ∈ P, N a 2 3 = 0) :
    Function.Injective (fun a : P => p1 a) := by
  intro a b h
  have e02 : N (a : GL (Fin 4) K) 0 2 = N (b : GL (Fin 4) K) 0 2 := by
    simpa [p1] using congrFun h 0
  have e03 : N (a : GL (Fin 4) K) 0 3 = N (b : GL (Fin 4) K) 0 3 := by
    simpa [p1] using congrFun h 1
  have e12 : N (a : GL (Fin 4) K) 1 2 = N (b : GL (Fin 4) K) 1 2 := by
    simpa [p1] using congrFun h 2
  have e13 : N (a : GL (Fin 4) K) 1 3 = N (b : GL (Fin 4) K) 1 3 := by
    simpa [p1] using congrFun h 3
  apply Subtype.ext
  apply Units.ext
  have hN : N (a : GL (Fin 4) K) = N (b : GL (Fin 4) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [N_eq_zero_of_mem hU a.2, N_eq_zero_of_mem hU b.2]
  rw [eq_one_add_N (a : GL (Fin 4) K), eq_one_add_N (b : GL (Fin 4) K), hN]

omit [CharP K 2] in
private lemma p2_one {P : Subgroup (GL (Fin 4) K)} : p2 (1 : P) = 0 := by
  funext i
  fin_cases i <;> simp [p2, N_one]

omit [CharP K 2] in
private lemma p2_add {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (h12 : ∀ a ∈ P, N a 1 2 = 0) (a b : P) : p2 (a * b) = p2 a + p2 b := by
  have hNa := N_eq_zero_of_mem hU a.2
  have hNb := N_eq_zero_of_mem hU b.2
  have hcoe : ((a * b : P) : GL (Fin 4) K) =
      (a : GL (Fin 4) K) * (b : GL (Fin 4) K) := rfl
  have hNM : N ((a : GL (Fin 4) K) * (b : GL (Fin 4) K)) =
      N (a : GL (Fin 4) K) + N (b : GL (Fin 4) K) +
        N (a : GL (Fin 4) K) * N (b : GL (Fin 4) K) := N_mul_eq _ _
  funext i
  fin_cases i <;>
    simp [p2, hcoe, hNM, mul_entry_01 hNa hNb, mul_entry_02 hNa hNb, mul_entry_13 hNa hNb,
      mul_entry_23 hNa hNb, h12 b b.2, h12 a a.2]

private def p2Add {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (h12 : ∀ a ∈ P, N a 1 2 = 0) : Additive P →+ (Fin 4 → K) where
  toFun a := p2 (Additive.toMul a)
  map_zero' := p2_one
  map_add' a b := by
    change p2 (Additive.toMul a * Additive.toMul b) = p2 (Additive.toMul a) + p2 (Additive.toMul b)
    exact p2_add hU h12 _ _

private lemma beta_p2_eq_zero {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (a b : P) :
    beta (p2 b) (p2 a) = 0 := by
  have hNa := N_eq_zero_of_mem hU a.2
  have hNb := N_eq_zero_of_mem hU b.2
  have hcm := comm_entry_03 hNb hNa (comm_N (hcomm b b.2 a a.2))
  have hp : beta (p2 b) (p2 a) =
      N (b : GL (Fin 4) K) 0 1 * N (a : GL (Fin 4) K) 1 3 +
        N (b : GL (Fin 4) K) 1 3 * N (a : GL (Fin 4) K) 0 1 +
        N (b : GL (Fin 4) K) 0 2 * N (a : GL (Fin 4) K) 2 3 +
        N (b : GL (Fin 4) K) 2 3 * N (a : GL (Fin 4) K) 0 2 := by
    simp [p2, beta_apply]
  rw [hp]
  calc
    N (b : GL (Fin 4) K) 0 1 * N (a : GL (Fin 4) K) 1 3 +
        N (b : GL (Fin 4) K) 1 3 * N (a : GL (Fin 4) K) 0 1 +
        N (b : GL (Fin 4) K) 0 2 * N (a : GL (Fin 4) K) 2 3 +
        N (b : GL (Fin 4) K) 2 3 * N (a : GL (Fin 4) K) 0 2 =
      (N (b : GL (Fin 4) K) 0 1 * N (a : GL (Fin 4) K) 1 3 +
        N (b : GL (Fin 4) K) 0 2 * N (a : GL (Fin 4) K) 2 3) +
      (N (a : GL (Fin 4) K) 0 1 * N (b : GL (Fin 4) K) 1 3 +
        N (a : GL (Fin 4) K) 0 2 * N (b : GL (Fin 4) K) 2 3) := by ring
    _ = 0 := CharTwo.add_eq_zero.mpr hcm

end Fixed

section Conditions

variable [CharP K 2]

omit [CharP K 2] in
private lemma fixed_cond_03 {a : GL (Fin 4) K} {B : Matrix (Fin 4) (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hB : B ∈ altSubgroup 4 K)
    (hfix : (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B) :
    N a 0 1 * B 1 3 + N a 0 2 * B 2 3 = 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 3) hfix
  rw [congr_entry_03 hUa.1 hUa.2 hB.2] at h
  have h' : (a : Matrix (Fin 4) (Fin 4) K) 0 1 * B 1 3 +
      (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 2 3 = 0 := by
    have h'' : B 0 3 + ((a : Matrix (Fin 4) (Fin 4) K) 0 1 * B 1 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 2 3) = B 0 3 + 0 := by
      simpa [add_assoc] using h
    exact add_left_cancel h''
  rwa [← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 1),
    ← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 2)] at h'

private lemma fixed_cond_12 {a : GL (Fin 4) K} {B : Matrix (Fin 4) (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hB : B ∈ altSubgroup 4 K) (h12 : N a 1 2 = 0)
    (hfix : (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B) :
    N a 1 3 * B 2 3 + N a 2 3 * B 1 3 = 0 := by
  have ha12 : (a : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 := by
    rw [← N_apply_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    exact h12
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 2) hfix
  rw [congr_entry_12 hUa.1 hUa.2 hB hB.2 ha12] at h
  have h' : (a : Matrix (Fin 4) (Fin 4) K) 1 3 * B 2 3 +
      (a : Matrix (Fin 4) (Fin 4) K) 2 3 * B 1 3 = 0 := by
    have h'' : B 1 2 + ((a : Matrix (Fin 4) (Fin 4) K) 1 3 * B 2 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 2 3 * B 1 3) = B 1 2 + 0 := by
      simpa [add_assoc] using h
    exact add_left_cancel h''
  rwa [← N_apply_of_ne (by decide : (1 : Fin 4) ≠ 3),
    ← N_apply_of_ne (by decide : (2 : Fin 4) ≠ 3)] at h'

private lemma fixed_cond_02 {a : GL (Fin 4) K} {B : Matrix (Fin 4) (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hB : B ∈ altSubgroup 4 K) (h12 : N a 1 2 = 0)
    (hfix : (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B) :
    N a 0 1 * B 1 2 + N a 0 3 * B 2 3 +
      N a 2 3 * (B 0 3 + N a 0 1 * B 1 3 + N a 0 2 * B 2 3) = 0 := by
  have ha12 : (a : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 := by
    rw [← N_apply_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    exact h12
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 2) hfix
  rw [congr_entry_02 hUa.1 hUa.2 hB hB.2] at h
  have h' : (a : Matrix (Fin 4) (Fin 4) K) 0 1 * B 1 2 +
      (a : Matrix (Fin 4) (Fin 4) K) 0 3 * B 2 3 +
      (a : Matrix (Fin 4) (Fin 4) K) 2 3 * (B 0 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 0 1 * B 1 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 2 3) = 0 := by
    have h'' : B 0 2 + ((a : Matrix (Fin 4) (Fin 4) K) 0 1 * B 1 2 +
        (a : Matrix (Fin 4) (Fin 4) K) 0 3 * B 2 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 2 3 * (B 0 3 +
          (a : Matrix (Fin 4) (Fin 4) K) 0 1 * B 1 3 +
          (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 2 3)) = B 0 2 + 0 := by
      simpa [add_assoc] using h
    exact add_left_cancel h''
  rwa [← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 1),
    ← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 3),
    ← N_apply_of_ne (by decide : (2 : Fin 4) ≠ 3),
    ← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 2)] at h'

private lemma fixed_cond_01 {a : GL (Fin 4) K} {B : Matrix (Fin 4) (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hB : B ∈ altSubgroup 4 K) (h12 : N a 1 2 = 0)
    (hfix : (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B) :
    N a 0 2 * B 1 2 + N a 0 3 * B 1 3 + N a 1 3 * B 0 3 +
      N a 1 3 * (N a 0 1 * B 1 3 + N a 0 2 * B 2 3) = 0 := by
  have ha12 : (a : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 := by
    rw [← N_apply_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    exact h12
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 1) hfix
  rw [congr_entry_01_case2 hUa.1 hUa.2 hB hB.2 ha12] at h
  have h' : (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 1 2 +
      (a : Matrix (Fin 4) (Fin 4) K) 0 3 * B 1 3 +
      (a : Matrix (Fin 4) (Fin 4) K) 1 3 * B 0 3 +
      (a : Matrix (Fin 4) (Fin 4) K) 1 3 * ((a : Matrix (Fin 4) (Fin 4) K) 0 1 * B 1 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 2 3) = 0 := by
    have h'' : B 0 1 + ((a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 1 2 +
        (a : Matrix (Fin 4) (Fin 4) K) 0 3 * B 1 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 1 3 * B 0 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 1 3 * ((a : Matrix (Fin 4) (Fin 4) K) 0 1 * B 1 3 +
          (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 2 3)) = B 0 1 + 0 := by
      simpa [add_assoc] using h
    exact add_left_cancel h''
  rwa [← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 2),
    ← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 3),
    ← N_apply_of_ne (by decide : (1 : Fin 4) ≠ 3),
    ← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 1)] at h'

private lemma fixed_cond_01_case1 {a : GL (Fin 4) K} {B : Matrix (Fin 4) (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hB : B ∈ altSubgroup 4 K) (h01 : N a 0 1 = 0) (h23 : B 2 3 = 0)
    (hfix : (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B) :
    N a 1 2 * B 0 2 + N a 1 3 * B 0 3 + N a 0 2 * B 1 2 + N a 0 3 * B 1 3 = 0 := by
  have ha01 : (a : Matrix (Fin 4) (Fin 4) K) 0 1 = 0 := by
    rw [← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 1)]
    exact h01
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 1) hfix
  rw [congr_entry_01_case1 hUa.1 hUa.2 hB hB.2 ha01 h23] at h
  have h' : (a : Matrix (Fin 4) (Fin 4) K) 1 2 * B 0 2 +
      (a : Matrix (Fin 4) (Fin 4) K) 1 3 * B 0 3 +
      (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 1 2 +
      (a : Matrix (Fin 4) (Fin 4) K) 0 3 * B 1 3 = 0 := by
    have h'' : B 0 1 + ((a : Matrix (Fin 4) (Fin 4) K) 1 2 * B 0 2 +
        (a : Matrix (Fin 4) (Fin 4) K) 1 3 * B 0 3 +
        (a : Matrix (Fin 4) (Fin 4) K) 0 2 * B 1 2 +
        (a : Matrix (Fin 4) (Fin 4) K) 0 3 * B 1 3) = B 0 1 + 0 := by
      simpa [add_assoc] using h
    exact add_left_cancel h''
  rwa [← N_apply_of_ne (by decide : (1 : Fin 4) ≠ 2),
    ← N_apply_of_ne (by decide : (1 : Fin 4) ≠ 3),
    ← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 2),
    ← N_apply_of_ne (by decide : (0 : Fin 4) ≠ 3)] at h'

end Conditions

section CaseOne

variable [CharP K 2]

private lemma case1_N01_eq_zero {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hsq : ∀ a ∈ P, a * a = 1)
    {a0 : GL (Fin 4) K} (ha0 : a0 ∈ P) (hd0 : N a0 1 2 ≠ 0) :
    ∀ a ∈ P, N a 0 1 = 0 := by
  have hN0 := N_eq_zero_of_mem hU ha0
  have h02 := congrArg (fun X : Matrix (Fin 4) (Fin 4) K => X 0 2) (N_mul_self (hsq a0 ha0))
  rw [mul_entry_02 hN0 hN0] at h02
  have hN01 : N a0 0 1 = 0 := (mul_eq_zero.mp h02).resolve_right hd0
  intro a ha
  have hNa := N_eq_zero_of_mem hU ha
  have h := comm_entry_02 hNa hN0 (comm_N (hcomm a ha a0 ha0))
  rw [hN01, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_right hd0

private lemma case1_N23_eq_zero {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hsq : ∀ a ∈ P, a * a = 1)
    {a0 : GL (Fin 4) K} (ha0 : a0 ∈ P) (hd0 : N a0 1 2 ≠ 0) :
    ∀ a ∈ P, N a 2 3 = 0 := by
  have hN0 := N_eq_zero_of_mem hU ha0
  have h13 := congrArg (fun X : Matrix (Fin 4) (Fin 4) K => X 1 3) (N_mul_self (hsq a0 ha0))
  rw [mul_entry_13 hN0 hN0] at h13
  have hN23 : N a0 2 3 = 0 := (mul_eq_zero.mp h13).resolve_left hd0
  intro a ha
  have hNa := N_eq_zero_of_mem hU ha
  have h := comm_entry_13 hNa hN0 (comm_N (hcomm a ha a0 ha0))
  rw [hN23, mul_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hd0

omit [CharP K 2] in
private lemma case1_B23_eq_zero {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    {a0 : GL (Fin 4) K} (ha0 : a0 ∈ P) (hd0 : N a0 1 2 ≠ 0)
    {B : Matrix (Fin 4) (Fin 4) K} (hB : B ∈ altSubgroup 4 K)
    (hfix : (a0 : Matrix (Fin 4) (Fin 4) K) * B * (a0 : Matrix (Fin 4) (Fin 4) K)ᵀ = B) :
    B 2 3 = 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 3) hfix
  rw [congr_entry_13 (hU a0 ha0).1 (hU a0 ha0).2 hB.2] at h
  have h' : (a0 : Matrix (Fin 4) (Fin 4) K) 1 2 * B 2 3 = 0 := by
    have h'' : B 1 3 + (a0 : Matrix (Fin 4) (Fin 4) K) 1 2 * B 2 3 = B 1 3 + 0 := by
      simpa using h
    exact add_left_cancel h''
  rw [← N_apply_of_ne (by decide : (1 : Fin 4) ≠ 2)] at h'
  exact (mul_eq_zero.mp h').resolve_left hd0

private lemma case1_ell_eq_zero {P : Subgroup (GL (Fin 4) K)}
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    {a : GL (Fin 4) K} (ha : a ∈ P) {B : Matrix (Fin 4) (Fin 4) K}
    (hB : B ∈ altSubgroup 4 K) (h01 : N a 0 1 = 0) (h23 : B 2 3 = 0)
    (hfix : (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B) :
    N a 1 2 * B 0 2 + N a 1 3 * B 0 3 + N a 0 2 * B 1 2 + N a 0 3 * B 1 3 = 0 :=
  fixed_cond_01_case1 (hU a ha) hB h01 h23 hfix

private theorem card_case1 [Finite K]
    (P : Subgroup (GL (Fin 4) K))
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hsq : ∀ a ∈ P, a * a = 1)
    (a0 : GL (Fin 4) K) (ha0 : a0 ∈ P) (hd0 : N a0 1 2 ≠ 0) :
    Nat.card P * Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B} ≤
      Nat.card K ^ 5 := by
  classical
  have : Nonempty K := ⟨0⟩
  have h01 := case1_N01_eq_zero hU hcomm hsq ha0 hd0
  have h23 := case1_N23_eq_zero hU hcomm hsq ha0 hd0
  have hpinj : Function.Injective (fun a : P => p1 a) := p1_injective hU h01 h23
  let S : Submodule K (Fin 4 → K) := Submodule.span K (Set.range (fun a : P => p1 a))
  have hPle : Nat.card P ≤ Nat.card S := by
    let f : P → S := fun a => ⟨p1 a, Submodule.subset_span (Set.mem_range_self a)⟩
    have hf : Function.Injective f := by
      intro a b h
      exact hpinj (Subtype.ext_iff.mp h)
    exact Nat.card_le_card_of_injective f hf
  have hfixle : Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B} ≤
      Nat.card K * Nat.card (beta.orthogonal S) := by
    let g : {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B} → K × (beta.orthogonal S) :=
      fun B =>
        (B.1 0 1, ⟨![B.1 0 2, B.1 0 3, B.1 1 2, B.1 1 3], by
          change ![B.1 0 2, B.1 0 3, B.1 1 2, B.1 1 3] ∈
            Submodule.orthogonalBilin beta S
          rw [Submodule.mem_orthogonalBilin_span]
          rintro x ⟨a, rfl⟩
          have hB23 : B.1 2 3 = 0 :=
            case1_B23_eq_zero hU ha0 hd0 B.2.1 (B.2.2 a0 ha0)
          have hell := case1_ell_eq_zero hU a.2 B.2.1 (h01 a a.2) hB23 (B.2.2 a a.2)
          have hb : beta (p1 a) ![B.1 0 2, B.1 0 3, B.1 1 2, B.1 1 3] =
              N a 1 2 * B.1 0 2 + N a 1 3 * B.1 0 3 +
                N a 0 2 * B.1 1 2 + N a 0 3 * B.1 1 3 := by
            simp [p1, beta_apply]
            ring
          rw [hb]
          exact hell⟩)
    have hg : Function.Injective g := by
      rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
      have h01' : B 0 1 = B' 0 1 := congrArg Prod.fst h
      have hc : (![B 0 2, B 0 3, B 1 2, B 1 3] : Fin 4 → K) =
          ![B' 0 2, B' 0 3, B' 1 2, B' 1 3] :=
        congrArg (fun x : K × (beta.orthogonal S) => (x.2 : Fin 4 → K)) h
      have h02 : B 0 2 = B' 0 2 := by simpa using congrFun hc 0
      have h03 : B 0 3 = B' 0 3 := by simpa using congrFun hc 1
      have h12 : B 1 2 = B' 1 2 := by simpa using congrFun hc 2
      have h13 : B 1 3 = B' 1 3 := by simpa using congrFun hc 3
      have hB23 : B 2 3 = 0 :=
        case1_B23_eq_zero hU ha0 hd0 hB.1 (hB.2 a0 ha0)
      have hB'23 : B' 2 3 = 0 :=
        case1_B23_eq_zero hU ha0 hd0 hB'.1 (hB'.2 a0 ha0)
      exact Subtype.ext (alt_eq_of_upper_entries hB.1 hB'.1 h01' h02 h03 h12 h13
        (by simpa using hB23.trans hB'23.symm))
    calc Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B}
        ≤ Nat.card (K × (beta.orthogonal S)) := Nat.card_le_card_of_injective g hg
    _ = Nat.card K * Nat.card (beta.orthogonal S) := Nat.card_prod _ _
  have hdimV : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  have horth := LinearMap.BilinForm.finrank_orthogonal beta_nondegenerate S
  have hSle : Module.finrank K S ≤ 4 := by
    have := Submodule.finrank_le S
    rwa [hdimV] at this
  have hsum : Module.finrank K S + Module.finrank K (beta.orthogonal S) = 4 := by
    rw [horth, hdimV]
    omega
  have hcardS : Nat.card S = Nat.card K ^ Module.finrank K S :=
    Module.natCard_eq_pow_finrank (K := K) (V := S)
  have hcardO : Nat.card (beta.orthogonal S) =
      Nat.card K ^ Module.finrank K (beta.orthogonal S) :=
    Module.natCard_eq_pow_finrank (K := K) (V := beta.orthogonal S)
  calc Nat.card P * Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B}
      ≤ Nat.card S * (Nat.card K * Nat.card (beta.orthogonal S)) := Nat.mul_le_mul hPle hfixle
  _ = Nat.card K * (Nat.card S * Nat.card (beta.orthogonal S)) := by ring
  _ = Nat.card K * (Nat.card K ^ Module.finrank K S *
        Nat.card K ^ Module.finrank K (beta.orthogonal S)) := by rw [hcardS, hcardO]
  _ = Nat.card K * Nat.card K ^ (Module.finrank K S +
        Module.finrank K (beta.orthogonal S)) := by rw [← pow_add]
  _ = Nat.card K * Nat.card K ^ 4 := by rw [hsum]
  _ = Nat.card K ^ 5 := by ring
  _ ≤ Nat.card K ^ 5 := le_rfl

end CaseOne

section CaseTwo

variable [CharP K 2]

private lemma eq_add_of_add_add_eq_zero {a b c : K} (h : a + b + c = 0) : a = b + c := by
  have h1 : a + b = c := CharTwo.add_eq_zero.mp h
  have h2 : (a + b) + b = c + b := congrArg (fun x => x + b) h1
  calc a = (a + b) + b := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  _ = c + b := h2
  _ = b + c := by rw [add_comm]

private lemma card_fixedByOne_alpha_le [Finite K] {a : GL (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hN12 : N a 1 2 = 0) (hα : N a 0 1 ≠ 0) :
    Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B} ≤ Nat.card K ^ 4 := by
  classical
  have : Nonempty K := ⟨0⟩
  let f : {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B} → (Fin 4 → K) :=
    fun B => ![B.1 0 1, B.1 0 2, B.1 0 3, B.1 2 3]
  have hf : Function.Injective f := by
    rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
    have c01 : B 0 1 = B' 0 1 := by simpa [f] using congrFun h 0
    have c02 : B 0 2 = B' 0 2 := by simpa [f] using congrFun h 1
    have c03 : B 0 3 = B' 0 3 := by simpa [f] using congrFun h 2
    have c23 : B 2 3 = B' 2 3 := by simpa [f] using congrFun h 3
    have iB : N a 0 1 * B 1 3 + N a 0 2 * B 2 3 = 0 := fixed_cond_03 hUa hB.1 hB.2
    have iB' : N a 0 1 * B' 1 3 + N a 0 2 * B' 2 3 = 0 := fixed_cond_03 hUa hB'.1 hB'.2
    have eB13 : N a 0 1 * B 1 3 = N a 0 2 * B 2 3 := CharTwo.add_eq_zero.mp iB
    have eB'13 : N a 0 1 * B' 1 3 = N a 0 2 * B' 2 3 := CharTwo.add_eq_zero.mp iB'
    have c13 : B 1 3 = B' 1 3 := by
      have hmul : N a 0 1 * B 1 3 = N a 0 1 * B' 1 3 := by rw [eB13, eB'13, c23]
      exact mul_left_cancel₀ hα hmul
    have jB : N a 0 1 * B 1 2 + N a 0 3 * B 2 3 +
        N a 2 3 * (B 0 3 + N a 0 1 * B 1 3 + N a 0 2 * B 2 3) = 0 :=
      fixed_cond_02 hUa hB.1 hN12 hB.2
    have jB' : N a 0 1 * B' 1 2 + N a 0 3 * B' 2 3 +
        N a 2 3 * (B' 0 3 + N a 0 1 * B' 1 3 + N a 0 2 * B' 2 3) = 0 :=
      fixed_cond_02 hUa hB'.1 hN12 hB'.2
    have hsum : B 0 3 + N a 0 1 * B 1 3 + N a 0 2 * B 2 3 = B 0 3 := by
      rw [add_assoc, iB, add_zero]
    have hsum' : B' 0 3 + N a 0 1 * B' 1 3 + N a 0 2 * B' 2 3 = B' 0 3 := by
      rw [add_assoc, iB', add_zero]
    have kB : N a 0 1 * B 1 2 + N a 0 3 * B 2 3 + N a 2 3 * B 0 3 = 0 := by
      have := jB
      rw [hsum] at this
      exact this
    have kB' : N a 0 1 * B' 1 2 + N a 0 3 * B' 2 3 + N a 2 3 * B' 0 3 = 0 := by
      have := jB'
      rw [hsum'] at this
      exact this
    have eB12 : N a 0 1 * B 1 2 = N a 0 3 * B 2 3 + N a 2 3 * B 0 3 :=
      eq_add_of_add_add_eq_zero kB
    have eB'12 : N a 0 1 * B' 1 2 = N a 0 3 * B' 2 3 + N a 2 3 * B' 0 3 :=
      eq_add_of_add_add_eq_zero kB'
    have c12 : B 1 2 = B' 1 2 := by
      have hmul : N a 0 1 * B 1 2 = N a 0 1 * B' 1 2 := by rw [eB12, eB'12, c23, c03]
      exact mul_left_cancel₀ hα hmul
    exact Subtype.ext (alt_eq_of_upper_entries hB.1 hB'.1 c01 c02 c03 c12 c13 c23)
  calc Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B}
      ≤ Nat.card (Fin 4 → K) := Nat.card_le_card_of_injective f hf
  _ = Nat.card K ^ 4 := by rw [Nat.card_fun]; norm_num

private lemma card_fixedByOne_beta_le [Finite K] {a : GL (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hN12 : N a 1 2 = 0) (hα : N a 0 1 = 0) (hβ : N a 0 2 ≠ 0) :
    Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B} ≤ Nat.card K ^ 4 := by
  classical
  have : Nonempty K := ⟨0⟩
  let f : {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B} → (Fin 4 → K) :=
    fun B => ![B.1 0 1, B.1 0 2, B.1 0 3, B.1 1 3]
  have hf : Function.Injective f := by
    rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
    have c01 : B 0 1 = B' 0 1 := by simpa [f] using congrFun h 0
    have c02 : B 0 2 = B' 0 2 := by simpa [f] using congrFun h 1
    have c03 : B 0 3 = B' 0 3 := by simpa [f] using congrFun h 2
    have c13 : B 1 3 = B' 1 3 := by simpa [f] using congrFun h 3
    have iB : N a 0 1 * B 1 3 + N a 0 2 * B 2 3 = 0 := fixed_cond_03 hUa hB.1 hB.2
    have iB' : N a 0 1 * B' 1 3 + N a 0 2 * B' 2 3 = 0 := fixed_cond_03 hUa hB'.1 hB'.2
    have cB23 : B 2 3 = 0 := by
      have := iB
      rw [hα, zero_mul, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hβ
    have cB'23 : B' 2 3 = 0 := by
      have := iB'
      rw [hα, zero_mul, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hβ
    have jB : N a 0 2 * B 1 2 + N a 0 3 * B 1 3 + N a 1 3 * B 0 3 +
        N a 1 3 * (N a 0 1 * B 1 3 + N a 0 2 * B 2 3) = 0 :=
      fixed_cond_01 hUa hB.1 hN12 hB.2
    have jB' : N a 0 2 * B' 1 2 + N a 0 3 * B' 1 3 + N a 1 3 * B' 0 3 +
        N a 1 3 * (N a 0 1 * B' 1 3 + N a 0 2 * B' 2 3) = 0 :=
      fixed_cond_01 hUa hB'.1 hN12 hB'.2
    have lB : N a 0 2 * B 1 2 + N a 0 3 * B 1 3 + N a 1 3 * B 0 3 = 0 := by
      have := jB
      rw [iB, mul_zero, add_zero] at this
      exact this
    have lB' : N a 0 2 * B' 1 2 + N a 0 3 * B' 1 3 + N a 1 3 * B' 0 3 = 0 := by
      have := jB'
      rw [iB', mul_zero, add_zero] at this
      exact this
    have eB12 : N a 0 2 * B 1 2 = N a 0 3 * B 1 3 + N a 1 3 * B 0 3 :=
      eq_add_of_add_add_eq_zero lB
    have eB'12 : N a 0 2 * B' 1 2 = N a 0 3 * B' 1 3 + N a 1 3 * B' 0 3 :=
      eq_add_of_add_add_eq_zero lB'
    have c12 : B 1 2 = B' 1 2 := by
      have hmul : N a 0 2 * B 1 2 = N a 0 2 * B' 1 2 := by rw [eB12, eB'12, c13, c03]
      exact mul_left_cancel₀ hβ hmul
    have c23 : B 2 3 = B' 2 3 := by rw [cB23, cB'23]
    exact Subtype.ext (alt_eq_of_upper_entries hB.1 hB'.1 c01 c02 c03 c12 c13 c23)
  calc Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B}
      ≤ Nat.card (Fin 4 → K) := Nat.card_le_card_of_injective f hf
  _ = Nat.card K ^ 4 := by rw [Nat.card_fun]; norm_num

private lemma card_fixedByOne_u_le [Finite K] {a : GL (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hN12 : N a 1 2 = 0) (hα : N a 0 1 = 0) (hβ : N a 0 2 = 0) (hu : N a 1 3 ≠ 0) :
    Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B} ≤ Nat.card K ^ 4 := by
  classical
  have : Nonempty K := ⟨0⟩
  let f : {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B} → (Fin 4 → K) :=
    fun B => ![B.1 0 1, B.1 0 2, B.1 1 2, B.1 1 3]
  have hf : Function.Injective f := by
    rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
    have c01 : B 0 1 = B' 0 1 := by simpa [f] using congrFun h 0
    have c02 : B 0 2 = B' 0 2 := by simpa [f] using congrFun h 1
    have c12 : B 1 2 = B' 1 2 := by simpa [f] using congrFun h 2
    have c13 : B 1 3 = B' 1 3 := by simpa [f] using congrFun h 3
    have iB : N a 1 3 * B 2 3 + N a 2 3 * B 1 3 = 0 := fixed_cond_12 hUa hB.1 hN12 hB.2
    have iB' : N a 1 3 * B' 2 3 + N a 2 3 * B' 1 3 = 0 := fixed_cond_12 hUa hB'.1 hN12 hB'.2
    have eB23 : N a 1 3 * B 2 3 = N a 2 3 * B 1 3 := CharTwo.add_eq_zero.mp iB
    have eB'23 : N a 1 3 * B' 2 3 = N a 2 3 * B' 1 3 := CharTwo.add_eq_zero.mp iB'
    have jB : N a 0 2 * B 1 2 + N a 0 3 * B 1 3 + N a 1 3 * B 0 3 +
        N a 1 3 * (N a 0 1 * B 1 3 + N a 0 2 * B 2 3) = 0 :=
      fixed_cond_01 hUa hB.1 hN12 hB.2
    have jB' : N a 0 2 * B' 1 2 + N a 0 3 * B' 1 3 + N a 1 3 * B' 0 3 +
        N a 1 3 * (N a 0 1 * B' 1 3 + N a 0 2 * B' 2 3) = 0 :=
      fixed_cond_01 hUa hB'.1 hN12 hB'.2
    have lB : N a 0 3 * B 1 3 + N a 1 3 * B 0 3 = 0 := by
      have := jB
      simp [hα, hβ] at this
      exact this
    have lB' : N a 0 3 * B' 1 3 + N a 1 3 * B' 0 3 = 0 := by
      have := jB'
      simp [hα, hβ] at this
      exact this
    have eB03 : N a 1 3 * B 0 3 = N a 0 3 * B 1 3 := (CharTwo.add_eq_zero.mp lB).symm
    have eB'03 : N a 1 3 * B' 0 3 = N a 0 3 * B' 1 3 := (CharTwo.add_eq_zero.mp lB').symm
    have c03 : B 0 3 = B' 0 3 := by
      have hmul : N a 1 3 * B 0 3 = N a 1 3 * B' 0 3 := by rw [eB03, eB'03, c13]
      exact mul_left_cancel₀ hu hmul
    have c23 : B 2 3 = B' 2 3 := by
      have hmul : N a 1 3 * B 2 3 = N a 1 3 * B' 2 3 := by rw [eB23, eB'23, c13]
      exact mul_left_cancel₀ hu hmul
    exact Subtype.ext (alt_eq_of_upper_entries hB.1 hB'.1 c01 c02 c03 c12 c13 c23)
  calc Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B}
      ≤ Nat.card (Fin 4 → K) := Nat.card_le_card_of_injective f hf
  _ = Nat.card K ^ 4 := by rw [Nat.card_fun]; norm_num

private lemma card_fixedByOne_h_le [Finite K] {a : GL (Fin 4) K}
    (hUa : (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hN12 : N a 1 2 = 0) (hα : N a 0 1 = 0) (hβ : N a 0 2 = 0)
    (hu : N a 1 3 = 0) (hh : N a 2 3 ≠ 0) :
    Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B} ≤ Nat.card K ^ 4 := by
  classical
  have : Nonempty K := ⟨0⟩
  let f : {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B} → (Fin 4 → K) :=
    fun B => ![B.1 0 1, B.1 0 2, B.1 1 2, B.1 2 3]
  have hf : Function.Injective f := by
    rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
    have c01 : B 0 1 = B' 0 1 := by simpa [f] using congrFun h 0
    have c02 : B 0 2 = B' 0 2 := by simpa [f] using congrFun h 1
    have c12 : B 1 2 = B' 1 2 := by simpa [f] using congrFun h 2
    have c23 : B 2 3 = B' 2 3 := by simpa [f] using congrFun h 3
    have iB : N a 1 3 * B 2 3 + N a 2 3 * B 1 3 = 0 := fixed_cond_12 hUa hB.1 hN12 hB.2
    have iB' : N a 1 3 * B' 2 3 + N a 2 3 * B' 1 3 = 0 := fixed_cond_12 hUa hB'.1 hN12 hB'.2
    have cB13 : B 1 3 = 0 := by
      have := iB
      rw [hu, zero_mul, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hh
    have cB'13 : B' 1 3 = 0 := by
      have := iB'
      rw [hu, zero_mul, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hh
    have jB : N a 0 1 * B 1 2 + N a 0 3 * B 2 3 +
        N a 2 3 * (B 0 3 + N a 0 1 * B 1 3 + N a 0 2 * B 2 3) = 0 :=
      fixed_cond_02 hUa hB.1 hN12 hB.2
    have jB' : N a 0 1 * B' 1 2 + N a 0 3 * B' 2 3 +
        N a 2 3 * (B' 0 3 + N a 0 1 * B' 1 3 + N a 0 2 * B' 2 3) = 0 :=
      fixed_cond_02 hUa hB'.1 hN12 hB'.2
    have lB : N a 0 3 * B 2 3 + N a 2 3 * B 0 3 = 0 := by
      have := jB
      simp [hα, hβ] at this
      exact this
    have lB' : N a 0 3 * B' 2 3 + N a 2 3 * B' 0 3 = 0 := by
      have := jB'
      simp [hα, hβ] at this
      exact this
    have eB03 : N a 2 3 * B 0 3 = N a 0 3 * B 2 3 := (CharTwo.add_eq_zero.mp lB).symm
    have eB'03 : N a 2 3 * B' 0 3 = N a 0 3 * B' 2 3 := (CharTwo.add_eq_zero.mp lB').symm
    have c03 : B 0 3 = B' 0 3 := by
      have hmul : N a 2 3 * B 0 3 = N a 2 3 * B' 0 3 := by rw [eB03, eB'03, c23]
      exact mul_left_cancel₀ hh hmul
    have c13 : B 1 3 = B' 1 3 := by rw [cB13, cB'13]
    exact Subtype.ext (alt_eq_of_upper_entries hB.1 hB'.1 c01 c02 c03 c12 c13 c23)
  calc Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a B}
      ≤ Nat.card (Fin 4 → K) := Nat.card_le_card_of_injective f hf
  _ = Nat.card K ^ 4 := by rw [Nat.card_fun]; norm_num

private theorem card_case2 [Finite K]
    (P : Subgroup (GL (Fin 4) K))
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hN12 : ∀ a ∈ P, N a 1 2 = 0) :
    Nat.card P * Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B} ≤
      Nat.card K ^ 7 := by
  classical
  have : Nonempty K := ⟨0⟩
  let S : Submodule K (Fin 4 → K) := Submodule.span K (Set.range (fun a : P => p2 a))
  let f := p2Add hU hN12
  have hker : Nat.card f.ker ≤ Nat.card K := by
    let g : f.ker → K := fun x => N ((Additive.toMul x.1 : P) : GL (Fin 4) K) 0 3
    have hg : Function.Injective g := by
      intro x y hxy
      have hx0 : p2 (Additive.toMul x.1) = 0 := x.2
      have hy0 : p2 (Additive.toMul y.1) = 0 := y.2
      have hx01 : N ((Additive.toMul x.1 : P) : GL (Fin 4) K) 0 1 = 0 := by
        simpa [p2] using congrFun hx0 0
      have hx02 : N ((Additive.toMul x.1 : P) : GL (Fin 4) K) 0 2 = 0 := by
        simpa [p2] using congrFun hx0 1
      have hx13 : N ((Additive.toMul x.1 : P) : GL (Fin 4) K) 1 3 = 0 := by
        simpa [p2] using congrFun hx0 2
      have hx23 : N ((Additive.toMul x.1 : P) : GL (Fin 4) K) 2 3 = 0 := by
        simpa [p2] using congrFun hx0 3
      have hy01 : N ((Additive.toMul y.1 : P) : GL (Fin 4) K) 0 1 = 0 := by
        simpa [p2] using congrFun hy0 0
      have hy02 : N ((Additive.toMul y.1 : P) : GL (Fin 4) K) 0 2 = 0 := by
        simpa [p2] using congrFun hy0 1
      have hy13 : N ((Additive.toMul y.1 : P) : GL (Fin 4) K) 1 3 = 0 := by
        simpa [p2] using congrFun hy0 2
      have hy23 : N ((Additive.toMul y.1 : P) : GL (Fin 4) K) 2 3 = 0 := by
        simpa [p2] using congrFun hy0 3
      have h03 : N ((Additive.toMul x.1 : P) : GL (Fin 4) K) 0 3 =
          N ((Additive.toMul y.1 : P) : GL (Fin 4) K) 0 3 := hxy
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      have hN : N ((Additive.toMul x.1 : P) : GL (Fin 4) K) =
          N ((Additive.toMul y.1 : P) : GL (Fin 4) K) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp_all [N_eq_zero_of_mem hU (Additive.toMul x.1).2,
            N_eq_zero_of_mem hU (Additive.toMul y.1).2,
            hN12 (Additive.toMul x.1).1 (Additive.toMul x.1).2,
            hN12 (Additive.toMul y.1).1 (Additive.toMul y.1).2]
      rw [eq_one_add_N, eq_one_add_N, hN]
    exact Nat.card_le_card_of_injective g hg
  have hrange : Nat.card f.range ≤ Nat.card S := by
    let g : f.range → S := fun x =>
      ⟨x.1, by
        obtain ⟨a, ha⟩ := x.2
        rw [← ha]
        exact Submodule.subset_span (Set.mem_range_self a)⟩
    have hg : Function.Injective g := by
      intro x y h
      have h' : x.1 = y.1 := congrArg (fun z : S => z.1) h
      exact Subtype.ext h'
    exact Nat.card_le_card_of_injective g hg
  have hPle : Nat.card P ≤ Nat.card K * Nat.card S := by
    calc Nat.card P = Nat.card (Additive P) := rfl
    _ = Nat.card f.ker * Nat.card f.range := (AddSubgroup.card_ker_mul_card_range f).symm
    _ ≤ Nat.card K * Nat.card S := Nat.mul_le_mul hker hrange
  have hSS : S ≤ beta.orthogonal S := by
    change Submodule.span K (Set.range (fun a : P => p2 a)) ≤ beta.orthogonal S
    rw [Submodule.span_le]
    rintro s ⟨a, rfl⟩
    change p2 a ∈ Submodule.orthogonalBilin beta
      (Submodule.span K (Set.range (fun a : P => p2 a)))
    rw [Submodule.mem_orthogonalBilin_span]
    rintro x ⟨b, rfl⟩
    exact beta_p2_eq_zero hU hcomm a b
  have hdim : Module.finrank K S ≤ 2 := by
    have hmono : Module.finrank K S ≤ Module.finrank K (beta.orthogonal S) :=
      Submodule.finrank_mono hSS
    have horth := LinearMap.BilinForm.finrank_orthogonal beta_nondegenerate S
    have hdimV : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
    have hSle : Module.finrank K S ≤ 4 := by
      have := Submodule.finrank_le S
      rwa [hdimV] at this
    rw [horth, hdimV] at hmono
    omega
  have hcardS : Nat.card S ≤ Nat.card K ^ 2 := by
    calc Nat.card S = Nat.card K ^ Module.finrank K S :=
        Module.natCard_eq_pow_finrank (K := K) (V := S)
    _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_right (Nat.card_pos (α := K)) hdim
  have hPle3 : Nat.card P ≤ Nat.card K ^ 3 := by
    calc Nat.card P ≤ Nat.card K * Nat.card S := hPle
    _ ≤ Nat.card K * Nat.card K ^ 2 := Nat.mul_le_mul_left _ hcardS
    _ = Nat.card K ^ 3 := by ring
  by_cases hp : ∀ a : P, p2 a = 0
  · have hcoord : ∀ a : P,
        N (a : GL (Fin 4) K) 0 1 = 0 ∧ N (a : GL (Fin 4) K) 0 2 = 0 ∧
        N (a : GL (Fin 4) K) 1 3 = 0 ∧ N (a : GL (Fin 4) K) 2 3 = 0 := by
      intro a
      have h := hp a
      exact ⟨by simpa [p2] using congrFun h 0, by simpa [p2] using congrFun h 1,
        by simpa [p2] using congrFun h 2, by simpa [p2] using congrFun h 3⟩
    have hPq : Nat.card P ≤ Nat.card K := by
      let gP : P → K := fun a => N (a : GL (Fin 4) K) 0 3
      have hgP : Function.Injective gP := by
        intro a b h
        obtain ⟨ha01, ha02, ha13, ha23⟩ := hcoord a
        obtain ⟨hb01, hb02, hb13, hb23⟩ := hcoord b
        have h03 : N (a : GL (Fin 4) K) 0 3 = N (b : GL (Fin 4) K) 0 3 := h
        apply Subtype.ext
        apply Units.ext
        have hN : N (a : GL (Fin 4) K) = N (b : GL (Fin 4) K) := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp_all [N_eq_zero_of_mem hU a.2, N_eq_zero_of_mem hU b.2,
              hN12 a.1 a.2, hN12 b.1 b.2]
        rw [eq_one_add_N, eq_one_add_N, hN]
      exact Nat.card_le_card_of_injective gP hgP
    have hfix6 : Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B} ≤
        Nat.card K ^ 6 := by
      let gF : {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B} → (Fin 6 → K) := fun B =>
        ![B.1 0 1, B.1 0 2, B.1 0 3, B.1 1 2, B.1 1 3, B.1 2 3]
      have hgF : Function.Injective gF := by
        rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
        have c01 : B 0 1 = B' 0 1 := by simpa [gF] using congrFun h 0
        have c02 : B 0 2 = B' 0 2 := by simpa [gF] using congrFun h 1
        have c03 : B 0 3 = B' 0 3 := by simpa [gF] using congrFun h 2
        have c12 : B 1 2 = B' 1 2 := by simpa [gF] using congrFun h 3
        have c13 : B 1 3 = B' 1 3 := by simpa [gF] using congrFun h 4
        have c23 : B 2 3 = B' 2 3 := by simpa [gF] using congrFun h 5
        exact Subtype.ext (alt_eq_of_upper_entries hB.1 hB'.1 c01 c02 c03 c12 c13 c23)
      calc Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B}
          ≤ Nat.card (Fin 6 → K) := Nat.card_le_card_of_injective gF hgF
      _ = Nat.card K ^ 6 := by rw [Nat.card_fun]; norm_num
    calc Nat.card P * Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B}
        ≤ Nat.card K * Nat.card K ^ 6 := Nat.mul_le_mul hPq hfix6
    _ = Nat.card K ^ 7 := by ring
  · push Not at hp
    obtain ⟨a0, hp0⟩ := hp
    have hincl : Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B} ≤
        Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a0.1 B} := by
      let i : {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B} →
          {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a0.1 B} := fun B =>
        ⟨B.1, B.2.1, B.2.2 a0.1 a0.2⟩
      have hi : Function.Injective i := by
        intro B B' h
        have h' : B.1 = B'.1 :=
          congrArg (fun z : {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a0.1 B} => z.1) h
        exact Subtype.ext h'
      exact Nat.card_le_card_of_injective i hi
    have hfix4 : Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedByOne a0.1 B} ≤
        Nat.card K ^ 4 := by
      by_cases hα : N a0.1 0 1 = 0
      · by_cases hβ : N a0.1 0 2 = 0
        · by_cases hu : N a0.1 1 3 = 0
          · have hh : N a0.1 2 3 ≠ 0 := by
              intro hh
              apply hp0
              funext i
              fin_cases i <;> simp [p2, hα, hβ, hu, hh]
            exact card_fixedByOne_h_le (hU a0.1 a0.2) (hN12 a0.1 a0.2) hα hβ hu hh
          · exact card_fixedByOne_u_le (hU a0.1 a0.2) (hN12 a0.1 a0.2) hα hβ hu
        · exact card_fixedByOne_beta_le (hU a0.1 a0.2) (hN12 a0.1 a0.2) hα hβ
      · exact card_fixedByOne_alpha_le (hU a0.1 a0.2) (hN12 a0.1 a0.2) hα
    calc Nat.card P * Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B}
        ≤ Nat.card K ^ 3 * Nat.card K ^ 4 := Nat.mul_le_mul hPle3 (le_trans hincl hfix4)
    _ = Nat.card K ^ 7 := by ring

end CaseTwo

theorem card_mul_card_altFix_le [Finite K] [CharP K 2] (P : Subgroup (GL (Fin 4) K))
    (hU : ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K).IsUpperTriangular ∧
      ∀ i, (a : Matrix (Fin 4) (Fin 4) K) i i = 1)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hsq : ∀ a ∈ P, a * a = 1) :
    Nat.card P * Nat.card {B : Matrix (Fin 4) (Fin 4) K // B ∈ altSubgroup 4 K ∧
      ∀ a ∈ P, (a : Matrix (Fin 4) (Fin 4) K) * B * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = B} ≤
      Nat.card K ^ 7 := by
  classical
  have : Nonempty K := ⟨0⟩
  by_cases hcase1 : ∃ a : GL (Fin 4) K, a ∈ P ∧ N a 1 2 ≠ 0
  · obtain ⟨a0, ha0, hd0⟩ := hcase1
    calc Nat.card P * Nat.card {B : Matrix (Fin 4) (Fin 4) K // fixedBy P B}
        ≤ Nat.card K ^ 5 := card_case1 P hU hcomm hsq a0 ha0 hd0
    _ ≤ Nat.card K ^ 7 := Nat.pow_le_pow_right (Nat.card_pos (α := K)) (by norm_num)
  · push Not at hcase1
    exact card_case2 P hU hcomm hcase1

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
