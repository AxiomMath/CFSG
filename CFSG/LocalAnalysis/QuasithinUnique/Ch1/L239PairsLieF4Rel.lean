module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Calc
public import CFSG.LieType.Ree.LargeReeInvolutionFusion

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open scoped commutatorElement

section Instances

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

theorem comm_famL₂
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {n i j : ℕ} (hi : i ≤ 11) (hj : j ≤ 11)
    {p q : Poly} (hp : varsBelow 24 p = true) (hq : varsBelow 24 q = true)
    {l : List (ℕ × Poly)} (hl : ∀ e ∈ l, e.1 ≤ 11 ∧ varsBelow 24 e.2 = true)
    (h : weq n (famWord i p (sigmaPoly p) ++ famWord j q (sigmaPoly q))
      (famProdWord l ++ famWord j q (sigmaPoly q) ++ famWord i p (sigmaPoly p)) = true)
    (s t : K) :
    ⁅fam m K i (polyEval (coordVal m s t 0 0 0 0 0 0 0 0 0 0) p),
        fam m K j (polyEval (coordVal m s t 0 0 0 0 0 0 0 0 0 0) q)⁆ =
      (l.map fun e => fam m K e.1 (polyEval (coordVal m s t 0 0 0 0 0 0 0 0 0 0) e.2)).prod :=
  comm_famL hK hi hj hp hq hl h _ (coordVal_add_twelve (m := m) s t 0 0 0 0 0 0 0 0 0 0)

theorem rel_C1
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    ⁅fam m K 1 s, fam m K 5 t⁆ = fam m K 9 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 5) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide) (l := [(9, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simpa [polyEval, monoEval, coordVal] using this

theorem rel_C2
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    ⁅fam m K 1 s, fam m K 11 t⁆ = fam m K 6 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide) (l := [(6, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simpa [polyEval, monoEval, coordVal] using this

theorem rel_C3
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    ⁅fam m K 3 s, fam m K 11 t⁆ = fam m K 8 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 3) (j := 11) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide) (l := [(8, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simpa [polyEval, monoEval, coordVal] using this

theorem rel_C6
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    ⁅fam m K 0 s, fam m K 7 t⁆ = fam m K 4 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 7) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide) (l := [(4, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  simpa [polyEval, monoEval, coordVal] using this

theorem rel_C4
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    ⁅fam m K 1 s, fam m K 4 t⁆ = fam m K 10 (s * t) *
      fam m K 6 (s * s * t * largeReeSigma m s) *
        fam m K 8 (s * largeReeSigma m s * largeReeSigma m t) := by
  have := comm_famL₂ hK (n := fuel) (i := 1) (j := 4) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(10, [[0, 1]]), (6, [[0, 0, 1, 12]]), (8, [[0, 12, 13]])]) (by decide)
    (by decide +kernel) s t
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

theorem rel_C5
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    ⁅fam m K 2 s, fam m K 4 t⁆ = fam m K 11 (s * t) *
      fam m K 6 (t * largeReeSigma m s) * fam m K 8 (s * largeReeSigma m t) := by
  have := comm_famL₂ hK (n := fuel) (i := 2) (j := 4) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide)
    (l := [(11, [[0, 1]]), (6, [[1, 12]]), (8, [[0, 13]])]) (by decide)
    (by decide +kernel) s t
  simpa [polyEval, monoEval, coordVal, mul_assoc] using this

end Instances

section Prod

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

theorem prod_fam_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {n : ℕ} {l₁ l₂ : List (ℕ × Poly)}
    (hl₁ : ∀ e ∈ l₁, e.1 ≤ 11 ∧ varsBelow 24 e.2 = true)
    (hl₂ : ∀ e ∈ l₂, e.1 ≤ 11 ∧ varsBelow 24 e.2 = true)
    (h : weq n (famProdWord l₁) (famProdWord l₂) = true) (x : ℕ → K)
    (hx : ∀ n < 12, x (n + 12) = largeReeSigma m (x n)) :
    (l₁.map fun e => fam m K e.1 (polyEval x e.2)).prod =
      (l₂.map fun e => fam m K e.1 (polyEval x e.2)).prod := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have := wordEval_eq_of_weq (R := K) h x
  rwa [wordEval_famProdWord hK x hx l₁ hl₁, wordEval_famProdWord hK x hx l₂ hl₂] at this

theorem rel_addH
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    fam m K 7 s * fam m K 7 t = fam m K 7 (s + t) * fam m K 8 (t * largeReeSigma m s) := by
  have := prod_fam_eq (m := m) hK (n := fuel) (l₁ := [(7, [[0]]), (7, [[1]])])
    (l₂ := [(7, [[0], [1]]), (8, [[1, 12]])]) (by decide) (by decide) (by decide +kernel)
    (coordVal m s t 0 0 0 0 0 0 0 0 0 0) (coordVal_add_twelve (m := m) s t 0 0 0 0 0 0 0 0 0 0)
  simpa [polyEval, monoEval, coordVal] using this

end Prod

section Split

variable {m : ℕ} {K : Type} [Field K]

set_option linter.unusedSimpArgs false

omit [Field K] in
@[expose] def blkWord (r₁ r₂ r₃ r₄ : ℕ) : Word :=
  [(r₁, [[0]]), (r₂, [[12]]), (r₃, [[1]]), (r₄, [[0, 0, 12], [13]])]

theorem sylowH_zero_zero'
    : sylowH m K 0 (0 : K) = 1 := by
  rw [sylowH_zero_left]
  simp only [sylowX_zero, largeReeSigma_zero, mul_one]

theorem sylowL_zero'
    : sylowL m K (0 : K) = 1 := by
  simp only [sylowL, sylowX_zero, largeReeSigma_zero, mul_one]

theorem fam_0_eq
    (c : K) : fam m K 0 c = sylowV m K c 0 0 0 0 0 0 0 0 0 0 0 := by
  show sylowA m K c = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_1_eq
    (c : K) : fam m K 1 c = sylowV m K 0 c 0 0 0 0 0 0 0 0 0 0 := by
  show sylowB m K c 0 = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_2_eq
    (c : K) : fam m K 2 c = sylowV m K 0 0 c 0 0 0 0 0 0 0 0 0 := by
  show sylowB m K 0 c = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_3_eq
    (c : K) : fam m K 3 c = sylowV m K 0 0 0 c 0 0 0 0 0 0 0 0 := by
  show sylowD m K c 0 = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_4_eq
    (c : K) : fam m K 4 c = sylowV m K 0 0 0 0 c 0 0 0 0 0 0 0 := by
  show sylowD m K 0 c = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_5_eq
    (c : K) : fam m K 5 c = sylowV m K 0 0 0 0 0 c 0 0 0 0 0 0 := by
  show sylowF m K c 0 = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_6_eq
    (c : K) : fam m K 6 c = sylowV m K 0 0 0 0 0 0 c 0 0 0 0 0 := by
  show sylowF m K 0 c = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_7_eq
    (c : K) : fam m K 7 c = sylowV m K 0 0 0 0 0 0 0 c 0 0 0 0 := by
  show sylowH m K c 0 = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_8_eq
    (c : K) : fam m K 8 c = sylowV m K 0 0 0 0 0 0 0 0 c 0 0 0 := by
  show sylowH m K 0 c = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_9_eq
    (c : K) : fam m K 9 c = sylowV m K 0 0 0 0 0 0 0 0 0 c 0 0 := by
  show sylowJ m K c = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_10_eq
    (c : K) : fam m K 10 c = sylowV m K 0 0 0 0 0 0 0 0 0 0 c 0 := by
  show sylowK m K c = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

theorem fam_11_eq
    (c : K) : fam m K 11 c = sylowV m K 0 0 0 0 0 0 0 0 0 0 0 c := by
  show sylowL m K c = _
  simp only [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_zero', sylowJ_zero, sylowK_zero, sylowL_zero', one_mul, mul_one]

variable [CharP K F4.prime]

theorem blk_split
    {n₁ n₂ r₁ r₂ r₃ r₄ : ℕ} (hn₁ : n₁ ≤ 11) (hn₂ : n₂ ≤ 11)
    (h : weq fuel (blkWord r₁ r₂ r₃ r₄) (famWord n₁ [[0]] [[12]] ++ famWord n₂ [[1]] [[13]]) =
      true) (b c : K) :
    sylowX K r₁ b * sylowX K r₂ (largeReeSigma m b) * sylowX K r₃ c *
        sylowX K r₄ (largeReeSigma m c + b ^ 2 * largeReeSigma m b) =
      fam m K n₁ b * fam m K n₂ c := by
  have : CharP K 2 := ‹CharP K F4.prime›
  set x := coordVal m b c 0 0 0 0 0 0 0 0 0 0 with hx
  have e := wordEval_eq_of_weq (R := K) h x
  have p0 : polyEval x [[0]] = b := by simp [hx, polyEval, monoEval, coordVal]
  have p1 : polyEval x [[1]] = c := by simp [hx, polyEval, monoEval, coordVal]
  have p12 : polyEval x [[12]] = largeReeSigma m b := by simp [hx, polyEval, monoEval, coordVal]
  have p13 : polyEval x [[13]] = largeReeSigma m c := by simp [hx, polyEval, monoEval, coordVal]
  have p30 : polyEval x [[0, 0, 12], [13]] =
      b * (b * largeReeSigma m b) + largeReeSigma m c := by
    simp [hx, polyEval, monoEval, coordVal]
  rw [wordEval_append, wordEval_famWord (m := m) hn₁ x [[0]] [[12]] (by rw [p0, p12]),
    wordEval_famWord (m := m) hn₂ x [[1]] [[13]] (by rw [p1, p13]), p0, p1] at e
  rw [← e, wordEval_eq_prod_sylowX]
  simp only [blkWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, p0, p1,
    p12, p30]
  rw [show b * (b * largeReeSigma m b) + largeReeSigma m c =
    largeReeSigma m c + b ^ 2 * largeReeSigma m b by ring, mul_assoc, mul_assoc]

theorem sylowB_split
    (b c : K) : sylowB m K b c = fam m K 1 b * fam m K 2 c :=
  blk_split (r₁ := 25) (r₂ := 27) (r₃ := 28) (r₄ := 30) (by norm_num) (by norm_num)
    (by decide +kernel) b c

theorem sylowD_split
    (d e : K) : sylowD m K d e = fam m K 3 d * fam m K 4 e :=
  blk_split (r₁ := 26) (r₂ := 34) (r₃ := 36) (r₄ := 39) (by norm_num) (by norm_num)
    (by decide +kernel) d e

theorem sylowF_split
    (f g : K) : sylowF m K f g = fam m K 5 f * fam m K 6 g :=
  blk_split (r₁ := 29) (r₂ := 37) (r₃ := 43) (r₄ := 46) (by norm_num) (by norm_num)
    (by decide +kernel) f g

theorem sylowH_split
    (h i : K) : sylowH m K h i = fam m K 7 h * fam m K 8 i :=
  blk_split (r₁ := 35) (r₂ := 32) (r₃ := 44) (r₄ := 47) (by norm_num) (by norm_num)
    (by decide +kernel) h i

theorem sylowV_zero_split
    (b c d e f g h i j k l : K) :
    sylowV m K 0 b c d e f g h i j k l = fam m K 1 b * fam m K 2 c * fam m K 3 d * fam m K 4 e *
      fam m K 5 f * fam m K 6 g * fam m K 7 h * fam m K 8 i * fam m K 9 j * fam m K 10 k *
        fam m K 11 l := by
  simp only [sylowV, sylowA_zero, one_mul, sylowB_split, sylowD_split, sylowF_split,
    sylowH_split, mul_assoc]
  rfl

theorem sylowV_one_split
    (a d e f g h i j k l : K) :
    sylowV m K a 0 0 d e f g h i j k l = fam m K 0 a * fam m K 3 d * fam m K 4 e * fam m K 5 f *
      fam m K 6 g * fam m K 7 h * fam m K 8 i * fam m K 9 j * fam m K 10 k * fam m K 11 l := by
  simp only [sylowV, sylowB_zero_zero, mul_one, sylowD_split, sylowF_split, sylowH_split,
    mul_assoc]
  rfl

end Split

section WeylInst

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime]

theorem weylOne_fam_1
    (c : K) : weylOne K * fam m K 1 c * (weylOne K)⁻¹ = fam m K 3 c :=
  weylOne_conj_fam (by decide +kernel) c

theorem weylOne_fam_2
    (c : K) : weylOne K * fam m K 2 c * (weylOne K)⁻¹ = fam m K 4 c :=
  weylOne_conj_fam (by decide +kernel) c

theorem weylOne_fam_5
    (c : K) : weylOne K * fam m K 5 c * (weylOne K)⁻¹ = fam m K 7 c :=
  weylOne_conj_fam (by decide +kernel) c

theorem weylTwo_fam_0
    (c : K) : weylTwo K * fam m K 0 c * (weylTwo K)⁻¹ = fam m K 9 c :=
  weylTwo_conj_fam (by decide +kernel) c

theorem weylTwo_fam_3
    (c : K) : weylTwo K * fam m K 3 c * (weylTwo K)⁻¹ = fam m K 5 c :=
  weylTwo_conj_fam (by decide +kernel) c

theorem weylTwo_fam_4
    (c : K) : weylTwo K * fam m K 4 c * (weylTwo K)⁻¹ = fam m K 6 c :=
  weylTwo_conj_fam (by decide +kernel) c

theorem weylTwo_fam_10
    (c : K) : weylTwo K * fam m K 10 c * (weylTwo K)⁻¹ = fam m K 11 c :=
  weylTwo_conj_fam (by decide +kernel) c

end WeylInst

section Mem

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

theorem sylowV_rest_mem_V1
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (d e f g h i j k l : K) :
    sylowV m K 0 0 0 d e f g h i j k l ∈
      F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ :=
  Subgroup.mem_inf.2 ⟨sylowV_rest_mem_rootSpan_one _ _ _ _ _ _ _ _ _,
    (Subgroup.mem_inf.1 (sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _)).2⟩

theorem fam_mem_U
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {n : ℕ} (hn : n ≤ 11) (c : K) :
    fam m K n c ∈ F4.reeFixedPosUnipotent K m := by
  match n, hn with
  | 0, _ => rw [fam_0_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 1, _ => rw [fam_1_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 2, _ => rw [fam_2_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 3, _ => rw [fam_3_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 4, _ => rw [fam_4_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 5, _ => rw [fam_5_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 6, _ => rw [fam_6_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 7, _ => rw [fam_7_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 8, _ => rw [fam_8_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 9, _ => rw [fam_9_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 10, _ => rw [fam_10_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _
  | 11, _ => rw [fam_11_eq]; exact sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _

theorem fam_mem_V0
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 11)
    (c : K) : fam m K n c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨0, by decide⟩ := by
  match n, h1, h2 with
  | 1, _, _ => rw [fam_1_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 2, _, _ => rw [fam_2_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 3, _, _ => rw [fam_3_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 4, _, _ => rw [fam_4_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 5, _, _ => rw [fam_5_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 6, _, _ => rw [fam_6_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 7, _, _ => rw [fam_7_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 8, _, _ => rw [fam_8_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 9, _, _ => rw [fam_9_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 10, _, _ => rw [fam_10_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _
  | 11, _, _ => rw [fam_11_eq]; exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _

theorem fam_mem_V1
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {n : ℕ} (h : n = 0 ∨ 3 ≤ n) (h2 : n ≤ 11)
    (c : K) : fam m K n c ∈ F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ := by
  match n, h, h2 with
  | 0, _, _ => exact sylowA_mem_complement_one hK c
  | 3, _, _ => rw [fam_3_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _
  | 4, _, _ => rw [fam_4_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _
  | 5, _, _ => rw [fam_5_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _
  | 6, _, _ => rw [fam_6_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _
  | 7, _, _ => rw [fam_7_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _
  | 8, _, _ => rw [fam_8_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _
  | 9, _, _ => rw [fam_9_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _
  | 10, _, _ => rw [fam_10_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _
  | 11, _, _ => rw [fam_11_eq]; exact sylowV_rest_mem_V1 hK _ _ _ _ _ _ _ _ _

end Mem

section High

@[expose] def lowIdx4 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 9, 10, 11]

@[expose] def genCoords : List Poly := coordsOf fuel sylowWord

@[expose] def lowEqs4 : List Poly := lowIdx4.map fun i => genCoords.getD i []

@[expose] def trace4 : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 3), (4, 2), (5, 5), (9, 7)]

theorem genCheck : collectCheck fuel sylowWord genCoords = true := by decide +kernel

theorem trace4_ok : traceZeros lowEqs4 [] trace4 [0, 1, 2, 3, 5, 7] = true := by decide +kernel

@[expose] def highOK (low : List ℕ) (w : Word) : Bool :=
  collectCheck fuel (shiftWord 24 w) (coordsOf fuel (shiftWord 24 w)) &&
    low.all fun i => (coordsOf fuel (shiftWord 24 w)).getD i [] == []

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

omit [Finite K] in
theorem wordEval_sylowWord_of_agree
    (x : ℕ → K) (a b c d e f g h i j k l : K)
    (hx : ∀ n < 24, x n = coordVal m a b c d e f g h i j k l n) :
    wordEval K x sylowWord = sylowV m K a b c d e f g h i j k l := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hv : ∀ f ∈ sylowWord, varsBelow 24 f.2 = true := by decide
  rw [sylowV_eq_wordEval]
  unfold wordEval
  congr 1
  refine List.map_congr_left fun f hf => ?_
  congr 1
  refine polyEval_congr fun mo hmo i hi => hx i ?_
  have := hv f hf
  simp only [varsBelow, List.all_eq_true, Nat.blt_eq] at this
  exact this mo hmo i hi

theorem high4_of_word
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {y : ModGL F4.tag K}
    (hy : y ∈ F4.reeFixedPosUnipotent K m) {w : Word} {x : ℕ → K} (hyw : y = wordEval K x w)
    (hchk : highOK lowIdx4 w = true) :
    ∃ e g i j k l : K, y = sylowV m K 0 0 0 0 e 0 g 0 i j k l := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨v, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hy
  set z : ℕ → K := fun n => if n < 24 then coordVal m (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
    (v 7) (v 8) (v 9) (v 10) (v 11) n else x (n - 24) with hz
  have hz24 : ∀ n < 24, z n = coordVal m (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)
      (v 9) (v 10) (v 11) n := fun n hn => by simp [hz, hn]
  have hz1 : wordEval K z sylowWord = sylowVec m K v :=
    wordEval_sylowWord_of_agree z _ _ _ _ _ _ _ _ _ _ _ _ hz24
  have hz2 : wordEval K z (shiftWord 24 w) = wordEval K x w := by
    rw [wordEval_shiftWord]
    congr 1
  have heq : wordEval K z sylowWord = wordEval K z (shiftWord 24 w) := by
    rw [hz1, hz2, ← hyw]
  simp only [highOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hchk
  obtain ⟨hcc, hlow⟩ := hchk
  have hvan : ∀ p ∈ lowEqs4, polyEval z p = 0 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    have hi24 : i < 24 := by
      simp only [lowIdx4, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    have h1 : polyEval z (polyAdd (genCoords.getD i [])
        ((coordsOf fuel (shiftWord 24 w)).getD i [])) = 0 :=
      eqs_of_wordEval_eq genCheck hcc heq i hi24
    rw [polyEval_polyAdd, hlow i hi] at h1
    simpa [polyEval] using h1
  have hz12 : ∀ i < 12, z (i + 12) = largeReeSigma m (z i) := by
    intro i hi
    rw [hz24 (i + 12) (by omega), hz24 i (by omega)]
    exact coordVal_add_twelve (m := m) _ _ _ _ _ _ _ _ _ _ _ _ i hi
  have hzero := traceZeros_sound z hz12 lowEqs4 hvan (zs₀ := []) (by simp) trace4_ok
  have h0 : v 0 = 0 := by simpa [hz24 0 (by norm_num), coordVal] using hzero 0 (by decide)
  have h1 : v 1 = 0 := by simpa [hz24 1 (by norm_num), coordVal] using hzero 1 (by decide)
  have h2 : v 2 = 0 := by simpa [hz24 2 (by norm_num), coordVal] using hzero 2 (by decide)
  have h3 : v 3 = 0 := by simpa [hz24 3 (by norm_num), coordVal] using hzero 3 (by decide)
  have h5 : v 5 = 0 := by simpa [hz24 5 (by norm_num), coordVal] using hzero 5 (by decide)
  have h7 : v 7 = 0 := by simpa [hz24 7 (by norm_num), coordVal] using hzero 7 (by decide)
  exact ⟨v 4, v 6, v 8, v 9, v 10, v 11, by simp only [sylowVec, h0, h1, h2, h3, h5, h7]⟩

end High

section Tail

@[expose] def commW (w₁ w₂ : Word) : Word := w₁ ++ w₂ ++ w₁.reverse ++ w₂.reverse

@[expose] def wordT1 : Word :=
  (famProdWord [(3, [[0, 1]]), (7, [[0, 12, 13]])]).reverse ++
    commW (famWord 1 [[0]] (sigmaPoly [[0]])) (famWord 0 [[1]] (sigmaPoly [[1]]))

@[expose] def wordT2 : Word :=
  (famProdWord [(5, [[0, 1]]), (7, [[0, 13]])]).reverse ++
    commW (famWord 2 [[0]] (sigmaPoly [[0]])) (famWord 0 [[1]] (sigmaPoly [[1]]))

theorem highOK_T1 : highOK lowIdx4 wordT1 = true := by decide +kernel

theorem highOK_T2 : highOK lowIdx4 wordT2 = true := by decide +kernel

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime] [Finite K]

omit [Finite K] in
theorem wordEval_commW
    (x : ℕ → K) (w₁ w₂ : Word) :
    wordEval K x (commW w₁ w₂) = ⁅wordEval K x w₁, wordEval K x w₂⁆ := by
  have : CharP K 2 := ‹CharP K F4.prime›
  simp only [commW, wordEval_append, wordEval_reverse, commutatorElement_def, mul_assoc]

theorem rel_T1
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    ∃ e g i j k l : K, ⁅fam m K 1 s, fam m K 0 t⁆ =
      fam m K 3 (s * t) * fam m K 7 (s * largeReeSigma m s * largeReeSigma m t) *
        sylowV m K 0 0 0 0 e 0 g 0 i j k l := by
  have : CharP K 2 := ‹CharP K F4.prime›
  set x := coordVal m s t 0 0 0 0 0 0 0 0 0 0 with hx
  have hx12 : ∀ n < 12, x (n + 12) = largeReeSigma m (x n) :=
    coordVal_add_twelve (m := m) s t 0 0 0 0 0 0 0 0 0 0
  have p0 : polyEval x [[0]] = s := by simp [hx, polyEval, monoEval, coordVal]
  have p1 : polyEval x [[1]] = t := by simp [hx, polyEval, monoEval, coordVal]
  have hl : ∀ e ∈ [(3, ([[0, 1]] : Poly)), (7, [[0, 12, 13]])],
      e.1 ≤ 11 ∧ varsBelow 24 e.2 = true := by decide
  have hprod := wordEval_famProdWord hK x hx12 _ hl
  have hs : ∀ p : Poly, varsBelow 24 p = true →
      polyEval x (sigmaPoly p) = largeReeSigma m (polyEval x p) := fun p hp =>
    polyEval_sigmaPoly hK x hx12 hp
  have hlead : (([(3, ([[0, 1]] : Poly)), (7, [[0, 12, 13]])].map fun e =>
      fam m K e.1 (polyEval x e.2)).prod) =
      fam m K 3 (s * t) * fam m K 7 (s * largeReeSigma m s * largeReeSigma m t) := by
    simp [polyEval, monoEval, hx, coordVal, mul_assoc]
  have hval : wordEval K x wordT1 =
      (fam m K 3 (s * t) * fam m K 7 (s * largeReeSigma m s * largeReeSigma m t))⁻¹ *
        ⁅fam m K 1 s, fam m K 0 t⁆ := by
    unfold wordT1
    rw [wordEval_append, wordEval_reverse, hprod, hlead, wordEval_commW,
      wordEval_famWord (m := m) (by norm_num) x [[0]] _ (hs [[0]] (by decide)),
      wordEval_famWord (m := m) (by norm_num) x [[1]] _ (hs [[1]] (by decide)), p0, p1]
  have hmem : (fam m K 3 (s * t) * fam m K 7 (s * largeReeSigma m s * largeReeSigma m t))⁻¹ *
      ⁅fam m K 1 s, fam m K 0 t⁆ ∈ F4.reeFixedPosUnipotent K m := by
    refine mul_mem (inv_mem (mul_mem (fam_mem_U hK (by norm_num) _) (fam_mem_U hK (by norm_num) _)))
      ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (fam_mem_U hK (by norm_num) _) (fam_mem_U hK (by norm_num) _))
      (inv_mem (fam_mem_U hK (by norm_num) _))) (inv_mem (fam_mem_U hK (by norm_num) _))
  obtain ⟨e, g, i, j, k, l, h⟩ := high4_of_word hK hmem hval.symm highOK_T1
  exact ⟨e, g, i, j, k, l, by rw [← h]; group⟩

theorem rel_T2
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s t : K) :
    ∃ e g i j k l : K, ⁅fam m K 2 s, fam m K 0 t⁆ =
      fam m K 5 (s * t) * fam m K 7 (s * largeReeSigma m t) *
        sylowV m K 0 0 0 0 e 0 g 0 i j k l := by
  have : CharP K 2 := ‹CharP K F4.prime›
  set x := coordVal m s t 0 0 0 0 0 0 0 0 0 0 with hx
  have hx12 : ∀ n < 12, x (n + 12) = largeReeSigma m (x n) :=
    coordVal_add_twelve (m := m) s t 0 0 0 0 0 0 0 0 0 0
  have p0 : polyEval x [[0]] = s := by simp [hx, polyEval, monoEval, coordVal]
  have p1 : polyEval x [[1]] = t := by simp [hx, polyEval, monoEval, coordVal]
  have hl : ∀ e ∈ [(5, ([[0, 1]] : Poly)), (7, [[0, 13]])],
      e.1 ≤ 11 ∧ varsBelow 24 e.2 = true := by decide
  have hprod := wordEval_famProdWord hK x hx12 _ hl
  have hs : ∀ p : Poly, varsBelow 24 p = true →
      polyEval x (sigmaPoly p) = largeReeSigma m (polyEval x p) := fun p hp =>
    polyEval_sigmaPoly hK x hx12 hp
  have hlead : (([(5, ([[0, 1]] : Poly)), (7, [[0, 13]])].map fun e =>
      fam m K e.1 (polyEval x e.2)).prod) =
      fam m K 5 (s * t) * fam m K 7 (s * largeReeSigma m t) := by
    simp [polyEval, monoEval, hx, coordVal]
  have hval : wordEval K x wordT2 =
      (fam m K 5 (s * t) * fam m K 7 (s * largeReeSigma m t))⁻¹ *
        ⁅fam m K 2 s, fam m K 0 t⁆ := by
    unfold wordT2
    rw [wordEval_append, wordEval_reverse, hprod, hlead, wordEval_commW,
      wordEval_famWord (m := m) (by norm_num) x [[0]] _ (hs [[0]] (by decide)),
      wordEval_famWord (m := m) (by norm_num) x [[1]] _ (hs [[1]] (by decide)), p0, p1]
  have hmem : (fam m K 5 (s * t) * fam m K 7 (s * largeReeSigma m t))⁻¹ *
      ⁅fam m K 2 s, fam m K 0 t⁆ ∈ F4.reeFixedPosUnipotent K m := by
    refine mul_mem (inv_mem (mul_mem (fam_mem_U hK (by norm_num) _) (fam_mem_U hK (by norm_num) _)))
      ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (fam_mem_U hK (by norm_num) _) (fam_mem_U hK (by norm_num) _))
      (inv_mem (fam_mem_U hK (by norm_num) _))) (inv_mem (fam_mem_U hK (by norm_num) _))
  obtain ⟨e, g, i, j, k, l, h⟩ := high4_of_word hK hmem hval.symm highOK_T2
  exact ⟨e, g, i, j, k, l, by rw [← h]; group⟩

end Tail

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4
