module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ModelBridge
public import CFSG.Open.StatedDefs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Matrix

section Abstract

variable {ι K : Type} [Fintype ι] [Field K] {Q : (ι → K) → K} {M : Matrix ι ι K}

structure IsQuadWith (Q : (ι → K) → K) (M : Matrix ι ι K) : Prop where
  add : ∀ x y, Q (x + y) = Q x + Q y + x ⬝ᵥ (M *ᵥ y)
  smul : ∀ (s : K) x, Q (s • x) = s ^ 2 * Q x

theorem two_eq_zero_K [CharP K 2] : (2 : K) = 0 := CharP.cast_eq_zero K 2

theorem IsQuadWith.zero (h : IsQuadWith Q M) : Q 0 = 0 := by
  simpa using h.smul 0 0

theorem IsQuadWith.self [CharP K 2] (h : IsQuadWith Q M) (x : ι → K) : x ⬝ᵥ (M *ᵥ x) = 0 := by
  have h1 := h.add x x
  have h2 : x + x = 0 := by
    have : (2 : K) • x = 0 := by rw [two_eq_zero_K, zero_smul]
    rw [two_smul] at this; exact this
  rw [h2, h.zero] at h1
  linear_combination -h1 - Q x * two_eq_zero_K (K := K)

theorem IsQuadWith.symm (h : IsQuadWith Q M) (x y : ι → K) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  have h1 := h.add x y
  have h2 := h.add y x
  rw [add_comm y x] at h2
  linear_combination h2 - h1

@[expose] def transvFun (M : Matrix ι ι K) (a x : ι → K) : ι → K :=
  x + (x ⬝ᵥ (M *ᵥ a)) • a

theorem transvFun_dot (M : Matrix ι ι K) (a x y : ι → K) :
    transvFun M a x ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ (M *ᵥ y) + (x ⬝ᵥ (M *ᵥ a)) * (a ⬝ᵥ (M *ᵥ y)) := by
  simp [transvFun, add_dotProduct, smul_dotProduct]

theorem transvFun_transvFun [CharP K 2] (h : IsQuadWith Q M) (a x : ι → K) :
    transvFun M a (transvFun M a x) = x := by
  have h1 : (x + (x ⬝ᵥ (M *ᵥ a)) • a) ⬝ᵥ (M *ᵥ a) = x ⬝ᵥ (M *ᵥ a) := by
    simp [add_dotProduct, smul_dotProduct, h.self]
  have h2 : (2 : K) • ((x ⬝ᵥ (M *ᵥ a)) • a) = 0 := by rw [two_eq_zero_K, zero_smul]
  rw [two_smul] at h2
  show (x + (x ⬝ᵥ (M *ᵥ a)) • a) + ((x + (x ⬝ᵥ (M *ᵥ a)) • a) ⬝ᵥ (M *ᵥ a)) • a = x
  rw [h1, add_assoc, h2, add_zero]

theorem Q_transvFun [CharP K 2] (h : IsQuadWith Q M) {a : ι → K} (ha : Q a = 1) (x : ι → K) :
    Q (transvFun M a x) = Q x := by
  have := h.add x ((x ⬝ᵥ (M *ᵥ a)) • a)
  rw [transvFun, this, h.smul, ha, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 := two_eq_zero_K (K := K)
  linear_combination (x ⬝ᵥ (M *ᵥ a)) * (x ⬝ᵥ (M *ᵥ a)) * h2

theorem transvMat_mulVec [DecidableEq ι] (M : Matrix ι ι K) (a x : ι → K) :
    ((1 : Matrix ι ι K) + vecMulVec a (M *ᵥ a)) *ᵥ x = transvFun M a x := by
  simp [transvFun, add_mulVec, vecMulVec_mulVec, dotProduct_comm]

theorem exists_transv [DecidableEq ι] [CharP K 2] (h : IsQuadWith Q M) (a : ι → K) :
    ∃ g : GL ι K, (∀ x, (g : Matrix ι ι K) *ᵥ x = transvFun M a x) ∧ g * g = 1 := by
  have hT : ((1 : Matrix ι ι K) + vecMulVec a (M *ᵥ a)) * (1 + vecMulVec a (M *ᵥ a)) = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← mulVec_mulVec, transvMat_mulVec, transvMat_mulVec, transvFun_transvFun h,
      one_mulVec]
  exact ⟨⟨_, _, hT, hT⟩, fun x => transvMat_mulVec M a x, Units.ext hT⟩

theorem transvFun_braid [CharP K 2] (h : IsQuadWith Q M) {a b : ι → K}
    (hab : a ⬝ᵥ (M *ᵥ b) = 1) (x : ι → K) :
    transvFun M a (transvFun M b (transvFun M a x)) =
      transvFun M b (transvFun M a (transvFun M b x)) := by
  have hba : b ⬝ᵥ (M *ᵥ a) = 1 := (h.symm b a).trans hab
  have e1 : transvFun M a (transvFun M b (transvFun M a x)) =
      x + ((x ⬝ᵥ (M *ᵥ a)) + (x ⬝ᵥ (M *ᵥ b))) • a + ((x ⬝ᵥ (M *ᵥ a)) + (x ⬝ᵥ (M *ᵥ b))) • b := by
    simp only [transvFun, add_dotProduct, smul_dotProduct, smul_eq_mul, hab, hba, h.self,
      mul_one, mul_zero, add_zero]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((x ⬝ᵥ (M *ᵥ a)) * a i) * two_eq_zero_K (K := K)
  have e2 : transvFun M b (transvFun M a (transvFun M b x)) =
      x + ((x ⬝ᵥ (M *ᵥ a)) + (x ⬝ᵥ (M *ᵥ b))) • a + ((x ⬝ᵥ (M *ᵥ a)) + (x ⬝ᵥ (M *ᵥ b))) • b := by
    simp only [transvFun, add_dotProduct, smul_dotProduct, smul_eq_mul, hab, hba, h.self,
      mul_one, mul_zero, add_zero]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((x ⬝ᵥ (M *ᵥ b)) * b i) * two_eq_zero_K (K := K)
  rw [e1, e2]

theorem exists_mem_statedOmega_orderOf_three [DecidableEq ι] [CharP K 2] (h : IsQuadWith Q M)
    {a b v : ι → K} (ha : Q a = 1) (hb : Q b = 1) (hab : a ⬝ᵥ (M *ᵥ b) = 1)
    (hva : v ⬝ᵥ (M *ᵥ a) = 0) (hvb : v ⬝ᵥ (M *ᵥ b) = 0) :
    ∃ g ∈ CFSG.Open.StatedOmega Q, orderOf g = 3 ∧ (g : Matrix ι ι K) *ᵥ v = v := by
  obtain ⟨s, hs, hss⟩ := exists_transv h a
  obtain ⟨t, ht, htt⟩ := exists_transv h b
  have hsI : s ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    Subgroup.subset_closure fun x => by rw [hs]; exact Q_transvFun h ha x
  have htI : t ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    Subgroup.subset_closure fun x => by rw [ht]; exact Q_transvFun h hb x
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hbraid : s * t * s = t * s * t := Units.ext (Matrix.ext_iff_mulVec.mpr fun x => by
    simp only [Units.val_mul, ← mulVec_mulVec, hs, ht]
    exact transvFun_braid h hab x)
  have hg3 : (s * t) ^ 3 = 1 := by
    calc (s * t) ^ 3 = (s * t * s) * (t * s * t) := by simp [pow_succ, mul_assoc]
      _ = (s * t * s) * (s * t * s) := by rw [hbraid]
      _ = s * t * (s * s) * t * s := by group
      _ = 1 := by rw [hss, mul_one, mul_assoc s t t, htt, mul_one, hss]
  have hgv : (↑(s * t) : Matrix ι ι K) *ᵥ v = v := by
    rw [Units.val_mul, ← mulVec_mulVec, ht, hs]
    have h1 : transvFun M b v = v := by simp [transvFun, hvb]
    have h2 : transvFun M a v = v := by simp [transvFun, hva]
    rw [h1, h2]
  have hg1 : s * t ≠ 1 := by
    intro h1
    have h2 : (↑(s * t) : Matrix ι ι K) *ᵥ b = b := by rw [h1]; simp
    rw [Units.val_mul, ← mulVec_mulVec, ht, hs] at h2
    have h3 : transvFun M b b = b := by simp [transvFun, h.self]
    have h4 : transvFun M a b = b + a := by
      simp [transvFun, (h.symm b a).trans hab, add_comm]
    rw [h3, h4] at h2
    have h5 : a = 0 := by simpa using h2
    rw [h5, h.zero] at ha
    exact zero_ne_one ha
  refine ⟨s * t, ?_, orderOf_eq_prime hg3 hg1, hgv⟩
  have hc : (s * t) ^ 2 ∈ CFSG.Open.StatedOmega Q := by
    have := Subgroup.commutator_mem_commutator hsI htI
    rw [commutatorElement_def, hs1, ht1] at this
    rw [pow_two]
    unfold CFSG.Open.StatedOmega
    simpa [mul_assoc] using this
  have h4 : s * t = ((s * t) ^ 2) ^ 2 := by
    rw [← pow_mul]; simp [pow_succ, hg3]
  rw [h4]
  exact pow_mem hc 2

theorem exists_pair_of_singular [CharP K 2] (h : IsQuadWith Q M) {a₀ b₀ w v : ι → K}
    (ha₀ : Q a₀ = 1) (hb₀ : Q b₀ = 1) (hab₀ : a₀ ⬝ᵥ (M *ᵥ b₀) = 1)
    (hwa : w ⬝ᵥ (M *ᵥ a₀) = 0) (hwb : w ⬝ᵥ (M *ᵥ b₀) = 0) (hQw : Q w = 0)
    (hvw : v ⬝ᵥ (M *ᵥ w) ≠ 0) :
    ∃ a b : ι → K, Q a = 1 ∧ Q b = 1 ∧ a ⬝ᵥ (M *ᵥ b) = 1 ∧
      v ⬝ᵥ (M *ᵥ a) = 0 ∧ v ⬝ᵥ (M *ᵥ b) = 0 := by
  have hwa' : a₀ ⬝ᵥ (M *ᵥ w) = 0 := (h.symm a₀ w).trans hwa
  have hwb' : b₀ ⬝ᵥ (M *ᵥ w) = 0 := (h.symm b₀ w).trans hwb
  have h2 := two_eq_zero_K (K := K)
  set μ := (v ⬝ᵥ (M *ᵥ a₀)) / (v ⬝ᵥ (M *ᵥ w)) with hμ
  set μ' := (v ⬝ᵥ (M *ᵥ b₀)) / (v ⬝ᵥ (M *ᵥ w)) with hμ'
  have hμw : μ * (v ⬝ᵥ (M *ᵥ w)) = v ⬝ᵥ (M *ᵥ a₀) := div_mul_cancel₀ _ hvw
  have hμw' : μ' * (v ⬝ᵥ (M *ᵥ w)) = v ⬝ᵥ (M *ᵥ b₀) := div_mul_cancel₀ _ hvw
  refine ⟨a₀ + μ • w, b₀ + μ' • w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.add, h.smul, ha₀, hQw, Matrix.mulVec_smul, dotProduct_smul, hwa', smul_eq_mul]; ring
  · rw [h.add, h.smul, hb₀, hQw, Matrix.mulVec_smul, dotProduct_smul, hwb', smul_eq_mul]; ring
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hab₀, hwa', hwb, h.self]
    ring
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
    linear_combination (v ⬝ᵥ (M *ᵥ a₀)) * h2 + hμw
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
    linear_combination (v ⬝ᵥ (M *ᵥ b₀)) * h2 + hμw'

end Abstract

section Plus

variable {K : Type} [Field K] {n : ℕ}

@[expose] def plusM (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 1 0

theorem plusM_mulVec (y : Fin n ⊕ Fin n → K) : plusM n K *ᵥ y = y ∘ Sum.swap := by
  funext r
  rcases r with i | i <;>
    simp [plusM, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

theorem dot_plusM (x y : Fin n ⊕ Fin n → K) :
    x ⬝ᵥ (plusM n K *ᵥ y) = ∑ i, (x (.inl i) * y (.inr i) + x (.inr i) * y (.inl i)) := by
  simp [plusM_mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem isQuadWith_plus : IsQuadWith (CFSG.Open.StatedQuadPlus n K) (plusM n K) where
  add x y := by
    simp only [CFSG.Open.StatedQuadPlus, dot_plusM, ← Finset.sum_add_distrib, Pi.add_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  smul s x := by
    simp only [CFSG.Open.StatedQuadPlus, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[expose] def plusA (i : Fin n) : Fin n ⊕ Fin n → K := Pi.single (.inl i) 1 + Pi.single (.inr i) 1

@[expose] def plusB (i j : Fin n) : Fin n ⊕ Fin n → K :=
  Pi.single (.inl i) 1 + Pi.single (.inl j) 1 + Pi.single (.inr j) 1

theorem Q_plusA (i : Fin n) : CFSG.Open.StatedQuadPlus n K (plusA i) = 1 := by
  simp [CFSG.Open.StatedQuadPlus, plusA, Pi.single_apply]

theorem sum_two_aux {i j : Fin n} (hij : i ≠ j) :
    ∑ x : Fin n, ((if x = j then if x = i then (1 : K) else 0 else 0) +
      if x = i then (if x = i then 1 else 0) + if x = j then 1 else 0 else 0) = 1 := by
  have h : ∀ x : Fin n, ((if x = j then if x = i then (1 : K) else 0 else 0) +
      if x = i then (if x = i then 1 else 0) + if x = j then 1 else 0 else 0) =
        if x = i then 1 else 0 := by
    intro x
    by_cases h1 : x = i
    · subst h1; simp [hij]
    · by_cases h2 : x = j <;> simp [h1, h2, hij.symm]
  simp [h]

theorem Q_plusB {i j : Fin n} (hij : i ≠ j) : CFSG.Open.StatedQuadPlus n K (plusB i j) = 1 := by
  simp [CFSG.Open.StatedQuadPlus, plusB, Pi.single_apply, hij.symm]

theorem B_plus {i j : Fin n} (hij : i ≠ j) :
    plusA i ⬝ᵥ (plusM n K *ᵥ plusB i j) = 1 := by
  rw [dot_plusM]
  simp [plusA, plusB, Pi.single_apply]
  exact sum_two_aux (K := K) hij

theorem Q_single (s : Fin n ⊕ Fin n) : CFSG.Open.StatedQuadPlus n K (Pi.single s 1) = 0 := by
  rcases s with i | i <;>
    simp [CFSG.Open.StatedQuadPlus, Pi.single_apply]

@[expose] def plusIdx (r : Fin n ⊕ Fin n) : Fin n := Sum.elim id id r

theorem plusA_apply_eq_zero {i : Fin n} {r : Fin n ⊕ Fin n} (h : plusIdx r ≠ i) :
    (plusA i : Fin n ⊕ Fin n → K) r = 0 := by
  rcases r with c | c <;> simp_all [plusIdx, plusA]

theorem plusB_apply_eq_zero {i j : Fin n} {r : Fin n ⊕ Fin n} (h : plusIdx r ≠ i)
    (h' : plusIdx r ≠ j) : (plusB i j : Fin n ⊕ Fin n → K) r = 0 := by
  rcases r with c | c <;> simp_all [plusIdx, plusB]

theorem single_dot_plusM (r : Fin n ⊕ Fin n) (y : Fin n ⊕ Fin n → K) :
    (Pi.single r 1 : Fin n ⊕ Fin n → K) ⬝ᵥ (plusM n K *ᵥ y) = y (Sum.swap r) := by
  simp [plusM_mulVec]

theorem dot_plusM_single (r : Fin n ⊕ Fin n) (v : Fin n ⊕ Fin n → K) :
    v ⬝ᵥ (plusM n K *ᵥ Pi.single (Sum.swap r) 1) = v r := by
  have : (Pi.single (Sum.swap r) 1 : Fin n ⊕ Fin n → K) ∘ Sum.swap = Pi.single r 1 := by
    funext s
    rcases s with a | a <;> rcases r with b | b <;> simp [Pi.single_apply]
  rw [plusM_mulVec, this]
  simp

theorem exists_three_distinct (hn : 3 ≤ n) (c : Fin n) : ∃ i j : Fin n, i ≠ c ∧ j ≠ c ∧ i ≠ j := by
  have hcard : 1 < (Finset.univ.erase c).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c)]; simp only [Finset.card_univ]
    simp; omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  exact ⟨i, j, Finset.ne_of_mem_erase hi, Finset.ne_of_mem_erase hj, hij⟩

theorem exists_pair_plus (hn : 3 ≤ n) [CharP K 2] (v : Fin n ⊕ Fin n → K) :
    ∃ a b : Fin n ⊕ Fin n → K, CFSG.Open.StatedQuadPlus n K a = 1 ∧
      CFSG.Open.StatedQuadPlus n K b = 1 ∧ a ⬝ᵥ (plusM n K *ᵥ b) = 1 ∧
      v ⬝ᵥ (plusM n K *ᵥ a) = 0 ∧ v ⬝ᵥ (plusM n K *ᵥ b) = 0 := by
  by_cases hv : v = 0
  · obtain ⟨i, j, -, -, hij⟩ := exists_three_distinct hn (⟨0, by omega⟩ : Fin n)
    exact ⟨plusA i, plusB i j, Q_plusA i, Q_plusB hij, B_plus hij, by simp [hv], by simp [hv]⟩
  · obtain ⟨r, hr⟩ := Function.ne_iff.mp hv
    obtain ⟨i, j, hi, hj, hij⟩ := exists_three_distinct hn (plusIdx r)
    refine exists_pair_of_singular isQuadWith_plus (Q_plusA i) (Q_plusB hij) (B_plus hij)
      (w := Pi.single (Sum.swap r) 1) ?_ ?_ (Q_single _) ?_
    · rw [single_dot_plusM, Sum.swap_swap]
      exact plusA_apply_eq_zero hi.symm
    · rw [single_dot_plusM, Sum.swap_swap]
      exact plusB_apply_eq_zero hi.symm hj.symm
    · rw [dot_plusM_single]; exact hr

theorem threeFixedModel_statedOmegaPlus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) :
    ThreeFixedModel (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n K))
      (Fin n ⊕ Fin n → K) := by
  intro v
  obtain ⟨a, b, ha, hb, hab, hva, hvb⟩ := exists_pair_plus hn v
  obtain ⟨g, hg, hg3, hgv⟩ := exists_mem_statedOmega_orderOf_three isQuadWith_plus ha hb hab hva hvb
  exact ⟨⟨g, hg⟩, by rw [Subgroup.orderOf_mk]; exact hg3, hgv⟩

end Plus

section Minus

variable {K : Type} [Field K] {n : ℕ}

@[expose] def minusM (n : ℕ) (K : Type) [Field K] (b : K) :
    Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K :=
  Matrix.of fun r s =>
    Sum.elim (fun i => Sum.elim (fun _ => (0 : K)) (Sum.elim (fun j => if i = j then 1 else 0)
        (fun _ => 0)) s)
      (Sum.elim (fun i => Sum.elim (fun j => if i = j then (1 : K) else 0) (fun _ => 0) s)
        (fun u => Sum.elim (fun _ => (0 : K)) (Sum.elim (fun _ => 0)
          (fun t => if u = t then 0 else b)) s)) r

@[expose] def minusEmb (n : ℕ) : Fin (n - 1) ⊕ Fin (n - 1) → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 :=
  Sum.elim .inl (fun i => .inr (.inl i))

theorem minusM_mulVec_emb (b : K) (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (r : Fin (n - 1) ⊕ Fin (n - 1)) :
    (minusM n K b *ᵥ y) (minusEmb n (Sum.swap r)) = y (minusEmb n r) := by
  rcases r with i | i <;>
    simp [minusM, minusEmb, mulVec, dotProduct, Fintype.sum_sum_type]

theorem minusM_mulVec_zero (b : K) (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    (minusM n K b *ᵥ y) (.inr (.inr 0)) = b * y (.inr (.inr 1)) := by
  simp [minusM, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem minusM_mulVec_one (b : K) (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    (minusM n K b *ᵥ y) (.inr (.inr 1)) = b * y (.inr (.inr 0)) := by
  simp [minusM, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem dot_minusM (b : K) (x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    x ⬝ᵥ (minusM n K b *ᵥ y) =
      ∑ i, (x (.inl i) * y (.inr (.inl i)) + x (.inr (.inl i)) * y (.inl i)) +
        b * (x (.inr (.inr 0)) * y (.inr (.inr 1)) + x (.inr (.inr 1)) * y (.inr (.inr 0))) := by
  have h1 : ∀ i, (minusM n K b *ᵥ y) (.inl i) = y (.inr (.inl i)) := fun i => by
    simpa [minusEmb] using minusM_mulVec_emb b y (Sum.inr i)
  have h2 : ∀ i, (minusM n K b *ᵥ y) (.inr (.inl i)) = y (.inl i) := fun i => by
    simpa [minusEmb] using minusM_mulVec_emb b y (Sum.inl i)
  simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2, minusM_mulVec_zero,
    minusM_mulVec_one, Finset.sum_add_distrib]
  ring

theorem isQuadWith_minus [CharP K 2] (b c : K) :
    IsQuadWith (CFSG.Open.StatedQuadMinus n K b c) (minusM n K b) where
  add x y := by
    rw [dot_minusM]
    have e : ∑ i, ((x (.inl i) + y (.inl i)) * (x (.inr (.inl i)) + y (.inr (.inl i)))) =
        ∑ i, x (.inl i) * x (.inr (.inl i)) + ∑ i, y (.inl i) * y (.inr (.inl i)) +
          ∑ i, (x (.inl i) * y (.inr (.inl i)) + x (.inr (.inl i)) * y (.inl i)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [CFSG.Open.StatedQuadMinus, Pi.add_apply, e]
    linear_combination (x (.inr (.inr 0)) * y (.inr (.inr 0)) +
      c * (x (.inr (.inr 1)) * y (.inr (.inr 1)))) * two_eq_zero_K (K := K)
  smul s x := by
    have e : ∑ i, (s • x) (.inl i) * (s • x) (.inr (.inl i)) =
        s ^ 2 * ∑ i, x (.inl i) * x (.inr (.inl i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    unfold CFSG.Open.StatedQuadMinus
    rw [e]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

@[expose] def minusA (n : ℕ) (K : Type) [Field K] (i : Fin (n - 1)) :
    Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  Pi.single (.inl i) 1 + Pi.single (.inr (.inl i)) 1

@[expose] def minusB (n : ℕ) (K : Type) [Field K] (i j : Fin (n - 1)) :
    Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  Pi.single (.inl i) 1 + Pi.single (.inl j) 1 + Pi.single (.inr (.inl j)) 1

@[expose] def minusC (n : ℕ) (K : Type) [Field K] (i : Fin (n - 1)) :
    Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  Pi.single (.inl i) 1 + Pi.single (.inr (.inr 0)) 1

theorem Q_minusA (b c : K) (i : Fin (n - 1)) :
    CFSG.Open.StatedQuadMinus n K b c (minusA n K i) = 1 := by
  simp [CFSG.Open.StatedQuadMinus, minusA, Pi.single_apply]

theorem Q_minusB (b c : K) {i j : Fin (n - 1)} (hij : i ≠ j) :
    CFSG.Open.StatedQuadMinus n K b c (minusB n K i j) = 1 := by
  simp [CFSG.Open.StatedQuadMinus, minusB, Pi.single_apply, hij.symm]

theorem Q_minusC (b c : K) (i : Fin (n - 1)) :
    CFSG.Open.StatedQuadMinus n K b c (minusC n K i) = 1 := by
  simp [CFSG.Open.StatedQuadMinus, minusC, Pi.single_apply]

theorem B_minusB (b : K) {i j : Fin (n - 1)} (hij : i ≠ j) :
    minusA n K i ⬝ᵥ (minusM n K b *ᵥ minusB n K i j) = 1 := by
  rw [dot_minusM]
  simp [minusA, minusB, Pi.single_apply]
  exact sum_two_aux (n := n - 1) (K := K) hij

theorem B_minusC (b : K) (i : Fin (n - 1)) :
    minusA n K i ⬝ᵥ (minusM n K b *ᵥ minusC n K i) = 1 := by
  rw [dot_minusM]
  simp [minusA, minusC, Pi.single_apply]

theorem Q_minusSingle (b c : K) (r : Fin (n - 1) ⊕ Fin (n - 1)) :
    CFSG.Open.StatedQuadMinus n K b c (Pi.single (minusEmb n r) 1) = 0 := by
  rcases r with i | i <;>
    simp [CFSG.Open.StatedQuadMinus, minusEmb, Pi.single_apply]

@[expose] def minusIdx (r : Fin (n - 1) ⊕ Fin (n - 1)) : Fin (n - 1) := Sum.elim id id r

theorem minusA_apply_eq_zero {i : Fin (n - 1)} {r : Fin (n - 1) ⊕ Fin (n - 1)}
    (h : minusIdx r ≠ i) : (minusA n K i) (minusEmb n r) = 0 := by
  rcases r with c | c <;> simp_all [minusIdx, minusEmb, minusA]

theorem minusC_apply_eq_zero {i : Fin (n - 1)} {r : Fin (n - 1) ⊕ Fin (n - 1)}
    (h : minusIdx r ≠ i) : (minusC n K i) (minusEmb n r) = 0 := by
  rcases r with c | c <;> simp_all [minusIdx, minusEmb, minusC]

theorem exists_pair_minus [CharP K 2] (hn : 3 ≤ n) (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    ∃ a a' : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      CFSG.Open.StatedQuadMinus n K b c a = 1 ∧ CFSG.Open.StatedQuadMinus n K b c a' = 1 ∧
      a ⬝ᵥ (minusM n K b *ᵥ a') = 1 ∧
      v ⬝ᵥ (minusM n K b *ᵥ a) = 0 ∧ v ⬝ᵥ (minusM n K b *ᵥ a') = 0 := by
  have hnt : Nontrivial (Fin (n - 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  by_cases hex : ∃ r : Fin (n - 1) ⊕ Fin (n - 1), v (minusEmb n r) ≠ 0
  · obtain ⟨r, hr⟩ := hex
    obtain ⟨i, hi⟩ := exists_ne (minusIdx r)
    refine exists_pair_of_singular (isQuadWith_minus b c) (Q_minusA b c i) (Q_minusC b c i)
      (B_minusC b i) (w := Pi.single (minusEmb n (Sum.swap r)) 1) ?_ ?_
      (by simpa using Q_minusSingle b c (Sum.swap r)) ?_
    · simp only [single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact minusA_apply_eq_zero hi.symm
    · simp only [single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact minusC_apply_eq_zero hi.symm
    · rw [(isQuadWith_minus (n := n) b c).symm]
      simp only [single_dotProduct, one_mul]
      rw [minusM_mulVec_emb]
      exact hr
  · simp only [not_exists, not_not] at hex
    have hl : ∀ i, v (.inl i) = 0 := fun i => by simpa [minusEmb] using hex (Sum.inl i)
    have hr : ∀ i, v (.inr (.inl i)) = 0 := fun i => by simpa [minusEmb] using hex (Sum.inr i)
    have h0 : 0 < n - 1 := by omega
    have h1 : 1 < n - 1 := by omega
    have hij : (⟨0, h0⟩ : Fin (n - 1)) ≠ ⟨1, h1⟩ := by simp [Fin.ext_iff]
    refine ⟨minusA n K ⟨0, h0⟩, minusB n K ⟨0, h0⟩ ⟨1, h1⟩, Q_minusA b c _, Q_minusB b c hij,
      B_minusB b hij, ?_, ?_⟩
    · rw [dot_minusM]; simp [minusA, hl, hr]
    · rw [dot_minusM]; simp [minusB, hl, hr]

theorem threeFixedModel_statedOmegaMinus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) (b c : K) (_hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ThreeFixedModel (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus n K b c))
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) := by
  intro v
  obtain ⟨a, a', ha, ha', haa, hva, hva'⟩ := exists_pair_minus hn b c v
  obtain ⟨g, hg, hg3, hgv⟩ :=
    exists_mem_statedOmega_orderOf_three (isQuadWith_minus b c) ha ha' haa hva hva'
  exact ⟨⟨g, hg⟩, by rw [Subgroup.orderOf_mk]; exact hg3, hgv⟩

end Minus

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
