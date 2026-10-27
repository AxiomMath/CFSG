module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.CharSum
public import CFSG.Open.StatedDefs
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

theorem chi_finset_sum (hF : Nat.card F = 2) {ι : Type} (s : Finset ι) (a : ι → F) :
    chi (∑ i ∈ s, a i) = ∏ i ∈ s, chi (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, chi_add hF, ih]

theorem sum_chi_mul (hF : Nat.card F = 2) : ∑ p : F × F, chi (p.1 * p.2) = 2 := by
  have hc : ({0, 1} : Finset F).card = Fintype.card F := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hF]
  have huniv : (Finset.univ : Finset F) = {0, 1} := (Finset.eq_univ_of_card _ hc).symm
  rw [Fintype.sum_prod_type]
  simp [huniv, chi_zero, chi_of_ne_zero (one_ne_zero (α := F))]

theorem sum_chi_hyperbolic (hF : Nat.card F = 2) {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∑ x : ι → F, ∑ y : ι → F, chi (∑ i, x i * y i) = 2 ^ Fintype.card ι := by
  classical
  have h1 : ∀ x y : ι → F, chi (∑ i, x i * y i) = ∏ i, chi (x i * y i) := fun x y =>
    chi_finset_sum hF _ _
  simp_rw [h1]
  have h2 : ∑ x : ι → F, ∑ y : ι → F, ∏ i, chi (x i * y i) =
      ∑ p : ι → F × F, ∏ i, chi ((p i).1 * (p i).2) := by
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ => F) (fun _ => F)).symm _ _ fun _ => rfl
  rw [h2]
  have h3 := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (F × F)))
    (fun _ q => chi (q.1 * q.2))
  rw [Fintype.piFinset_univ] at h3
  rw [← h3]
  simp [sum_chi_mul hF]

theorem sum_chi_binary (hF : Nat.card F = 2) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∑ t : Fin 2 → F, chi (t 0 ^ 2 + b * t 0 * t 1 + c * t 1 ^ 2) = -2 := by
  have hN : ∀ t : Fin 2 → F, t ≠ 0 → t 0 ^ 2 + b * t 0 * t 1 + c * t 1 ^ 2 ≠ 0 := by
    intro t ht h0
    by_cases h1 : t 1 = 0
    · have h0' : t 0 ≠ 0 := by
        intro h
        apply ht
        funext i
        fin_cases i
        · exact h
        · exact h1
      apply h0'
      rw [h1] at h0
      simpa using h0
    · apply hirr (t 0 / t 1)
      have : t 1 ^ 2 * ((t 0 / t 1) ^ 2 + b * (t 0 / t 1) + c) =
          t 0 ^ 2 + b * t 0 * t 1 + c * t 1 ^ 2 := by
        field_simp
      have h2 : t 1 ^ 2 * ((t 0 / t 1) ^ 2 + b * (t 0 / t 1) + c) = 0 := by rw [this]; exact h0
      exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 h1)
  have hsum : ∀ t : Fin 2 → F, chi (t 0 ^ 2 + b * t 0 * t 1 + c * t 1 ^ 2) =
      if t = 0 then 1 else -1 := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp [chi_zero]
    · simp only [ht, ↓reduceIte]; exact chi_of_ne_zero (hN t ht)
  simp_rw [hsum]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have hcard : Fintype.card (Fin 2 → F) = 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hF]; norm_num
  have h1 : (Finset.univ.filter fun t : Fin 2 → F => t = 0).card = 1 := by
    rw [Finset.filter_eq']; simp
  have h2 : (Finset.univ.filter fun t : Fin 2 → F => ¬ t = 0).card = 3 := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), h1,
      Finset.card_univ, hcard]
  rw [h1, h2]
  norm_num

theorem charSum_statedQuadMinus (hF : Nat.card F = 2) {n : ℕ} (hn : 1 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∑ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F, chi (StatedQuadMinus n F b c v) =
      -(2 : ℤ) ^ n := by
  classical
  let e : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) ≃
      (Fin (n - 1) → F) × ((Fin (n - 1) → F) × (Fin 2 → F)) :=
    (Equiv.sumArrowEquivProdArrow _ _ F).trans
      ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ F))
  let g : (Fin (n - 1) → F) × ((Fin (n - 1) → F) × (Fin 2 → F)) → ℤ := fun p =>
    chi (∑ i, p.1 i * p.2.1 i) * chi (p.2.2 0 ^ 2 + b * p.2.2 0 * p.2.2 1 + c * p.2.2 1 ^ 2)
  have he1 : ∀ v i, (e v).1 i = v (Sum.inl i) := fun v i => rfl
  have he2 : ∀ v i, (e v).2.1 i = v (Sum.inr (Sum.inl i)) := fun v i => rfl
  have he3 : ∀ v k, (e v).2.2 k = v (Sum.inr (Sum.inr k)) := fun v k => rfl
  have hQ : ∀ v, chi (StatedQuadMinus n F b c v) = g (e v) := by
    intro v
    simp only [g, he1, he2, he3]
    rw [← chi_add hF]
    congr 1
    simp only [StatedQuadMinus]
    ring
  rw [Finset.sum_congr rfl fun v _ => hQ v, Fintype.sum_equiv e (fun v => g (e v)) g
    (fun _ => rfl)]
  simp only [g]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_chi_hyperbolic hF, sum_chi_binary hF hirr, Fintype.card_fin]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

end CFSG.HardMathSupport.Curtis.UnitaryLevi
