module

public import CFSG.LieType.HighestRoot.CentLinear
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2

public section

namespace CFSG.LieType.HighestRoot

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

variable (K p f) in
@[expose] noncomputable def rootComplSU (n : ℕ) : Subgroup (Su K p f n) :=
  longRootGroupSU K p f (-(negBlock K n 0))

theorem rootComplSU_le_centralizer (hn : 2 ≤ n) :
    rootComplSU K p f n ≤ Subgroup.centralizer ({rootInvSU K p f hn} : Set (Su K p f n)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply suMat_injective
  have h := hx.1
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  rw [suMat_mul, suMat_mul, suMat_rootInvSU]
  exact h

theorem centralizer_le_normalizer_rootComplSU (hn : 2 ≤ n) :
    Subgroup.centralizer ({rootInvSU K p f hn} : Set (Su K p f n)) ≤
      Subgroup.normalizer (rootComplSU K p f n : Set (Su K p f n)) := by
  have e : ∀ {c : Su K p f n},
      c ∈ Subgroup.centralizer ({rootInvSU K p f hn} : Set (Su K p f n)) →
        suMat c * -(negBlock K n 0) = -(negBlock K n 0) * suMat c := fun hc => by
    have := congrArg suMat (Subgroup.mem_centralizer_singleton_iff.mp hc)
    rw [suMat_mul, suMat_mul, suMat_rootInvSU] at this
    rw [Matrix.mul_neg, Matrix.neg_mul, this]
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => conj_mem_longRootGroupSU_of_commute (e hc) hx
  · intro hx
    have h := conj_mem_longRootGroupSU_of_commute (e (inv_mem hc)) hx
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h

theorem rootInvSU_notMem_rootComplSU (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    rootInvSU K p f hn ∉ rootComplSU K p f n := by
  intro h
  have h1 : suMat (rootInvSU K p f hn) * (1 + -negBlock K n 0) = 1 + -negBlock K n 0 := h.2
  rw [suMat_rootInvSU, Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, negBlock_mul_self] at h1
  have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.one_apply_eq, negBlock_zero_apply,
    show (0 : ℕ) < 2 by norm_num, ite_true] at h3
  have : (2 : K) * 2 = 0 := by linear_combination -h3
  exact h2 (by simpa using this)

omit [Finite K] [Fact p.Prime] in
theorem eq_one_of_pow_three_eq_one_of_charP_eq (hp : p = 3) {c : K} (h : c ^ 3 = 1) : c = 1 := by
  subst hp
  exact eq_one_of_pow_three_eq_one_of_charP h

theorem exists_sq_eq_neg_one_of_three (hK : Nat.card K = (p ^ f) ^ 2) (h3 : p ^ f = 3) :
    ∃ ι : K, ι ≠ 0 ∧ ι * ι = -1 ∧ unitaryInvolution K p f ι * ι = 1 := by
  obtain ⟨ι, hι0, hι⟩ := exists_unitaryInvolution_eq_neg hK
  have hcube : ι ^ 3 = -ι := by rw [← h3, ← unitaryInvolution_apply, hι]
  have hsq : ι * ι = -1 := by
    have : ι * (ι * ι + 1) = 0 := by linear_combination hcube
    linear_combination (mul_eq_zero.1 this).resolve_left hι0
  exact ⟨ι, hι0, hsq, by rw [hι]; linear_combination -hsq⟩

theorem mem_rootSU2_of_orderOf_eq_three (hK : Nat.card K = (p ^ f) ^ 2) (h3q : p ^ f = 3)
    (hn : 2 ≤ n) {x : Su K p f n}
    (hx : x ∈ Subgroup.centralizer ({rootInvSU K p f hn} : Set (Su K p f n)))
    (h3 : orderOf x = 3) (hc : ∀ y ∈ rootComplSU K p f n, Commute x y) :
    x ∈ rootSU2 K p f hn := by
  have hp3 : p = 3 := by
    have hf : f ≠ 0 := by
      rintro rfl
      simp at h3q
    have hdvd : p ∣ p ^ f := dvd_pow_self p hf
    rw [h3q] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 hdvd
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (by omega)
  obtain ⟨ι, hι0, hιsq, hιnorm⟩ := exists_sq_eq_neg_one_of_three hK h3q
  set X := suMat x with hXdef
  have hxz : X * negBlock K n 0 = negBlock K n 0 * X := by
    have := congrArg suMat (Subgroup.mem_centralizer_singleton_iff.mp hx)
    rw [suMat_mul, suMat_mul, suMat_rootInvSU] at this
    exact this
  let u : normOne (unitaryInvolution K p f) := ⟨Units.mk0 ι hι0, hιnorm⟩
  have hcol : ∀ j : Fin n, 2 ≤ j.val → ∀ i, i ≠ j → X i j = 0 := by
    intro j hj i hij
    by_cases hi : i.val < 2
    · exact apply_eq_zero_of_commute h2 hxz hi hj
    ·
      let d : Fin n → normOne (unitaryInvolution K p f) := fun a =>
        (if a = j then u else 1) * (if a = i then u⁻¹ else 1)
      have hd : d ∈ detKer (unitaryInvolution K p f) n := by
        rw [mem_detKer]
        simp only [d, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true,
          mul_inv_cancel]
      set t := diagSU (unitaryInvolution K p f) d hd
      have hD : suMat t = Matrix.diagonal fun a => ((d a : normOne _) : Kˣ).val := rfl
      have hdj : ((d j : normOne _) : Kˣ).val = ι := by
        simp [d, Ne.symm hij, u]
      have hdi : ((d i : normOne _) : Kˣ).val = ι⁻¹ := by
        simp [d, hij, u]
      have hdlow : ∀ a : Fin n, a.val < 2 → ((d a : normOne _) : Kˣ).val = 1 := by
        intro a ha
        have haj : a ≠ j := fun e => by rw [e] at ha; omega
        have hai : a ≠ i := fun e => by rw [e] at ha; omega
        simp [d, haj, hai]
      have htC : t ∈ rootComplSU K p f n := by
        refine mem_longRootGroupSU.2 ⟨?_, ?_⟩
        · rw [hD, negBlock_eq_diagonal, Matrix.mul_neg, Matrix.neg_mul,
            Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
          congr 2
          funext a
          ring
        · rw [hD, negBlock_eq_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_neg,
            Matrix.diagonal_add, Matrix.diagonal_mul_diagonal]
          congr 1
          funext a
          by_cases ha : a.val < 2
          · rw [hdlow a ha, one_mul]
          · have : ¬ (0 ≤ a.val ∧ a.val < 0 + 2) := by omega
            rw [ite_eq_right this]
            ring
      have hT := congrArg suMat (hc t htC).eq
      rw [suMat_mul, suMat_mul, hD] at hT
      have h := congrFun (congrFun hT i) j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hdj, hdi] at h
      have hne : ι - ι⁻¹ ≠ 0 := by
        have hinv : ι⁻¹ = -ι := inv_eq_of_mul_eq_one_right (by linear_combination -hιsq)
        rw [hinv, sub_neg_eq_add, ← two_mul]
        exact mul_ne_zero h2 hι0
      have : X i j * (ι - ι⁻¹) = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_right hne
  have hdiag : ∀ j : Fin n, 2 ≤ j.val → X j j = 1 := by
    intro j hj
    have hx3 : X * X * X = 1 := by
      have := congrArg suMat (pow_orderOf_eq_one x)
      rw [h3, pow_three, suMat_mul, suMat_mul, suMat_one] at this
      rw [← Matrix.mul_assoc] at this
      exact this
    have e1 := cube_apply_of_col (hcol j hj)
    rw [hx3, Matrix.one_apply_eq] at e1
    exact eq_one_of_pow_three_eq_one_of_charP_eq hp3 e1.symm
  rw [rootSU2_eq_longRootGroupSU h2 hn]
  exact ⟨hxz, mul_one_add_negBlock_of_col hcol hdiag⟩

theorem centralizerCondition_rootSU2 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n) :
    CentralizerCondition (fixedSubfield K p f) (rootSU2 K p f hn) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  have hc := isClassicalSL2_rootSU2 hK hp hn
  intro z hz hz2
  obtain rfl := (isLongRootSU2_standard (K := K) (p := p) (f := f) hn).eq_of_orderOf_eq_two hK hp
    hz hz2
  refine ⟨hc.centralizer_le_normalizer, fun hF L hLc hLn hLe hzL => ?_⟩
  have h3q : p ^ f = 3 := by rw [← card_fixedSubfield hK, hF]
  have : Finite (fixedSubfield K p f) := Nat.finite_of_card_ne_zero (by omega)
  exact eq_of_normal_of_orderOf_three hF hz2 hc.nonempty_mulEquiv
    (rootComplSU_le_centralizer hn) (centralizer_le_normalizer_rootComplSU hn)
    (rootInvSU_notMem_rootComplSU h2 hn)
    (fun x hx h3 hcomm => mem_rootSU2_of_orderOf_eq_three hK h3q hn hx h3 hcomm)
    hLc hLn hLe hzL

end CFSG.LieType.HighestRoot
