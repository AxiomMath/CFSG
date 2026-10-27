module

public import CFSG.LieType.HighestRoot.CentLinearBasic
public import CFSG.ClassicalInvolution.Models.LinearPairs.Intrinsic
public import CFSG.ClassicalInvolution.WeakCT.Amalgam
public import CFSG.ClassicalInvolution.ModelFacts.Families

public section

namespace CFSG.LieType.HighestRoot

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem eq_one_of_pow_three_eq_one [Finite K] (hK : Nat.card K = 3) {c : K} (h : c ^ 3 = 1) :
    c = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hc := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, h] at hc
  exact hc.symm

theorem two_ne_zero_of_card_eq_three [Finite K] (hK : Nat.card K = 3) : (2 : K) ≠ 0 := by
  intro h
  have h3 := three_eq_zero hK
  have : (1 : K) = 0 := by linear_combination h3 - h
  exact one_ne_zero this

theorem mul_apply_of_col {A M : Matrix (Fin n) (Fin n) K} {j : Fin n}
    (hM : ∀ k, k ≠ j → M k j = 0) (i : Fin n) : (A * M) i j = A i j * M j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [hM k hk, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]

theorem eq_one_of_pow_three_eq_one_of_charP [CharP K 3] {c : K} (h : c ^ 3 = 1) : c = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (c - 1) ^ 3 = 0 := by rw [sub_pow_char, h, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)

theorem cube_apply_of_col {X : Matrix (Fin n) (Fin n) K} {j : Fin n}
    (hcol : ∀ i, i ≠ j → X i j = 0) : (X * X * X) j j = X j j ^ 3 := by
  rw [mul_apply_of_col hcol, mul_apply_of_col hcol, pow_three, mul_assoc]

theorem mul_one_add_negBlock_of_col {X : Matrix (Fin n) (Fin n) K}
    (hcol : ∀ j : Fin n, 2 ≤ j.val → ∀ i, i ≠ j → X i j = 0)
    (hdiag : ∀ j : Fin n, 2 ≤ j.val → X j j = 1) :
    X * (1 + negBlock K n 0) = 1 + negBlock K n 0 := by
  have hD : (1 : Matrix (Fin n) (Fin n) K) + negBlock K n 0 =
      Matrix.diagonal (fun a => if a.val < 2 then 0 else 2) := by
    rw [negBlock_eq_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    funext a
    by_cases ha : a.val < 2
    · have : 0 ≤ a.val ∧ a.val < 0 + 2 := by omega
      rw [ite_eq_left this, ite_eq_left ha]
      norm_num
    · have : ¬ (0 ≤ a.val ∧ a.val < 0 + 2) := by omega
      rw [ite_eq_right this, ite_eq_right ha]
      norm_num
  rw [hD]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply]
  by_cases hj : 2 ≤ j.val
  · rw [ite_eq_right (show ¬ j.val < 2 by omega)]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_right (show ¬ i.val < 2 by omega), hdiag i hj, one_mul]
    · rw [ite_eq_right hij, hcol j hj i hij, zero_mul]
  · rw [ite_eq_left (show j.val < 2 by omega), mul_zero]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_left (show i.val < 2 by omega)]
    · rw [ite_eq_right hij]

variable (K) in
@[expose] def rootCompl (n : ℕ) : Subgroup SL(n, K) :=
  longRootGroup (-(negBlock K n 0))

theorem negBlock_zero_apply (a b : Fin n) :
    negBlock K n 0 a b = if a = b then (if a.val < 2 then -1 else 1) else 0 := by
  rw [negBlock_eq_diagonal, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a.val < 2 <;> simp [ha]
  · simp [hab]

theorem apply_eq_zero_of_commute (h2 : (2 : K) ≠ 0) {X : Matrix (Fin n) (Fin n) K}
    (hX : X * negBlock K n 0 = negBlock K n 0 * X) {i j : Fin n} (hi : i.val < 2)
    (hj : 2 ≤ j.val) : X i j = 0 := by
  have h := congrFun (congrFun hX i) j
  rw [negBlock_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hj' : ¬ (0 ≤ j.val ∧ j.val < 0 + 2) := by omega
  have hi' : 0 ≤ i.val ∧ i.val < 0 + 2 := by omega
  rw [ite_eq_right hj', ite_eq_left hi'] at h
  have : (2 : K) * X i j = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

theorem rootCompl_le_centralizer (hn : 2 ≤ n) :
    rootCompl K n ≤ Subgroup.centralizer ({rootInv K hn} : Set SL(n, K)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have h := hx.1
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv]
  exact h

theorem centralizer_le_normalizer_rootCompl (hn : 2 ≤ n) :
    Subgroup.centralizer ({rootInv K hn} : Set SL(n, K)) ≤
      Subgroup.normalizer (rootCompl K n : Set SL(n, K)) := by
  have e : ∀ {c : SL(n, K)}, c ∈ Subgroup.centralizer ({rootInv K hn} : Set SL(n, K)) →
      (c : Matrix (Fin n) (Fin n) K) * -(negBlock K n 0) = -(negBlock K n 0) * c := fun hc => by
    have := congrArg (fun g : SL(n, K) => (g : Matrix (Fin n) (Fin n) K))
      (Subgroup.mem_centralizer_singleton_iff.mp hc)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv] at this
    rw [Matrix.mul_neg, Matrix.neg_mul, this]
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => conj_mem_longRootGroup_of_commute (e hc) hx
  · intro hx
    have h := conj_mem_longRootGroup_of_commute (e (inv_mem hc)) hx
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h

theorem rootInv_notMem_rootCompl (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    rootInv K hn ∉ rootCompl K n := by
  intro h
  have h1 := h.2
  rw [coe_rootInv, Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, negBlock_mul_self] at h1
  have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.one_apply_eq, negBlock_zero_apply,
    show (0 : ℕ) < 2 by norm_num, ite_true] at h3
  have : (2 : K) * 2 = 0 := by linear_combination -h3
  exact h2 (by simpa using this)

@[expose] def lowTransvection {i j : Fin n} (hij : j ≠ i) (c : K) : SL(n, K) :=
  ⟨Matrix.transvection j i c, Matrix.det_transvection_of_ne _ _ hij c⟩

theorem coe_lowTransvection {i j : Fin n} (hij : j ≠ i) (c : K) :
    ((lowTransvection hij c : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      Matrix.transvection j i c := rfl

theorem lowTransvection_mem_rootCompl {i j : Fin n} (hij : j ≠ i) (hi : 2 ≤ i.val)
    (hj : 2 ≤ j.val) (c : K) : lowTransvection hij c ∈ rootCompl K n := by
  have hSN : Matrix.single j i c * negBlock K n 0 = Matrix.single j i c := by
    ext a b
    rw [negBlock_eq_diagonal, Matrix.mul_diagonal]
    by_cases hb : b = i
    · subst hb
      have : ¬ (0 ≤ b.val ∧ b.val < 0 + 2) := by omega
      rw [ite_eq_right this, mul_one]
    · simp [Ne.symm hb]
  have hNS : negBlock K n 0 * Matrix.single j i c = Matrix.single j i c := by
    ext a b
    rw [negBlock_eq_diagonal, Matrix.diagonal_mul]
    by_cases ha : a = j
    · subst ha
      have : ¬ (0 ≤ a.val ∧ a.val < 0 + 2) := by omega
      rw [ite_eq_right this, one_mul]
    · simp [Ne.symm ha]
  refine ⟨?_, ?_⟩
  · show (1 + Matrix.single j i c) * -(negBlock K n 0) =
      -(negBlock K n 0) * (1 + Matrix.single j i c)
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul,
      Matrix.mul_neg, hSN, hNS, Matrix.one_mul, Matrix.mul_one]
  · show (1 + Matrix.single j i c) * (1 + -(negBlock K n 0)) = 1 + -(negBlock K n 0)
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_neg, hSN,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel

theorem mem_rootSL2_of_orderOf_eq_three [Finite K] (hK : Nat.card K = 3) (hn : 2 ≤ n)
    {x : SL(n, K)} (hx : x ∈ Subgroup.centralizer ({rootInv K hn} : Set SL(n, K)))
    (h3 : orderOf x = 3) (hc : ∀ y ∈ rootCompl K n, Commute x y) : x ∈ rootSL2 K hn := by
  have h2 := two_ne_zero_of_card_eq_three hK
  set X := (x : Matrix (Fin n) (Fin n) K) with hXdef
  have hxz : X * negBlock K n 0 = negBlock K n 0 * X := by
    have := congrArg (fun g : SL(n, K) => (g : Matrix (Fin n) (Fin n) K))
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv] at this
    exact this
  have hcol : ∀ j : Fin n, 2 ≤ j.val → ∀ i, i ≠ j → X i j = 0 := by
    intro j hj i hij
    by_cases hi : i.val < 2
    · exact apply_eq_zero_of_commute h2 hxz hi hj
    · have hT := (hc _ (lowTransvection_mem_rootCompl hij.symm (by omega) hj 1)).eq
      have h0 : X * (1 + Matrix.single j i 1) = (1 + Matrix.single j i 1) * X := by
        have := congrArg (fun g : SL(n, K) => (g : Matrix (Fin n) (Fin n) K)) hT
        simp only [Matrix.SpecialLinearGroup.coe_mul, coe_lowTransvection,
          Matrix.transvection] at this
        exact this
      have h : X * Matrix.single j i 1 = Matrix.single j i 1 * X := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h0
        exact add_left_cancel h0
      have h' := congrFun (congrFun h i) i
      rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij,
        mul_one] at h'
      exact h'
  have hdiag : ∀ j : Fin n, 2 ≤ j.val → X j j = 1 := by
    intro j hj
    have hx3 : X * X * X = 1 := by
      have := congrArg (fun g : SL(n, K) => (g : Matrix (Fin n) (Fin n) K))
        (pow_orderOf_eq_one x)
      simp only [h3, pow_three, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_one] at this
      rw [← Matrix.mul_assoc] at this
      exact this
    have e1 := cube_apply_of_col (hcol j hj)
    rw [hx3, Matrix.one_apply_eq] at e1
    exact eq_one_of_pow_three_eq_one hK e1.symm
  rw [rootSL2_eq_longRootGroup h2 hn]
  exact ⟨hxz, mul_one_add_negBlock_of_col hcol hdiag⟩

theorem centralizerCondition_rootSL2 (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    CentralizerCondition K (rootSL2 K hn) := by
  have hc := isClassicalSL2_rootSL2 h2 hn
  intro z hz hz2
  obtain rfl := (isLongRootSL2_standard (K := K) hn).eq_of_orderOf_eq_two h2 hz hz2
  refine ⟨hc.centralizer_le_normalizer, fun hK L hLc hLn hLe hzL => ?_⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact eq_of_normal_of_orderOf_three hK hz2 hc.nonempty_mulEquiv (rootCompl_le_centralizer hn)
    (centralizer_le_normalizer_rootCompl hn) (rootInv_notMem_rootCompl h2 hn)
    (fun x hx h3 hcomm => mem_rootSL2_of_orderOf_eq_three hK hn hx h3 hcomm) hLc hLn hLe hzL

theorem highestRootCZ_specialLinear {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {m : ℕ}
    (hm : 1 ≤ m) : HighestRootCZ (CFSG.LieType.Universal.SpecialLinear.rootDatum m F) F := by
  refine ⟨Pi.single ⟨0, hm⟩ 1, Or.inl ⟨1, ⟨0, hm⟩, by simp⟩, fun δ hδ =>
    (CFSG.ClassicalInvolution.ModelFacts.isLongest_single_A (m := m) hm rfl
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m F).isFiniteType _).2 δ hδ, ?_⟩
  have e : rankOneGroup (CFSG.LieType.Universal.SpecialLinear.rootDatum m F)
      (Pi.single ⟨0, hm⟩ 1) = rootSL2 F (by omega : 2 ≤ m + 1) :=
    rankOne_eq_range (K := F) (⟨0, hm⟩ : Fin m)
  rw [e]
  exact centralizerCondition_rootSL2 h2 _

end CFSG.LieType.HighestRoot
