module

public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteOrderFourier
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteCharacters
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare

public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem finiteOrderEigenprojection_apply_of_eigenvector {V : Type*} [AddCommGroup V]
    [Module ℂ V] (period : ℕ) (periodUnit eigenvalue : ℂˣ)
    (hunit : (periodUnit : ℂ) = period) (operator : Module.End ℂ V) {x : V}
    (hx : operator x = (eigenvalue : ℂ) • x) :
    finiteOrderEigenprojection period periodUnit eigenvalue operator x = x := by
  have hp : ∀ k : ℕ, (((↑eigenvalue⁻¹ : ℂ) • operator) ^ k) x = x := by
    intro k
    induction k with
    | zero => rfl
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply, hk, LinearMap.smul_apply, hx, smul_smul,
        Units.inv_mul, one_smul]
  change (↑periodUnit⁻¹ : ℂ) •
    ((∑ k ∈ Finset.range period, ((↑eigenvalue⁻¹ : ℂ) • operator) ^ k) x) = x
  rw [LinearMap.sum_apply]
  simp only [hp, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← hunit, Units.inv_mul, one_smul]

theorem finiteOrderEigenprojection_range_eq_eigenspace {V : Type*} [AddCommGroup V]
    [Module ℂ V] (period : ℕ) (periodUnit eigenvalue : ℂˣ)
    (hunit : (periodUnit : ℂ) = period) (heigenvalue : eigenvalue ^ period = 1)
    (operator : Module.End ℂ V) (hperiod : operator ^ period = 1) :
    (finiteOrderEigenprojection period periodUnit eigenvalue operator).range =
      operator.eigenspace (eigenvalue : ℂ) := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    exact congrArg (fun f : Module.End ℂ V => f v)
      (finiteOrderEigenprojection_eigenvalue period periodUnit eigenvalue
        heigenvalue operator hperiod)
  · intro x hx
    exact ⟨x, finiteOrderEigenprojection_apply_of_eigenvector period periodUnit
      eigenvalue hunit operator (Module.End.mem_eigenspace_iff.mp hx)⟩

theorem finite_order_eigenmultiplicity_trace {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (period : ℕ) (periodUnit eigenvalue : ℂˣ)
    (hunit : (periodUnit : ℂ) = period) (heigenvalue : eigenvalue ^ period = 1)
    (operator : Module.End ℂ V) (hperiod : operator ^ period = 1) :
    (↑periodUnit⁻¹ : ℂ) * ∑ k ∈ Finset.range period,
      (↑eigenvalue⁻¹ : ℂ) ^ k * LinearMap.trace ℂ V (operator ^ k) =
        (Module.finrank ℂ (operator.eigenspace (eigenvalue : ℂ)) : ℂ) := by
  have hidem := finiteOrderEigenprojection_idempotent period periodUnit eigenvalue
    hunit heigenvalue operator hperiod
  have htrace := (LinearMap.IsIdempotentElem.isProj_range
    (finiteOrderEigenprojection period periodUnit eigenvalue operator) hidem).trace
  rw [finiteOrderEigenprojection_range_eq_eigenspace period periodUnit eigenvalue
    hunit heigenvalue operator hperiod] at htrace
  rw [← htrace, finiteOrderEigenprojection, cyclicOperatorAverage, map_smul, map_sum]
  simp only [smul_pow, map_smul, smul_eq_mul]

theorem finiteOrderEigenprojection_power_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (period : ℕ) (periodUnit eigenvalue : ℂˣ) (heigenvalue : eigenvalue ^ period = 1)
    (operator : Module.End ℂ V) (hperiod : operator ^ period = 1) (h : ℕ) :
    operator ^ h * finiteOrderEigenprojection period periodUnit eigenvalue operator =
      ((eigenvalue : ℂ) ^ h) •
        finiteOrderEigenprojection period periodUnit eigenvalue operator := by
  induction h with
  | zero => simp
  | succ h hh =>
    rw [pow_succ', mul_assoc, hh, mul_smul_comm,
      finiteOrderEigenprojection_eigenvalue period periodUnit eigenvalue heigenvalue
        operator hperiod, smul_smul, pow_succ]

theorem finite_order_trace_power_expansion {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (period : ℕ) (periodUnit root : ℂˣ)
    (hunit : (periodUnit : ℂ) = period) (hroot : IsPrimitiveRoot (root : ℂ) period)
    (operator : Module.End ℂ V) (hperiod : operator ^ period = 1) (h : ℕ) :
    LinearMap.trace ℂ V (operator ^ h) =
      ∑ t ∈ Finset.range period,
        (Module.finrank ℂ (operator.eigenspace ((root : ℂ) ^ t)) : ℂ) *
          (root : ℂ) ^ (t * h) := by
  have hunitroot : root ^ period = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hroot.pow_eq_one
  have hp : ∀ t : ℕ, (root ^ t) ^ period = 1 := by
    intro t
    rw [← pow_mul, Nat.mul_comm, pow_mul, hunitroot, one_pow]
  have htrace (t : ℕ) :
      LinearMap.trace ℂ V (finiteOrderEigenprojection period periodUnit (root ^ t) operator) =
        (Module.finrank ℂ (operator.eigenspace ((root : ℂ) ^ t)) : ℂ) := by
    have hidem := finiteOrderEigenprojection_idempotent period periodUnit (root ^ t)
      hunit (hp t) operator hperiod
    have htr := (LinearMap.IsIdempotentElem.isProj_range
      (finiteOrderEigenprojection period periodUnit (root ^ t) operator) hidem).trace
    rw [finiteOrderEigenprojection_range_eq_eigenspace period periodUnit (root ^ t)
      hunit (hp t) operator hperiod] at htr
    simpa only [Units.val_pow_eq_pow_val] using htr
  have hsum := finiteOrderEigenprojection_sum period periodUnit root hunit hroot operator
  calc
    _ = LinearMap.trace ℂ V
        (operator ^ h * ∑ t ∈ Finset.range period,
          finiteOrderEigenprojection period periodUnit (root ^ t) operator) := by
      rw [hsum, mul_one]
    _ = _ := by
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [finiteOrderEigenprojection_power_action period periodUnit (root ^ t) (hp t)
        operator hperiod h, map_smul, smul_eq_mul, htrace t, Units.val_pow_eq_pow_val,
        ← pow_mul, mul_comm]

@[expose] def cyclicEigenmultiplicity {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (root : ℂ) (t : ℕ) : ℕ :=
  Module.finrank ℂ (Module.End.eigenspace (data.representation y) (root ^ t))

theorem character_cyclic_eigenmultiplicity_expansion {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (period : ℕ)
    (hp : 0 < period) (hy : y ^ period = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root period) (h : ℕ) :
    data.character (y ^ h) = ∑ t ∈ Finset.range period,
      (cyclicEigenmultiplicity data y root t : ℂ) * root ^ (t * h) := by
  let periodUnit : ℂˣ := Units.mk0 (period : ℂ) (Nat.cast_ne_zero.mpr hp.ne')
  let rootUnit : ℂˣ := Units.mk0 root (hroot.ne_zero hp.ne')
  have hperiod : data.representation y ^ period = 1 := by
    rw [← map_pow, hy, map_one]
  have hexp := finite_order_trace_power_expansion period periodUnit rootUnit rfl hroot
    (data.representation y) hperiod h
  have hrootVal : (rootUnit : ℂ) = root := rfl
  rw [hrootVal] at hexp
  rw [FiniteComplexRepresentation.character, Representation.character, map_pow]
  unfold cyclicEigenmultiplicity
  exact hexp

theorem character_cyclic_eigenmultiplicity_average {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (period : ℕ)
    (hp : 0 < period) (hy : y ^ period = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root period) (t : ℕ) :
    (period : ℂ)⁻¹ * ∑ k ∈ Finset.range period,
      (root ^ t)⁻¹ ^ k * data.character (y ^ k) =
        (cyclicEigenmultiplicity data y root t : ℂ) := by
  let periodUnit : ℂˣ := Units.mk0 (period : ℂ) (Nat.cast_ne_zero.mpr hp.ne')
  let rootUnit : ℂˣ := Units.mk0 root (hroot.ne_zero hp.ne')
  have hrootunit : rootUnit ^ period = 1 := by
    apply Units.ext
    change root ^ period = 1
    exact hroot.pow_eq_one
  have hEigen : (rootUnit ^ t) ^ period = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hrootunit, one_pow]
  have hperiod : data.representation y ^ period = 1 := by
    rw [← map_pow, hy, map_one]
  have havg := finite_order_eigenmultiplicity_trace period periodUnit (rootUnit ^ t)
    rfl hEigen (data.representation y) hperiod
  have hrootVal : (rootUnit : ℂ) = root := rfl
  have hperiodVal : (periodUnit : ℂ) = period := rfl
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hrootVal, hperiodVal] at havg
  unfold cyclicEigenmultiplicity
  simp only [FiniteComplexRepresentation.character, Representation.character, map_pow]
  exact havg

theorem character_cyclic_eigenmultiplicity_degree {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (period : ℕ)
    (hp : 0 < period) (hy : y ^ period = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root period) :
    ∑ t ∈ Finset.range period, cyclicEigenmultiplicity data y root t =
      Module.finrank ℂ data.vector := by
  have h := character_cyclic_eigenmultiplicity_expansion data y period hp hy root hroot 0
  simp only [pow_zero, Nat.mul_zero, mul_one,
    FiniteComplexRepresentation.character, Representation.char_one] at h
  exact_mod_cast h.symm

theorem cyclicEigenmultiplicity_eq_of_isConj {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) {y z : G} (period : ℕ)
    (hp : 0 < period) (hy : y ^ period = 1) (hz : z ^ period = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root period) (hconj : IsConj y z) (t : ℕ) :
    cyclicEigenmultiplicity data y root t = cyclicEigenmultiplicity data z root t := by
  have hvalues : ∀ k : ℕ, data.character (y ^ k) = data.character (z ^ k) := by
    intro k
    obtain ⟨c, hc⟩ := isConj_iff.mp (hconj.pow k)
    rw [← hc]
    exact (Representation.char_conj data.representation _ c).symm
  have havg := character_cyclic_eigenmultiplicity_average data y period hp hy root hroot t
  have hbvg := character_cyclic_eigenmultiplicity_average data z period hp hz root hroot t
  have heq : (cyclicEigenmultiplicity data y root t : ℂ) =
      (cyclicEigenmultiplicity data z root t : ℂ) := by
    rw [← havg, ← hbvg]
    simp only [hvalues]
  exact_mod_cast heq

theorem actual_root_character_eigenmultiplicities {G : Type} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* CFSG.Wreathed.Wreath (2 ^ n))
    (data : FiniteComplexRepresentation G) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    (∀ h : ℕ, data.character (CFSG.Wreathed.WreathCentralSquare.actualRoot S e ^ h) =
      ∑ t ∈ Finset.range (2 * 2 ^ n),
        (cyclicEigenmultiplicity data (CFSG.Wreathed.WreathCentralSquare.actualRoot S e)
          root t : ℂ) * root ^ (t * h)) ∧
    (∀ t : ℕ, ((2 * 2 ^ n : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 * 2 ^ n),
      (root ^ t)⁻¹ ^ k *
        data.character (CFSG.Wreathed.WreathCentralSquare.actualRoot S e ^ k) =
      (cyclicEigenmultiplicity data (CFSG.Wreathed.WreathCentralSquare.actualRoot S e)
        root t : ℂ)) ∧
    ∑ t ∈ Finset.range (2 * 2 ^ n),
      cyclicEigenmultiplicity data (CFSG.Wreathed.WreathCentralSquare.actualRoot S e) root t =
      Module.finrank ℂ data.vector := by
  have hp : 0 < 2 * 2 ^ n := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hy : CFSG.Wreathed.WreathCentralSquare.actualRoot S e ^ (2 * 2 ^ n) = 1 := by
    rw [← CFSG.Wreathed.WreathCentralSquare.actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  exact ⟨character_cyclic_eigenmultiplicity_expansion data _ _ hp hy root hroot,
    character_cyclic_eigenmultiplicity_average data _ _ hp hy root hroot,
    character_cyclic_eigenmultiplicity_degree data _ _ hp hy root hroot⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity




