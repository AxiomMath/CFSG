module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCentralFourierRows
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseGenericColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.BrauerWong
  CFSG.Wreathed.ConditionalSquareRoot CFSG.Wreathed.SquareRootSmallCharacterRigidity

variable {G : Type} [Group G] [Fintype G]

theorem twisted_rows_orthogonal_of_section (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (B : basis.index) (a : G)
    (m : ℕ) (C : ℕ → Subgroup G) (lamG ΦG : G → ℂ) (hΦreal : ∀ g, conj (ΦG g) = ΦG g)
    (ε : ℤ) (hlam0 : ∀ k ∈ Finset.Ico 1 m, ∀ c ∈ C k, lamG c ≠ 0)
    (hindep : ∀ k ∈ Finset.Ico 1 m, ∀ α β : ℂ,
      (∀ y ∈ C k, Odd (orderOf y) → α + β * (1 + ε * ΦG y) = 0) → α = 0 ∧ β = 0)
    (v : basis.index → ℕ → Fin 2 → ℂ)
    (hv : IsTwistedCentralSectionRows basis ideal B a m C lamG ΦG ε v)
    (W : basis.index → ℂ) {k : ℕ} (hk : k ∈ Finset.Ico 1 m)
    (hoff : ∀ r ∈ C k, Odd (orderOf r) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        W χ * conj ((basis.representation χ).character (a ^ k * r)) = 0) (ℓ : Fin 2) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      W χ * conj (v χ k ℓ) = 0 := by
  set BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B with hBB
  set α := ∑ χ ∈ BB, W χ * conj (v χ k 0) with hα
  set β := ∑ χ ∈ BB, W χ * conj (v χ k 1) with hβ
  have hcomb : ∀ r ∈ C k, Odd (orderOf r) → α + β * (1 + ε * ΦG r) = 0 := by
    intro r hr hrodd
    have hexp : ∑ χ ∈ BB, W χ * conj ((basis.representation χ).character (a ^ k * r)) =
        conj (lamG r) * (α + β * (1 + ε * ΦG r)) := by
      rw [hα, hβ, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [hv χ hχ k hk r hr hrodd]
      simp only [map_mul, map_add, map_one, map_intCast, hΦreal]
      ring
    have h := hoff r hr hrodd
    rw [hexp] at h
    exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero (starRingEnd ℂ)).mpr (hlam0 k hk r hr))
  have hzero := hindep k hk α β hcomb
  obtain rfl | rfl : ℓ = 0 ∨ ℓ = 1 := by fin_cases ℓ <;> simp
  · exact hzero.1
  · exact hzero.2

variable {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)} {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
    (wreathModelHom S e (Original.z (2 ^ n))) σ υ g)

theorem generic_columns_of_section (hn : 2 ≤ n) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (B : basis.index)
    {u u' : modelBase S e} (hu' : u' ∉ h.exc) (hconj : IsConj (u : G) (u' : G))
    (hnorm : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      (basis.representation χ).character u' * conj ((basis.representation χ).character u') =
        ((2 ^ n : ℕ) : ℂ) ^ 2)
    (hvan : ∀ x : G, (∀ a c : G, a * c = x → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
        Odd (orderOf c) → ¬ IsConj a (u' : G)) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character u' * conj ((basis.representation χ).character x) =
          0) :
    (∀ u'' : modelBase S e, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character u * conj ((basis.representation χ).character u'') =
      if IsConj (u : G) (u'' : G) then ((2 ^ n : ℕ) : ℂ) ^ 2 else 0) ∧
    (∀ (k : ℕ) (r : G),
      r ∈ Subgroup.centralizer ({wreathModelHom S e (Original.a (2 ^ n)) ^ k} : Set G) →
      Odd (orderOf r) → ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character u * conj ((basis.representation χ).character
          (wreathModelHom S e (Original.a (2 ^ n)) ^ k * r)) = 0) ∧
    (∀ yy : G, orderOf yy = 2 * 2 ^ n → ∀ t : ℤ, Odd t →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character u *
          conj ((basis.representation χ).character (yy ^ t)) = 0) ∧
    ∀ z : G, Odd (orderOf z) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character u * conj ((basis.representation χ).character z) = 0 := by
  have hval : ∀ χ : basis.index, (basis.representation χ).character u =
      (basis.representation χ).character u' := by
    intro χ
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [← hc]
    exact (Representation.char_conj (basis.representation χ).representation _ c).symm
  have hsum : ∀ T : basis.index → ℂ,
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character u * T χ =
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character u' * T χ :=
    fun T => Finset.sum_congr rfl fun χ _ => by rw [hval]
  obtain ⟨-, hdvd⟩ := ConditionalGeneralBase.orderOf_generic h hu'
  refine ⟨fun u'' => ?_, fun k r hr hrodd => ?_, fun yy hyy t ht => ?_, fun z hz => ?_⟩
  · rw [hsum]
    by_cases hc : IsConj (u : G) (u'' : G)
    · rw [ite_eq_left hc, ← hnorm]
      refine Finset.sum_congr rfl fun χ _ => ?_
      have h1 : (basis.representation χ).character u'' =
          (basis.representation χ).character u' := by
        rw [← hval χ]
        obtain ⟨c, hc'⟩ := isConj_iff.mp hc
        rw [← hc']
        exact Representation.char_conj (basis.representation χ).representation _ c
      rw [h1]
    · rw [ite_eq_right hc]
      refine hvan _ fun a' c' hac hcomm ha hc' hconj' => ?_
      have heq := ConditionalSquareRoot.two_part_eq_self
        (ConditionalGeneralBase.exists_orderOf_base u'') hac hcomm ha
        (fun h2 => (Nat.not_even_iff_odd.mpr hc') (even_iff_two_dvd.mpr h2))
      rw [heq] at hconj'
      exact hc (hconj.trans hconj'.symm)
  · rw [hsum]
    refine hvan _ fun a' c' hac hcomm ha hc' hconj' => ?_
    have hx : (((h.left * h.right) ^ k : modelBase S e) : G) =
        wreathModelHom S e (Original.a (2 ^ n)) ^ k := by
      rw [Subgroup.coe_pow, h.coe_left_mul_right]
    have hcomm' : Commute (((h.left * h.right) ^ k : modelBase S e) : G) r := by
      rw [hx]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hr).symm
    have hbx : a' = (((h.left * h.right) ^ k : modelBase S e) : G) :=
      ConditionalFourier.two_part_unique hac hcomm ha hc' (by rw [hx]) hcomm'
        (ConditionalGeneralBase.exists_orderOf_base _) hrodd
    rw [hbx] at hconj'
    exact not_isConj_of_mem_exc h hn (Or.inl (Or.inl (Subgroup.npow_mem_zpowers _ k))) hu'
      hconj'
  · rw [hsum]
    refine hvan _ fun a' c' hac hcomm ha hc' hconj' => ?_
    have hy2 : orderOf yy = 2 ^ (n + 1) := by rw [hyy, pow_succ, Nat.mul_comm]
    have hyt : orderOf (yy ^ t) = 2 ^ (n + 1) := orderOf_odd_power hy2 ht
    rw [ConditionalSquareRoot.two_part_eq_self ⟨n + 1, hyt⟩ hac hcomm ha
      (fun h2 => (Nat.not_even_iff_odd.mpr hc') (even_iff_two_dvd.mpr h2))] at hconj'
    obtain ⟨c'', hc''⟩ := hconj'
    have hd := hdvd
    rw [← SemiconjBy.orderOf_eq _ hc'', hyt, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at hd
    omega
  · rw [hsum]
    refine hvan _ fun a' c' hac hcomm ha hc' hconj' => ?_
    have hb1 : a' = 1 :=
      ConditionalFourier.two_part_unique hac hcomm ha hc' (one_mul z) (Commute.one_left z)
        ⟨0, by rw [orderOf_one, pow_zero]⟩ hz
    rw [hb1, isConj_one_right] at hconj'
    exact ConditionalGeneralBase.generic_ne_one h hu' hconj'

end CFSG.Wreathed.FlatBase
