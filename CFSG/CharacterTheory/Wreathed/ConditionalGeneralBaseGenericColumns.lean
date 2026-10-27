module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseSections
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseFusion
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootSections

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.BrauerWong
open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalSquareRoot
open CFSG.Wreathed.SquareRootSmallCharacterRigidity

variable {G : Type} [Group G] {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)} {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
    (wreathModelHom S e (Original.z (2 ^ n))) σ υ g)

theorem exists_orderOf_base (x : modelBase S e) : ∃ k : ℕ, orderOf (x : G) = 2 ^ k := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_dvd_of_pow_eq_one (pow_modulus_eq_one_of_mem_modelBase S e x.2))
  exact ⟨k, hk⟩

theorem generic_ne_one {u : modelBase S e} (hu : u ∉ h.exc) : (u : G) ≠ 1 := fun hu1 =>
  hu (by rw [show u = 1 from Subtype.ext hu1]; exact Or.inr (Subgroup.one_mem _))

theorem orderOf_generic {u : modelBase S e} (hu : u ∉ h.exc) :
    (∃ r : ℕ, 1 ≤ r ∧ orderOf (u : G) = 2 ^ r) ∧ orderOf (u : G) ∣ 2 ^ n := by
  have hdvd : orderOf (u : G) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (pow_modulus_eq_one_of_mem_modelBase S e u.2)
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨⟨r, Nat.one_le_iff_ne_zero.mpr fun hr0 => generic_ne_one h hu ?_, hr⟩, hdvd⟩
  rw [hr0, pow_zero, orderOf_eq_one_iff] at hr
  exact hr

variable [Fintype G]

theorem generic_centralizer_quotient (hn : 2 ≤ n) {u : modelBase S e} (hu : u ∉ h.exc) :
    ∃ (N : Subgroup (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G))) (_ : N.Normal),
      Odd (Nat.card N) ∧
      IsPGroup 2 (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) ⧸ N) ∧
      IsMulCommutative (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) ⧸ N) ∧
      Nat.card (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) ⧸ N) = (2 ^ n) ^ 2 := by
  have hC : Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) =
      Subgroup.centralizer ({(u : G)} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hC]
  obtain ⟨-, -, hindex, ⟨f, -⟩, hodd, -, -⟩ := centralizer_oddCore_complement h hn hu
  refine ⟨CFSG.oddCore _, inferInstance, hodd, ?_, ⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · apply IsPGroup.of_card (n := n * 2)
    rw [← Subgroup.index_eq_card, hindex, ← pow_mul]
  · show x * y = y * x
    obtain ⟨x, rfl⟩ := f.surjective x
    obtain ⟨y, rfl⟩ := f.surjective y
    rw [← map_mul f, ← map_mul f, mul_comm_base S e x y]
  · rw [← Subgroup.index_eq_card, hindex]

theorem generic_value_column (hn : 2 ≤ n) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : modelBase S e}
    (hu : u ∉ h.exc) :
    (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        conj ((basis.representation χ).character u) * (basis.representation χ).character u =
      ((2 ^ n : ℕ) : ℂ) ^ 2) ∧
    ∀ x : G, (∀ a c : G, a * c = x → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
      ¬ 2 ∣ orderOf c → ¬ IsConj a (u : G)) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character u * conj ((basis.representation χ).character x) =
          0 := by
  obtain ⟨⟨r, hr, hord⟩, -⟩ := orderOf_generic h hu
  obtain ⟨N, hnormal, hN, hquot, hcomm, hcard⟩ := generic_centralizer_quotient h hn hu
  obtain ⟨hnorm, hoff⟩ :=
    abelian_section_value_column basis ideal principal hprincipal hr hord N hN hquot
  refine ⟨?_, hoff⟩
  rw [hnorm, hcard]
  push_cast
  ring

theorem generic_column_norm (hn : 2 ≤ n) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : modelBase S e}
    (hu : u ∉ h.exc) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        conj ((basis.representation χ).character u) * (basis.representation χ).character u =
      ((2 ^ n : ℕ) : ℂ) ^ 2 :=
  (generic_value_column h hn basis ideal principal hprincipal hu).1

theorem generic_column_off_section (hn : 2 ≤ n) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : modelBase S e}
    (hu : u ∉ h.exc) (x : G)
    (hx : ∀ a c : G, a * c = x → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
      ¬ 2 ∣ orderOf c → ¬ IsConj a (u : G)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u * conj ((basis.representation χ).character x) = 0 :=
  (generic_value_column h hn basis ideal principal hprincipal hu).2 x hx

theorem generic_column_central_section (hn : 2 ≤ n) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : modelBase S e}
    (hu : u ∉ h.exc) (k : ℕ) {r : G}
    (hr : r ∈ Subgroup.centralizer ({wreathModelHom S e (Original.a (2 ^ n)) ^ k} : Set G))
    (hrodd : Odd (orderOf r)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u *
        conj ((basis.representation χ).character
          (wreathModelHom S e (Original.a (2 ^ n)) ^ k * r)) = 0 := by
  refine generic_column_off_section h hn basis ideal principal hprincipal hu _ ?_
  intro b c hbc hcomm hb hc hconj
  have hx : (((h.left * h.right) ^ k : modelBase S e) : G) =
      wreathModelHom S e (Original.a (2 ^ n)) ^ k := by
    rw [Subgroup.coe_pow, h.coe_left_mul_right]
  have hcomm' : Commute (((h.left * h.right) ^ k : modelBase S e) : G) r := by
    rw [hx]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hr).symm
  have hbx : b = (((h.left * h.right) ^ k : modelBase S e) : G) :=
    two_part_unique hbc hcomm hb (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hc)) (by rw [hx])
      hcomm' (exists_orderOf_base _) hrodd
  rw [hbx] at hconj
  exact not_isConj_of_mem_exc h hn (Or.inl (Or.inl (Subgroup.npow_mem_zpowers _ k))) hu hconj

theorem generic_column_odd_power (hn : 2 ≤ n) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : modelBase S e}
    (hu : u ∉ h.exc) {y : G} (hy : orderOf y = 2 * 2 ^ n) {t : ℤ} (ht : Odd t) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u *
        conj ((basis.representation χ).character (y ^ t)) = 0 := by
  refine generic_column_off_section h hn basis ideal principal hprincipal hu _ ?_
  intro b c hbc hcomm hb hc hconj
  have hy2 : orderOf y = 2 ^ (n + 1) := by rw [hy, pow_succ, Nat.mul_comm]
  have hyt : orderOf (y ^ t) = 2 ^ (n + 1) := orderOf_odd_power hy2 ht
  rw [two_part_eq_self ⟨n + 1, hyt⟩ hbc hcomm hb hc] at hconj
  obtain ⟨c', hc'⟩ := hconj
  have hdvd := (orderOf_generic h hu).2
  rw [← SemiconjBy.orderOf_eq _ hc', hyt, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at hdvd
  omega

theorem generic_column_odd_order (hn : 2 ≤ n) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : modelBase S e}
    (hu : u ∉ h.exc) {z : G} (hz : Odd (orderOf z)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u * conj ((basis.representation χ).character z) = 0 := by
  refine generic_column_off_section h hn basis ideal principal hprincipal hu _ ?_
  intro b c hbc hcomm hb hc hconj
  have hb1 : b = 1 :=
    two_part_unique hbc hcomm hb (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hc)) (one_mul z)
      (Commute.one_left z) ⟨0, by rw [orderOf_one, pow_zero]⟩ hz
  rw [hb1, isConj_one_right] at hconj
  exact generic_ne_one h hu hconj

theorem generic_column_generic (hn : 2 ≤ n) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : modelBase S e}
    (hu : u ∉ h.exc) (u' : modelBase S e) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character u * conj ((basis.representation χ).character u') =
      if IsConj (u : G) (u' : G) then ((2 ^ n : ℕ) : ℂ) ^ 2 else 0 := by
  split_ifs with hconj
  · have hχ : ∀ χ : basis.index, (basis.representation χ).character u' =
        (basis.representation χ).character u := by
      intro χ
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hc]
      exact Representation.char_conj (basis.representation χ).representation _ c
    rw [← generic_column_norm h hn basis ideal principal hprincipal hu]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hχ χ, mul_comm]
  · refine generic_column_off_section h hn basis ideal principal hprincipal hu _ ?_
    intro b c hbc hcomm hb hc hconj'
    rw [two_part_eq_self (exists_orderOf_base u') hbc hcomm hb hc] at hconj'
    exact hconj hconj'.symm

end CFSG.Wreathed.ConditionalGeneralBase
