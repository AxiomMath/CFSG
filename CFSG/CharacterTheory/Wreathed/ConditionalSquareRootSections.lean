module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigiditySignedEven
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsSections
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsPowers

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalSquareRoot

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.Wreathed.SquareRootSmallCharacterRigidity
  CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal CFSG.Wreathed.ConditionalFourier

theorem actualRoot_odd_zpow_isConj_add_modulus {G : Type} [Group G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) {h : ℤ} (hh : Odd h) :
    IsConj (actualRoot S e ^ h) (actualRoot S e ^ (h + (2 ^ n : ℕ))) := by
  set y := actualRoot S e with hy_def
  have hy : orderOf y = 2 * 2 ^ n := actualRoot_orderOf n hn S e
  have hy1 : y ^ ((2 * 2 ^ n : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hy, pow_orderOf_eq_one]
  set c := wreathModelHom S e (Original.x2 (2 ^ n)) with hc_def
  have hconj : c * y * c⁻¹ = y ^ (2 ^ n + 1) := actualRoot_conjugate_half n (by omega) S e
  refine isConj_iff.mpr ⟨c, ?_⟩
  have hmap : c * y ^ h * c⁻¹ = (c * y * c⁻¹) ^ h := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  rw [hmap, hconj, ← zpow_natCast, ← zpow_mul]
  obtain ⟨j, rfl⟩ := hh
  have hexp : ((2 ^ n + 1 : ℕ) : ℤ) * (2 * j + 1) =
      (2 * j + 1 + (2 ^ n : ℕ)) + ((2 * 2 ^ n : ℕ) : ℤ) * j := by
    push_cast
    ring
  rw [hexp, zpow_add, zpow_mul, hy1, one_zpow, mul_one]

theorem actualRoot_odd_zpow_isConj_iff {G : Type} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) {h t : ℤ} (hh : Odd h) (ht : Odd t) :
    IsConj (actualRoot S e ^ h) (actualRoot S e ^ t) ↔ h ≡ t [ZMOD (2 ^ n : ℕ)] := by
  set y := actualRoot S e with hy_def
  have hy : orderOf y = 2 * 2 ^ n := actualRoot_orderOf n hn S e
  have hmpos : 0 < 2 ^ n := by positivity
  constructor
  · intro hconj
    set a := wreathModelHom S e (Original.a (2 ^ n)) with ha_def
    have ha : orderOf a = 2 ^ n := orderOf_wreathModelHom_a n S e
    have hsq : y ^ 2 = a := actualRoot_sq S e
    have hpow2 : ∀ u : ℤ, (y ^ u) ^ 2 = a ^ u := fun u => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq]
    have hconj2 : IsConj (a ^ h) (a ^ t) := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      refine isConj_iff.mpr ⟨c, ?_⟩
      rw [← hpow2 h, ← hpow2 t, ← hc, conj_pow]
    have ham : a ^ (2 ^ n) = 1 := by rw [← ha, pow_orderOf_eq_one]
    rw [finite_order_zpow_eq_nat_remainder a (2 ^ n) hmpos ham h,
      finite_order_zpow_eq_nat_remainder a (2 ^ n) hmpos ham t] at hconj2
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hm2 : 2 ^ n = 2 * 2 ^ k := by rw [hk, pow_succ, mul_comm]
    have hrem : ∀ u : ℤ, Odd u → (u % ((2 ^ n : ℕ) : ℤ)).toNat ∈ Finset.Ico 1 (2 ^ n) := by
      intro u hu
      have hodd := odd_twice_remainder (m := 2 ^ k) (by positivity) u hu
      rw [← hm2] at hodd
      have hlt : (u % ((2 ^ n : ℕ) : ℤ)).toNat < 2 ^ n := by
        have h1 := Int.emod_lt_of_pos u (show (0 : ℤ) < ((2 ^ n : ℕ) : ℤ) by exact_mod_cast hmpos)
        omega
      exact Finset.mem_Ico.mpr ⟨hodd.pos, hlt⟩
    have heq := wreath_powers_eq_of_isConj n hn S e (hrem h hh) (hrem t ht) hconj2
    have hnonneg : ∀ u : ℤ, 0 ≤ u % ((2 ^ n : ℕ) : ℤ) := fun u =>
      Int.emod_nonneg u (by exact_mod_cast hmpos.ne')
    have h1 := Int.toNat_of_nonneg (hnonneg h)
    have h2 := Int.toNat_of_nonneg (hnonneg t)
    change h % ((2 ^ n : ℕ) : ℤ) = t % ((2 ^ n : ℕ) : ℤ)
    omega
  · intro hmod
    obtain ⟨q, hq⟩ : ∃ q : ℤ, t = h + (2 ^ n : ℕ) * q := by
      obtain ⟨q, hq⟩ := (Int.modEq_iff_dvd.mp hmod)
      exact ⟨q, by linarith⟩
    have hy1 : y ^ ((2 * 2 ^ n : ℕ) : ℤ) = 1 := by
      rw [zpow_natCast, ← hy, pow_orderOf_eq_one]
    rcases Int.even_or_odd q with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · have hyt : y ^ t = y ^ h := by
        rw [hq, show h + ((2 ^ n : ℕ) : ℤ) * (l + l) = h + ((2 * 2 ^ n : ℕ) : ℤ) * l by
          push_cast; ring, zpow_add, zpow_mul, hy1, one_zpow, mul_one]
      rw [hyt]
    · have hyt : y ^ t = y ^ (h + (2 ^ n : ℕ)) := by
        rw [hq, show h + ((2 ^ n : ℕ) : ℤ) * (2 * l + 1) =
          (h + ((2 ^ n : ℕ) : ℤ)) + ((2 * 2 ^ n : ℕ) : ℤ) * l by push_cast; ring,
          zpow_add, zpow_mul, hy1, one_zpow, mul_one]
      rw [hyt]
      exact actualRoot_odd_zpow_isConj_add_modulus n hn S e hh

theorem odd_power_column_orthogonal {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {h : ℤ} (hh : Odd h) (g : G)
    (hg : ∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
      ¬ 2 ∣ orderOf c → ¬ IsConj a (y ^ h)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character (y ^ h) *
        starRingEnd ℂ ((basis.representation χ).character g) = 0 := by
  have hy2 : orderOf y = 2 ^ (n + 1) := by rw [hy, pow_succ, Nat.mul_comm]
  have hyh := orderOf_odd_power hy2 hh
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers (y ^ h) : Set G)
  have hC : C = Subgroup.centralizer ({y ^ h} : Set G) := by
    dsimp only [C]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hdata := maximal_root_centralizer_odd_complement n hn S e (y ^ h) (by
    rw [hyh, pow_succ, Nat.mul_comm])
  dsimp only at hdata
  have hneeded : ∃ (N : Subgroup (Subgroup.centralizer ({y ^ h} : Set G)))
      (_ : N.Normal), Odd (Nat.card N) ∧
      IsPGroup 2 ((Subgroup.centralizer ({y ^ h} : Set G)) ⧸ N) ∧
      IsCyclic ((Subgroup.centralizer ({y ^ h} : Set G)) ⧸ N) := by
    obtain ⟨N, hnormal, hN, _, _, _, _, hquot, hcyc, _⟩ := hdata
    exact ⟨N, hnormal, hN, hquot, hcyc⟩
  rw [← hC] at hneeded
  obtain ⟨N, hnormal, hN, hquot, hcyc⟩ := hneeded
  let : N.Normal := hnormal
  let : IsCyclic (C ⧸ N) := hcyc
  let localBasis : FiniteIrreducibleCharacterBasis C :=
    Classical.choice finiteIrreducibleCharacterBasis_exists
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation C)
      (principalFiniteComplexRepresentation_isIrreducible C)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  exact principal_value_column_off_section basis ideal principal hprincipal (by omega) hyh
    localBasis localPrincipal hlocalPrincipal N hN hquot g hg

theorem two_part_eq_self {G : Type} [Group G] {u a c : G} (hu : ∃ e : ℕ, orderOf u = 2 ^ e)
    (hac : a * c = u) (hcomm : Commute a c) (ha : ∃ e : ℕ, orderOf a = 2 ^ e)
    (hc : ¬ 2 ∣ orderOf c) : a = u :=
  two_part_unique (G := G) hac hcomm ha (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hc))
    (mul_one u) (Commute.one_right u) hu (by rw [orderOf_one]; exact odd_one)

theorem actualRoot_odd_power_columns_orthogonal {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {h t : ℤ} (hh : Odd h) (ht : Odd t) (hht : ¬ h ≡ t [ZMOD (2 ^ n : ℕ)]) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character (actualRoot S e ^ h) *
        starRingEnd ℂ ((basis.representation χ).character (actualRoot S e ^ t)) = 0 := by
  have hy : orderOf (actualRoot S e) = 2 * 2 ^ n := actualRoot_orderOf n hn S e
  refine odd_power_column_orthogonal n hn S e _ hy basis ideal principal hprincipal hh _ ?_
  intro a c hac hcomm ha hc hconj
  have hy2 : orderOf (actualRoot S e) = 2 ^ (n + 1) := by rw [hy, pow_succ, Nat.mul_comm]
  have hat : a = actualRoot S e ^ t :=
    two_part_eq_self ⟨n + 1, orderOf_odd_power hy2 ht⟩ hac hcomm ha hc
  rw [hat] at hconj
  exact hht ((actualRoot_odd_zpow_isConj_iff n hn S e ht hh).mp hconj).symm

theorem actualRoot_odd_power_column_orthogonal_central {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {h : ℤ} (hh : Odd h) (k : ℕ) (r : G)
    (hr : r ∈ Subgroup.centralizer ({wreathModelHom S e (Original.a (2 ^ n)) ^ k} : Set G))
    (hrodd : Odd (orderOf r)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character (actualRoot S e ^ h) *
        starRingEnd ℂ ((basis.representation χ).character
          (wreathModelHom S e (Original.a (2 ^ n)) ^ k * r)) = 0 := by
  have hy : orderOf (actualRoot S e) = 2 * 2 ^ n := actualRoot_orderOf n hn S e
  refine odd_power_column_orthogonal n hn S e _ hy basis ideal principal hprincipal hh _ ?_
  set a := wreathModelHom S e (Original.a (2 ^ n)) with ha_def
  have ha : orderOf a = 2 ^ n := orderOf_wreathModelHom_a n S e
  intro b c hbc hcomm hb hc hconj
  have hcommr : Commute (a ^ k) r :=
    (Subgroup.mem_centralizer_singleton_iff.mp hr).symm
  have hak : ∃ e : ℕ, orderOf (a ^ k) = 2 ^ e := by
    have hdvd : orderOf (a ^ k) ∣ 2 ^ n := by
      rw [← ha]
      exact orderOf_pow_dvd k
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨i, hi⟩
  have hb' : b = a ^ k := two_part_unique hbc hcomm hb
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hc)) rfl hcommr hak hrodd
  rw [hb'] at hconj
  obtain ⟨c', hc'⟩ := isConj_iff.mp hconj
  have hord : orderOf (actualRoot S e ^ h) = orderOf (a ^ k) := by
    rw [← hc', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hy2 : orderOf (actualRoot S e) = 2 ^ (n + 1) := by rw [hy, pow_succ, Nat.mul_comm]
  rw [orderOf_odd_power hy2 hh] at hord
  have hdvd : orderOf (a ^ k) ∣ 2 ^ n := by
    rw [← ha]
    exact orderOf_pow_dvd k
  rw [← hord] at hdvd
  have := Nat.le_of_dvd (by positivity) hdvd
  rw [pow_succ] at this
  have hpos : 0 < 2 ^ n := by positivity
  omega

end CFSG.Wreathed.ConditionalSquareRoot
