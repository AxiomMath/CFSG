module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerDegreeProductSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.OrderFourDegreeCongruence
public import CFSG.CharacterTheory.Semidihedral.Principal.OddFourierFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem character_ne_one_of_not_mem_ker {K : Type*} [Group K] [Finite K]
    (data : FiniteComplexRepresentation K) {g : K}
    (hg : g ∉ MonoidHom.ker data.representation) : data.character g ≠ data.character 1 := by
  intro h
  apply hg
  rw [MonoidHom.mem_ker]
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpow : data.representation g ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have htr : LinearMap.trace ℂ data.vector (data.representation g) =
      (Module.finrank ℂ data.vector : ℂ) := by
    rw [← Representation.char_one data.representation]
    exact h
  exact CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank _ hn hpow htr

theorem family_character_nonconstant {G : Type} [Group G] [Fintype G] {t : G}
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (localPrincipal : localBasis.index) (q : ℕ) (φ : C t → ℂ)
    (hφ : ∃ lφ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
      (localBasis.representation lφ).IsIrreducible ∧
      (localBasis.representation lφ).character = φ ∧
      Module.finrank ℂ (localBasis.representation lφ).vector = q ∧
      MonoidHom.ker (localBasis.representation lφ).representation = NZ t) :
    φ 1 = q ∧ ∃ y : C t, Odd (orderOf y) ∧ φ y ≠ q := by
  obtain ⟨lφ, -, -, hchar, hdeg, hker⟩ := hφ
  have hφ1 : φ 1 = q := by
    rw [← hchar, ← hdeg]
    exact (basis_character_one localBasis lφ).1
  refine ⟨hφ1, ?_⟩
  have : Finite (Gamma t) := Finite.of_surjective _ (QuotientGroup.mk'_surjective (NZ t))
  obtain ⟨γ, hγ1, hγodd⟩ := exists_ne_one_odd_orderOf_of_isSimpleGroup hnonab
  have hγ1' : (γ : Gamma t) ≠ 1 := fun h => hγ1 (Subtype.ext h)
  have hγodd' : Odd (orderOf (γ : Gamma t)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨y, hy, hκy⟩ := exists_odd_orderOf_map_ne_one (kappa t)
    (QuotientGroup.mk'_surjective _) hγ1' hγodd'
  refine ⟨y, hy, fun h => ?_⟩
  have hyker : y ∉ MonoidHom.ker (localBasis.representation lφ).representation := by
    rw [hker]
    intro hmem
    apply hκy
    exact (QuotientGroup.eq_one_iff y).mpr hmem
  apply character_ne_one_of_not_mem_ker (localBasis.representation lφ) hyker
  rw [hchar, h, hφ1]

theorem coefficient_eq_of_combination_eq {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) {B : Finset basis.index} (k k' : basis.index → ℂ)
    (h : (fun g => ∑ d ∈ B, k d * (basis.representation d).character g) =
      fun g => ∑ d ∈ B, k' d * (basis.representation d).character g) {c : basis.index}
    (hc : c ∈ B) : k c = k' c := by
  rw [← basis_combination_coefficient basis hc k, ← basis_combination_coefficient basis hc k', h]

theorem eq_of_coefficient_ne_zero {ι : Type*} [DecidableEq ι] {x₀ x₁ x₂ x₃ y : ι}
    {δ₁ δ₂ δ₃ δ : ℤ} (hδ : δ ≠ 0) (hy : y ≠ x₀) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h23 : x₂ ≠ x₃)
    (h : δ = (if y = x₀ then 1 else 0) + δ₁ * (if y = x₁ then 1 else 0) +
      δ₂ * (if y = x₂ then 1 else 0) + δ₃ * (if y = x₃ then 1 else 0)) :
    (y = x₁ ∧ δ = δ₁) ∨ (y = x₂ ∧ δ = δ₂) ∨ (y = x₃ ∧ δ = δ₃) := by
  by_cases hy1 : y = x₁
  · subst hy1
    simp [hy, h12, h13] at h
    exact Or.inl ⟨rfl, h⟩
  by_cases hy2 : y = x₂
  · subst hy2
    simp [hy, hy1, h23] at h
    exact Or.inr (Or.inl ⟨rfl, h⟩)
  by_cases hy3 : y = x₃
  · subst hy3
    simp [hy, hy1, hy2] at h
    exact Or.inr (Or.inr ⟨rfl, h⟩)
  simp [hy, hy1, hy2, hy3] at h
  exact absurd h hδ

theorem sum_cyclicRoot_eq_zero_of_noncentral {M : ℕ} (hM : 0 < M) (hM2 : Even M) {w : ℤ}
    (hw0 : ¬ (M : ℤ) ∣ w) (hw1 : ¬ (M : ℤ) ∣ w + (M / 2 : ℕ)) :
    ∑ j ∈ Finset.range M, cyclicRoot M ^ ((j : ℤ) * w) = 0 ∧
      ∑ j ∈ Finset.range M, (-1 : ℂ) ^ j * cyclicRoot M ^ ((j : ℤ) * w) = 0 := by
  constructor
  · have h := sum_range_cyclicRoot_zpow hM w
    rw [ite_eq_right hw0] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  · have h := sum_range_cyclicRoot_zpow hM (w + (M / 2 : ℕ))
    rw [ite_eq_right hw1] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (w + ((M / 2 : ℕ) : ℤ)) * j = (j : ℤ) * w + (j : ℤ) * ((M / 2 : ℕ) : ℤ) by ring,
      zpow_add₀ (cyclicRoot_ne_zero M), mul_comm]
    congr 1
    rw [mul_comm, zpow_mul, zpow_natCast, zpow_natCast, cyclicRoot_pow_half hM hM2]

theorem character_zpow_of_multiplicities {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) {g : G} {M : ℕ} (hM : 0 < M) (hM4 : 4 ∣ M)
    (hg : g ^ M = 1) (χ : basis.index) (θ η : ℤ)
    (hθ : multiplicityColumn basis g M ((M / 2 : ℕ) : ℤ) χ =
      multiplicityColumn basis g M 0 χ - θ)
    (hη : ∀ j : ℕ, j < M → Even j → j ≠ 0 → j ≠ M / 2 →
      multiplicityColumn basis g M j χ = multiplicityColumn basis g M 0 χ - η)
    (hodd : ∀ j : ℕ, j < M → Odd j →
      multiplicityColumn basis g M j χ = multiplicityColumn basis g M 1 χ)
    (v : ℤ) (hv0 : ¬ v ≡ 0 [ZMOD M]) (hv1 : ¬ v ≡ (M / 2 : ℕ) [ZMOD M]) :
    (basis.representation χ).character (g ^ v) = η + (η - θ) * (-1 : ℂ) ^ v := by
  have hM2 : Even M := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hM4)
  have hM2' : Even (M / 2) := by
    obtain ⟨m, hm⟩ := hM4
    exact ⟨m, by omega⟩
  set L : ℤ → ℤ := fun j => multiplicityColumn basis g M j χ with hLdef
  set w : ℕ := (v % (M : ℤ)).toNat with hwdef
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
  have hwv : (w : ℤ) = v % M := Int.toNat_of_nonneg (Int.emod_nonneg _ hMpos.ne')
  have hwlt : w < M := by
    have := Int.emod_lt_of_pos v hMpos
    omega
  have hgv : g ^ v = g ^ w := by
    rw [zpow_eq_zpow_emod' v hg, ← hwv, zpow_natCast]
  have hneg : (-1 : ℂ) ^ v = (-1 : ℂ) ^ w := by
    have hv : v = (w : ℤ) + M * (v / M) := by
      have h := Int.mul_ediv_add_emod v M
      rw [hwv]
      linarith
    rw [hv, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul, zpow_natCast, zpow_natCast,
      hM2.neg_one_pow, one_zpow, mul_one]
  have hwv' : (w : ℤ) ≡ v [ZMOD M] := by rw [hwv]; exact Int.mod_modEq v M
  have hw0 : ¬ (M : ℤ) ∣ (w : ℤ) := fun h =>
    hv0 (hwv'.symm.trans (Int.modEq_zero_iff_dvd.mpr h))
  have hw1 : ¬ (M : ℤ) ∣ (w : ℤ) + ((M / 2 : ℕ) : ℤ) := by
    intro h
    have h' : (M : ℤ) ∣ (w : ℤ) - ((M / 2 : ℕ) : ℤ) := by
      have hsub := dvd_sub h (dvd_refl (M : ℤ))
      have hM2eq : (M : ℤ) = 2 * ((M / 2 : ℕ) : ℤ) := by
        obtain ⟨m, hm⟩ := hM2
        omega
      rwa [show (w : ℤ) + ((M / 2 : ℕ) : ℤ) - M = (w : ℤ) - ((M / 2 : ℕ) : ℤ) by omega] at hsub
    exact hv1 (hwv'.symm.trans (Int.modEq_iff_dvd.mpr h').symm)
  obtain ⟨hsum, halt⟩ := sum_cyclicRoot_eq_zero_of_noncentral hM hM2 hw0 hw1
  rw [hgv, hneg, cyclicMultiplicity_inversion (basis.representation χ).character g hM hwlt]
  have hcast : ∀ j : ℕ, cyclicMultiplicity (basis.representation χ).character g M j =
      (L j : ℂ) := fun j => (multiplicityColumn_cast basis hM hg j χ).symm
  simp_rw [hcast]
  have hdec : ∀ j ∈ Finset.range M, (L j : ℂ) =
      ((L 1 + L 0 - η : ℤ) : ℂ) / 2 + ((L 0 - η - L 1 : ℤ) : ℂ) / 2 * (-1 : ℂ) ^ j +
        (if j = 0 then (η : ℂ) else 0) + (if j = M / 2 then ((η - θ : ℤ) : ℂ) else 0) := by
    intro j hj
    have hjM := Finset.mem_range.mp hj
    rcases Nat.even_or_odd j with he | ho
    · rw [he.neg_one_pow]
      by_cases h0 : j = 0
      · subst h0
        rw [ite_eq_left rfl, ite_eq_right (show (0 : ℕ) ≠ M / 2 by omega)]
        push_cast
        ring
      · by_cases hm : j = M / 2
        · rw [ite_eq_right h0, ite_eq_left hm]
          have h := hθ
          rw [← hm] at h
          simp only [hLdef]
          rw [h]
          push_cast
          ring
        · rw [ite_eq_right h0, ite_eq_right hm]
          simp only [hLdef]
          rw [hη j hjM he h0 hm]
          push_cast
          ring
    · rw [ho.neg_one_pow, ite_eq_right (by rintro rfl; exact absurd ho (by decide)),
        ite_eq_right (fun h : j = M / 2 => absurd (h ▸ ho) (Nat.not_odd_iff_even.mpr hM2'))]
      simp only [hLdef]
      rw [hodd j hjM ho]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun j hj => by rw [hdec j hj]]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_range, hM, ite_true, show M / 2 < M by omega]
  rw [hsum, halt]
  have hhalf : cyclicRoot M ^ (((M / 2 : ℕ) : ℤ) * (w : ℤ)) = (-1 : ℂ) ^ w := by
    rw [zpow_mul, zpow_natCast, zpow_natCast, cyclicRoot_pow_half hM hM2]
  rw [hhalf, Nat.cast_zero, zero_mul, zpow_zero]
  push_cast
  ring

section Twist

variable {G : Type*} [Group G] [Fintype G]

theorem multiplicityColumn_even_of_quarter {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (e : SemidihedralGroup n ≃* S) (basis : FiniteIrreducibleCharacterBasis G)
    (χ : basis.index) (η : ℤ)
    (h : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      multiplicityColumn basis (e (r n) : G) (modulus n) (2 * (l : ℤ)) χ =
        multiplicityColumn basis (e (r n) : G) (modulus n) 0 χ - η) :
    ∀ j : ℕ, j < modulus n → Even j → j ≠ 0 → j ≠ modulus n / 2 →
      multiplicityColumn basis (e (r n) : G) (modulus n) j χ =
        multiplicityColumn basis (e (r n) : G) (modulus n) 0 χ - η := by
  obtain ⟨hM, -, hK2, hhalf⟩ := modulus_eq_four_mul hn
  intro j hjM hje hj0 hjh
  obtain ⟨l, rfl⟩ := hje
  have hl : l + l = 2 * l := by ring
  rw [hl] at hjM hj0 hjh ⊢
  by_cases hle : l ≤ modulus n / 4 - 1
  · have h' := h l (by omega) hle
    push_cast
    exact h'
  ·
    set m := modulus n / 2 - l with hm
    have hm1 : 1 ≤ m := by omega
    have hm2 : m ≤ modulus n / 4 - 1 := by omega
    have htw := congrFun (supplied_multiplicityColumn_twist hn e basis (2 * (m : ℤ))) χ
    have hcong : (((modulus n / 2 : ℕ) : ℤ) - 1) * (2 * (m : ℤ)) ≡ ((2 * l : ℕ) : ℤ)
        [ZMOD modulus n] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨1 - (m : ℤ), ?_⟩
      have hmz : (m : ℤ) = ((modulus n / 2 : ℕ) : ℤ) - l := by omega
      have hMz : ((modulus n : ℕ) : ℤ) = 2 * ((modulus n / 2 : ℕ) : ℤ) := by omega
      rw [hmz, hMz]
      push_cast
      ring
    rw [← congrFun (multiplicityColumn_congr basis _ _ hcong) χ, htw]
    exact h m hm1 hm2

theorem multiplicityColumn_odd_of_transversal {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (e : SemidihedralGroup n ≃* S) (basis : FiniteIrreducibleCharacterBasis G)
    (χ : basis.index) {I : Finset (ZMod (modulus n))}
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I)
    (h : ∀ x ∈ I, multiplicityColumn basis (e (r n) : G) (modulus n) (x.val : ℤ) χ =
      multiplicityColumn basis (e (r n) : G) (modulus n) 1 χ) :
    ∀ j : ℕ, j < modulus n → Odd j →
      multiplicityColumn basis (e (r n) : G) (modulus n) j χ =
        multiplicityColumn basis (e (r n) : G) (modulus n) 1 χ := by
  obtain ⟨hM, -, hK2, hhalf⟩ := modulus_eq_four_mul hn
  have : NeZero (modulus n) := ⟨by omega⟩
  intro j hjM hjo
  set x : ZMod (modulus n) := (j : ZMod (modulus n)) with hx
  have hxval : x.val = j := ZMod.val_cast_of_lt hjM
  have hxodd : Odd x.val := hxval ▸ hjo
  have hpair := hI.pair x hxodd
  set a : ZMod (modulus n) := ((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1 with ha
  have hcases : x ∈ I ∨ a * x ∈ I := by
    by_contra hcon
    push Not at hcon
    have hempty : (({x, a * x} : Finset (ZMod (modulus n))) ∩ I) = ∅ := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        iff_false, not_and]
      rintro (rfl | rfl)
      · exact hcon.1
      · exact hcon.2
    rw [hempty, Finset.card_empty] at hpair
    exact absurd hpair (by norm_num)
  rcases hcases with hxI | haxI
  · have h' := h x hxI
    rw [hxval] at h'
    exact h'
  · have h' := h (a * x) haxI
    have haval : a.val = 2 * 2 ^ (n - 3) - 1 := supplied_twist_val hn
    have hcong : (((a * x).val : ℕ) : ℤ) ≡ (((modulus n / 2 : ℕ) : ℤ) - 1) * (j : ℤ)
        [ZMOD modulus n] := by
      rw [ZMod.val_mul, haval, hxval]
      have h1 : (((2 * 2 ^ (n - 3) - 1) * j % modulus n : ℕ) : ℤ) ≡
          (((2 * 2 ^ (n - 3) - 1) * j : ℕ) : ℤ) [ZMOD modulus n] := by
        exact_mod_cast Nat.mod_modEq _ _
      refine h1.trans ?_
      rw [show ((modulus n / 2 : ℕ) : ℤ) - 1 = (((2 * 2 ^ (n - 3) - 1 : ℕ)) : ℤ) by
        rw [show modulus n / 2 = 2 * 2 ^ (n - 3) by omega]
        push_cast [Nat.cast_sub (show 1 ≤ 2 * 2 ^ (n - 3) by omega)]
        ring]
      push_cast
      rfl
    rw [congrFun (multiplicityColumn_congr basis _ _ hcong) χ] at h'
    have htw := congrFun (supplied_multiplicityColumn_twist hn e basis (j : ℤ)) χ
    rw [htw] at h'
    exact h'

end Twist

theorem quarter_rotation_facts {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (e : SemidihedralGroup n ≃* S) :
    orderOf ((e (r n) : G) ^ (modulus n / 4)) = 4 ∧
      IsConj ((e (r n) : G) ^ (modulus n / 4)) ((e (r n) : G) ^ (modulus n / 4))⁻¹ ∧
      ((e (r n) : G) ^ (modulus n / 4)) ^ 2 = (e (r n) : G) ^ (modulus n / 2) := by
  obtain ⟨hM, -, hK2, hhalf⟩ := modulus_eq_four_mul hn
  have hord : orderOf (e (r n) : G) = modulus n := supplied_orderOf_r (by omega) e
  have hM4 : modulus n / 4 = 2 ^ (n - 3) := by omega
  refine ⟨?_, ?_, ?_⟩
  · have h := orderOf_pow_orderOf_div (x := (e (r n) : G)) (n := 4) (by rw [hord]; omega)
      (by rw [hord, hM]; exact dvd_mul_right 4 _)
    rwa [hord] at h
  · refine isConj_iff.mpr ⟨(e (s n) : G), ?_⟩
    rw [← conj_pow, supplied_s_conj_r e, ← pow_mul]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    have hexp : (2 ^ (n - 2) - 1) * (modulus n / 4) + modulus n / 4 =
        modulus n * 2 ^ (n - 4) := by
      rw [hM4, hM]
      have h3 : n - 3 = (n - 4) + 1 := by omega
      have h2 : n - 2 = (n - 4) + 2 := by omega
      rw [h2, h3]
      have hpos : 1 ≤ 2 ^ (n - 4 + 2) := Nat.one_le_two_pow
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega))]
      ring
    rw [hexp, pow_mul, supplied_r_pow_modulus e, one_pow]
  · rw [← pow_mul]
    congr 1
    omega

theorem degree_congruence_of_quarter_rotation {G : Type*} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (e : SemidihedralGroup n ≃* S) (basis : FiniteIrreducibleCharacterBasis G)
    (c : basis.index) (a b : ℤ)
    (hu : (basis.representation c).character ((e (r n) : G) ^ (modulus n / 4)) = a)
    (ht : (basis.representation c).character ((e (r n) : G) ^ (modulus n / 2)) = b) :
    (Module.finrank ℂ (basis.representation c).vector : ℤ) + b - 2 * a ≡ 0 [ZMOD 8] := by
  obtain ⟨hord, hconj, hsq⟩ := quarter_rotation_facts hn e
  obtain ⟨-, -, k, hk⟩ := no_index_two_real_order_four_degree_congruence hindex
    (basis.representation c).representation hord hconj
  have hk' : ((Module.finrank ℂ (basis.representation c).vector : ℤ) + b - 2 * a : ℤ) =
      8 * k := by
    have h1 : (basis.representation c).representation.character 1 =
        (Module.finrank ℂ (basis.representation c).vector : ℂ) :=
      (basis_character_one basis c).1
    have hu' : (basis.representation c).representation.character
        ((e (r n) : G) ^ (modulus n / 4)) = a := hu
    have ht' : (basis.representation c).representation.character
        (((e (r n) : G) ^ (modulus n / 4)) ^ 2) = b := by rw [hsq]; exact ht
    rw [h1, hu', ht'] at hk
    exact_mod_cast hk
  rw [Int.modEq_zero_iff_dvd, hk']
  exact Dvd.intro k rfl

theorem actual_principal_rotation_values_and_congruences {G : Type} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {t : G} (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he1 : q % 4 = 1 → e = 1)
    (he3 : q % 4 = 3 → e = -1) (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    {S : Sylow 2 G} (e' : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) :
    (∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] → ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      (basis.representation χ₁).character ((e' (r n) : G) ^ v) = δ₁ ∧
      (basis.representation χ₂).character ((e' (r n) : G) ^ v) = -δ₂ * (-1 : ℂ) ^ v ∧
      (basis.representation χ₃).character ((e' (r n) : G) ^ v) = -δ₃ * (-1 : ℂ) ^ v) ∧
    (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) ≡ δ₁ * (2 - e * q) [ZMOD 8] ∧
    (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) ≡ -δ₂ * e * q [ZMOD 8] ∧
    (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) ≡ -δ₃ [ZMOD 8] := by
  obtain ⟨hlφ, hδ₁, hδ₂, hδ₃, -, hnd, -, -, -, -, -, hB, -, hodd, hsec, hrel⟩ := hfam
  obtain ⟨-, -, hf₃1, -, -, hδ₄', -, -, -⟩ := hdeg
  obtain ⟨hφ1, hφnc⟩ := family_character_nonconstant hnonab localBasis ideal localPrincipal q φ hlφ
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  let χ : basis.index → G → ℂ := fun c => (basis.representation c).character
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hχ₂B : χ₂ ∈ B := hmem χ₂ (by simp)
  have hχ₃B : χ₃ ∈ B := hmem χ₃ (by simp)
  have hχ₄B : χ₄ ∈ B := hmem χ₄ (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := hnd
  set f₁ := Module.finrank ℂ (basis.representation χ₁).vector
  set f₂ := Module.finrank ℂ (basis.representation χ₂).vector
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector
  have hf₁c : (basis.representation χ₁).character 1 = f₁ := (basis_character_one basis χ₁).1
  have hf₂c : (basis.representation χ₂).character 1 = f₂ := (basis_character_one basis χ₂).1
  have hf₃c : (basis.representation χ₃).character 1 = f₃ := (basis_character_one basis χ₃).1
  have he : e = 1 ∨ e = -1 := by
    obtain ⟨m, hm⟩ := hqodd
    rcases Nat.even_or_odd m with ⟨l, hl⟩ | ⟨l, hl⟩
    · exact Or.inl (he1 (by omega))
    · exact Or.inr (he3 (by omega))
  have hoddF : ∀ c ∈ B, (∃ d : ℕ, Odd d ∧ (basis.representation c).character 1 = d) ↔
      (c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃) := by
    intro c hc
    rw [← hodd c hc, (basis_character_one basis c).1]
    constructor
    · rintro ⟨d, hd, hcd⟩
      rwa [Nat.cast_injective hcd]
    · intro h
      exact ⟨_, h, rfl⟩
  let Φ : G → ℂ := fun g => if h : g ∈ C t then φ ⟨g, h⟩ else 0
  have hΦC : ∀ (y : G) (hy : y ∈ C t), Φ y = φ ⟨y, hy⟩ := fun y hy => by
    simp only [Φ, hy, dite_true]
  have hΦ1 : Φ 1 = q := by
    rw [hΦC 1 (one_mem _)]
    exact hφ1
  have hΦ : ∃ y₁ ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      ∃ y₂ ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
        Odd (orderOf y₁) ∧ Odd (orderOf y₂) ∧ Φ y₁ ≠ Φ y₂ := by
    rw [hcent]
    obtain ⟨y, hy, hyq⟩ := hφnc
    refine ⟨1, one_mem _, y, y.2, by simp, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact hy
    · rw [hΦ1, hΦC y y.2]
      exact fun h => hyq h.symm
  have hχ₁t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₁).character ((e' (r n) : G) ^ (modulus n / 2) * y) =
        δ₁ * e * Φ y := by
    rw [hcent]
    intro y hy hyo
    rw [hΦC y hy]
    exact (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).1
  have hχ₂t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₂).character ((e' (r n) : G) ^ (modulus n / 2) * y) =
        -δ₂ * e * Φ y := by
    rw [hcent]
    intro y hy hyo
    rw [hΦC y hy, (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).2.1]
    ring
  have hχ₃t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₃).character ((e' (r n) : G) ^ (modulus n / 2) * y) = -δ₃ := by
    rw [hcent]
    intro y hy hyo
    exact (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).2.2.1
  obtain ⟨-, -, hrel1, -⟩ := hrel 1 (by simp)
  rw [hf₁c, hf₂c, hf₃c] at hrel1
  have hdeg3 : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0 := by exact_mod_cast hrel1
  obtain ⟨-, hΘ, -, -, -, -, -, -⟩ :=
    nonsimple_principal_Fourier_odd_degree_product hindex hn e' basis ideal principal hprincipal
      χ₁ χ₂ χ₃ hχ₁B hχ₂B hχ₃B h01 h02 h03 h12 h13 h23 hoddF f₁ f₂ f₃ hf₁c hf₂c hf₃c q hq3 hqodd e
      δ₁ δ₂ δ₃ he hδ₁ hδ₂ hδ₃ Φ hΦ hΦ1 hχ₁t hχ₂t hχ₃t hdeg3
  obtain ⟨-, -, hΘapply, -, -, hE1, -, -, -, -, -, -, -, -, -, -,
    c₁', c₂', c₃', δ₁', δ₂', δ₃', εe, ψ', hc₁', -, -, h12', h13', -, hc₁p', -, -,
    hδ₁', -, -, -, -, hψmem', -, hEeq, hθcoef, hηcoef, -, -, hne0, -, hεsign⟩ :=
    even_cyclic_principal_Fourier_family hn e' basis ideal principal hprincipal
  beta_reduce at hΘapply hEeq hθcoef hηcoef hE1 hne0 hεsign
  set L := multiplicityColumn basis (e' (r n) : G) (modulus n)
  obtain ⟨hM4, hkeven, hk2, hhalf⟩ := modulus_eq_four_mul hn
  have hθours : ∀ c ∈ B, L 0 c - L ((modulus n / 2 : ℕ) : ℤ) c =
      (if c = principal then 1 else 0) + δ₁ * (if c = χ₁ then 1 else 0) +
        δ₂ * (if c = χ₂ then 1 else 0) + δ₃ * (if c = χ₃ then 1 else 0) := by
    intro c hc
    have h := coefficient_eq_of_combination_eq basis
      (fun d => ((L 0 d - L ((modulus n / 2 : ℕ) : ℤ) d : ℤ) : ℂ))
      (fun d => (((if d = principal then 1 else 0) + δ₁ * (if d = χ₁ then 1 else 0) +
        δ₂ * (if d = χ₂ then 1 else 0) + δ₃ * (if d = χ₃ then 1 else 0) : ℤ) : ℂ)) (by
          funext g
          rw [← hΘapply g, hΘ]
          simp [Finset.sum_add_distrib, add_mul, Finset.sum_ite_eq', hpB, hχ₁B, hχ₂B, hχ₃B,
            hprincipal]) hc
    exact_mod_cast h
  have hεe' : εe = -δ₁' := by
    rw [(basis_character_one basis c₁').1] at hεsign hne0
    rw [hεsign]
    exact neg_sign_one_add_mul_eq hδ₁' (basis_character_one basis c₁').2 hne0
  have hc₁'match : (c₁' = χ₁ ∧ δ₁' = δ₁) ∨ (c₁' = χ₂ ∧ δ₁' = δ₂) ∨ (c₁' = χ₃ ∧ δ₁' = δ₃) := by
    have h1 : δ₁' = (if c₁' = principal then 1 else 0) + δ₁ * (if c₁' = χ₁ then 1 else 0) +
        δ₂ * (if c₁' = χ₂ then 1 else 0) + δ₃ * (if c₁' = χ₃ then 1 else 0) := by
      rw [← hθours c₁' hc₁', hθcoef c₁' hc₁']
      simp [hc₁p', h12', h13']
    exact eq_of_coefficient_ne_zero (by rcases hδ₁' with h | h <;> omega) hc₁p' h12 h13 h23 h1
  have hsec1 := hsec 1 (by simp)
  simp only [OneMemClass.coe_one, mul_one, hφ1] at hsec1
  obtain ⟨hχ₁tv, hχ₂tv, hχ₃tv, hχ₄tv, hψtv, hνtv⟩ := hsec1
  obtain ⟨-, hvodd, hvinv⟩ :=
    cyclic_principal_Fourier_projection_values hn e' basis ideal principal hprincipal
  beta_reduce at hvodd hvinv
  have hk1 : 1 ≤ modulus n / 4 - 1 := by omega
  have hψ'deg : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      ¬ Odd (Module.finrank ℂ (basis.representation (ψ' l)).vector) := by
    intro l hl1 hl2 hodd'
    have h := hE1 l hl1 hl2
    rw [hEeq l hl1 hl2, hεe'] at h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at h
    rw [(basis_character_one basis c₁').1, (basis_character_one basis (ψ' l)).1] at h
    have hc₁'odd : Odd (Module.finrank ℂ (basis.representation c₁').vector) := by
      rw [hodd c₁' hc₁']
      rcases hc₁'match with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> simp [h']
    have hZ : (1 : ℤ) + δ₁' * (Module.finrank ℂ (basis.representation c₁').vector : ℤ) -
        δ₁' * (Module.finrank ℂ (basis.representation (ψ' l)).vector : ℤ) = 0 := by
      have h' : ((1 + δ₁' * (Module.finrank ℂ (basis.representation c₁').vector : ℤ) -
          δ₁' * (Module.finrank ℂ (basis.representation (ψ' l)).vector : ℤ) : ℤ) : ℂ) = 0 := by
        push_cast at h ⊢
        linear_combination h
      exact_mod_cast h'
    obtain ⟨a, ha⟩ := hc₁'odd
    obtain ⟨b, hb⟩ := hodd'
    rcases hδ₁' with h1 | h1 <;> rw [h1] at hZ <;> omega
  have hzt : (e' (z n) : G) = t := by
    rw [← hcent]
    show ((e' (r n ^ half n) : (S : Subgroup G)) : G) = _
    rw [map_pow, SubmonoidClass.coe_pow]
    congr 1
    show 2 ^ (n - 2) = modulus n / 2
    omega
  have htS : t ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hzt]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn)) (e'.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((e' w : (S : Subgroup G)) : G)) h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnv : ∀ c ∈ B, χ c t ≠ 0 := fun c hc =>
    CFSG.LyonsUnitaryFour.principal_block_character_ne_zero_of_centralizes_sylow basis ideal 2
      principal hprincipal c hc S t htS
  have hψ'1B : ψ' 1 ∈ B := (hψmem' 1 le_rfl hk1).1
  have hψ'1 : ψ' 1 ≠ principal ∧ ψ' 1 ≠ χ₁ ∧ ψ' 1 ≠ χ₂ ∧ ψ' 1 ≠ χ₃ := by
    have h := hψ'deg 1 le_rfl hk1
    rw [hodd _ hψ'1B] at h
    push Not at h
    exact h
  have hEt := (hvinv t t 1 (mul_one t) (Commute.one_right t) ht
    (by rw [orderOf_one]; exact odd_one)).2.1 1 le_rfl hk1
  rw [hEeq 1 le_rfl hk1, hεe'] at hEt
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at hEt
  have heq0 : (e : ℂ) * q ≠ 1 := by
    intro h
    have h' : e * (q : ℤ) = 1 := by exact_mod_cast h
    rcases he with rfl | rfl <;> omega
  have hc₁'χ₁ : c₁' = χ₁ ∧ δ₁' = δ₁ := by
    rcases hc₁'match with h | ⟨hc, hδ⟩ | ⟨hc, hδ⟩
    · exact h
    ·
      exfalso
      rw [hc, hδ] at hEt
      have hsq : (δ₂ : ℂ) * δ₂ = 1 := by rcases hδ₂ with h | h <;> rw [h] <;> norm_num
      have hval : (basis.representation (ψ' 1)).character t = δ₂ * (1 - e * q) := by
        have h := hEt
        rw [hχ₂tv] at h
        push_cast at h
        linear_combination (-(δ₂ : ℂ)) * h - ((basis.representation (ψ' 1)).character t +
          δ₂ * e * q) * hsq
      have hψ'list : ψ' 1 ∈ ({principal, χ₁, χ₂, χ₃, χ₄} ∪
          (Finset.Icc 1 (2 ^ (n - 3) - 1)).image ψ ∪ (Finset.range (2 ^ (n - 3))).image ν :
            Finset basis.index) := hB ▸ hψ'1B
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_image] at hψ'list
      obtain ⟨hp', h1', h2', h3'⟩ := hψ'1
      have hint : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
          ((a * (1 + e * q) : ℤ) : ℂ) ≠ ((b * (1 - e * q) : ℤ) : ℂ) := by
        intro a b ha hb h
        have h' : a * (1 + e * (q : ℤ)) = b * (1 - e * q) := by exact_mod_cast h
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases he with rfl | rfl <;>
          omega
      rcases hψ'list with ((h | h | h | h | h) | ⟨j, hj, hjeq⟩) | ⟨i, hi, hieq⟩
      · exact hp' h
      · exact h1' h
      · exact h2' h
      · exact h3' h
      · rw [h, hχ₄tv, hδ₄'] at hval
        have hZ : ((-δ₂ * (1 - e * q) : ℤ) : ℂ) = ((δ₂ * (1 - e * q) : ℤ) : ℂ) := by
          push_cast at hval ⊢
          exact hval
        have hZ' : -δ₂ * (1 - e * (q : ℤ)) = δ₂ * (1 - e * q) := by exact_mod_cast hZ
        rcases hδ₂ with rfl | rfl <;> rcases he with rfl | rfl <;> omega
      · rw [← hjeq, hψtv j hj] at hval
        exact hint δ₁ δ₂ hδ₁ hδ₂ (by push_cast; exact hval)
      · rw [← hieq, hνtv i hi] at hval
        exact hint (-δ₁) δ₂ (by rcases hδ₁ with h | h <;> rw [h] <;> norm_num) hδ₂
          (by push_cast; linear_combination hval)
    ·
      exfalso
      apply hnv (ψ' 1) hψ'1B
      rw [hc, hδ] at hEt
      have hsq : (δ₃ : ℂ) * δ₃ = 1 := by rcases hδ₃ with h | h <;> rw [h] <;> norm_num
      have h := hEt
      rw [hχ₃tv] at h
      push_cast at h
      show (basis.representation (ψ' 1)).character t = 0
      linear_combination (-(δ₃ : ℂ)) * h - ((basis.representation (ψ' 1)).character t + δ₃) * hsq
  obtain ⟨hc₁'eq, hδ₁'eq⟩ := hc₁'χ₁
  have hψ'avoid : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      ψ' l ≠ principal ∧ ψ' l ≠ χ₁ ∧ ψ' l ≠ χ₂ ∧ ψ' l ≠ χ₃ := by
    intro l hl1 hl2
    have h := hψ'deg l hl1 hl2
    rw [hodd _ (hψmem' l hl1 hl2).1] at h
    push Not at h
    exact h
  have hηχ : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      L 0 χ₁ - L (2 * (l : ℤ)) χ₁ = δ₁ ∧ L 0 χ₂ - L (2 * (l : ℤ)) χ₂ = 0 ∧
        L 0 χ₃ - L (2 * (l : ℤ)) χ₃ = 0 := by
    intro l hl1 hl2
    obtain ⟨-, ha1, ha2, ha3⟩ := hψ'avoid l hl1 hl2
    refine ⟨?_, ?_, ?_⟩
    · rw [hηcoef l hl1 hl2 χ₁ hχ₁B, hc₁'eq, hδ₁'eq]
      simp [Ne.symm h01, Ne.symm ha1]
    · rw [hηcoef l hl1 hl2 χ₂ hχ₂B, hc₁'eq]
      simp [Ne.symm h02, Ne.symm h12, Ne.symm ha2]
    · rw [hηcoef l hl1 hl2 χ₃ hχ₃B, hc₁'eq]
      simp [Ne.symm h03, Ne.symm h13, Ne.symm ha3]
  have hθχ : L 0 χ₁ - L ((modulus n / 2 : ℕ) : ℤ) χ₁ = δ₁ ∧
      L 0 χ₂ - L ((modulus n / 2 : ℕ) : ℤ) χ₂ = δ₂ ∧
      L 0 χ₃ - L ((modulus n / 2 : ℕ) : ℤ) χ₃ = δ₃ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hθours χ₁ hχ₁B]
      simp [Ne.symm h01, h12, h13]
    · rw [hθours χ₂ hχ₂B]
      simp [Ne.symm h02, Ne.symm h12, h23]
    · rw [hθours χ₃ hχ₃B]
      simp [Ne.symm h03, Ne.symm h13, Ne.symm h23]
  obtain ⟨I, hI⟩ := exists_isOddResidueTransversal (n := n) hn
  obtain ⟨hIcard, -, -, -, -, -, -, -, -, -, -, εo, ν', dν, hεo, -, hνinj', hνmem', hfeq, hφcoef,
    -⟩ := odd_cyclic_principal_Fourier_family hn e' basis ideal principal hprincipal I hI
  beta_reduce at hfeq hφcoef hνmem'
  have hpair : ∀ x y : basis.index, (x = χ₁ ∨ x = χ₂ ∨ x = χ₃) → (y = χ₁ ∨ y = χ₂ ∨ y = χ₃) →
      x ≠ y → (basis.representation x).character t = (basis.representation y).character t →
      Module.finrank ℂ (basis.representation x).vector =
        Module.finrank ℂ (basis.representation y).vector → False := by
    have hq0 : (q : ℤ) ≠ 0 := by omega
    have key12 : (basis.representation χ₁).character t = (basis.representation χ₂).character t →
        f₁ = f₂ → False := by
      intro hv hd
      rw [hχ₁tv, hχ₂tv] at hv
      have hv' : δ₁ * e * (q : ℤ) = -(δ₂ * e * q) := by exact_mod_cast hv
      rw [hd] at hdeg3
      rcases hδ₁ with rfl | rfl <;> rcases hδ₂ with rfl | rfl <;> rcases hδ₃ with rfl | rfl <;>
        rcases he with rfl | rfl <;> omega
    have key13 : (basis.representation χ₁).character t = (basis.representation χ₃).character t →
        False := by
      intro hv
      rw [hχ₁tv, hχ₃tv] at hv
      have hv' : δ₁ * e * (q : ℤ) = -δ₃ := by exact_mod_cast hv
      rcases hδ₁ with rfl | rfl <;> rcases hδ₃ with rfl | rfl <;> rcases he with rfl | rfl <;>
        omega
    have key23 : (basis.representation χ₂).character t = (basis.representation χ₃).character t →
        False := by
      intro hv
      rw [hχ₂tv, hχ₃tv] at hv
      have hv' : -(δ₂ * e * (q : ℤ)) = -δ₃ := by exact_mod_cast hv
      rcases hδ₂ with rfl | rfl <;> rcases hδ₃ with rfl | rfl <;> rcases he with rfl | rfl <;>
        omega
    intro x y hx hy hxy hv hd
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact hxy rfl
    · exact key12 hv hd
    · exact key13 hv
    · exact key12 hv.symm hd.symm
    · exact hxy rfl
    · exact key23 hv
    · exact key13 hv.symm
    · exact key23 hv.symm
    · exact hxy rfl
  have hν't : ∀ j ∈ I, χ (ν' j) t = χ (ν' 1) t := by
    intro j hj
    have hjodd : Odd ((j.val : ℕ) : ℤ) := by exact_mod_cast hI.odd j hj
    have h := (hvinv t t 1 (mul_one t) (Commute.one_right t) ht
      (by rw [orderOf_one]; exact odd_one)).2.2 _ hjodd
    rw [hfeq j hj] at h
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
    have hεo0 : (εo : ℂ) ≠ 0 := by rcases hεo with h | h <;> rw [h] <;> norm_num
    have h' := (mul_eq_zero.mp h).resolve_left hεo0
    exact sub_eq_zero.mp h'
  have hν'deg : ∀ j ∈ I, Module.finrank ℂ (basis.representation (ν' j)).vector = dν := by
    intro j hj
    have h := (hνmem' j hj).2.2
    rw [(basis_character_one basis (ν' j)).1] at h
    exact_mod_cast h
  have hν'avoid : ∀ j ∈ I, ν' j ≠ χ₁ ∧ ν' j ≠ χ₂ ∧ ν' j ≠ χ₃ := by
    have hnone : ∀ j₀ ∈ I, ¬ (ν' j₀ = χ₁ ∨ ν' j₀ = χ₂ ∨ ν' j₀ = χ₃) := by
      intro j₀ hj₀ hin
      have hcard : 1 < I.card := by rw [hIcard]; omega
      obtain ⟨j₁, hj₁, hj₁ne⟩ := Finset.exists_mem_ne hcard j₀
      have hne : ν' j₁ ≠ ν' j₀ := fun h => hj₁ne (hνinj' j₁ hj₁ j₀ hj₀ h)
      have hd₀odd : Odd dν := by
        rw [← hν'deg j₀ hj₀, hodd _ (hνmem' j₀ hj₀).1]
        rcases hin with h | h | h <;> simp [h]
      have hin₁ : ν' j₁ = χ₁ ∨ ν' j₁ = χ₂ ∨ ν' j₁ = χ₃ := by
        have h := (hodd _ (hνmem' j₁ hj₁).1).mp (by rw [hν'deg j₁ hj₁]; exact hd₀odd)
        rcases h with h | h
        · exact absurd h (hνmem' j₁ hj₁).2.1
        · exact h
      exact hpair (ν' j₁) (ν' j₀) hin₁ hin hne
        ((hν't j₁ hj₁).trans (hν't j₀ hj₀).symm)
        ((hν'deg j₁ hj₁).trans (hν'deg j₀ hj₀).symm)
    intro j hj
    have h := hnone j hj
    push Not at h
    exact h
  have hφχ : ∀ x ∈ I, ∀ c, (c = χ₁ ∨ c = χ₂ ∨ c = χ₃) → L (x.val : ℤ) c = L 1 c := by
    intro x hx c hc
    have h1I : (1 : ZMod (modulus n)) ∈ I := hI.one_mem
    have hcB : c ∈ B := by rcases hc with rfl | rfl | rfl <;> assumption
    have h := hφcoef x hx c hcB
    have hcx : c ≠ ν' x := by
      obtain ⟨h1, h2, h3⟩ := hν'avoid x hx
      rcases hc with rfl | rfl | rfl
      · exact Ne.symm h1
      · exact Ne.symm h2
      · exact Ne.symm h3
    have hc1 : c ≠ ν' 1 := by
      obtain ⟨h1, h2, h3⟩ := hν'avoid 1 h1I
      rcases hc with rfl | rfl | rfl
      · exact Ne.symm h1
      · exact Ne.symm h2
      · exact Ne.symm h3
    rw [ite_eq_right hcx, ite_eq_right hc1, sub_zero, mul_zero] at h
    linarith
  have hgM : (e' (r n) : G) ^ modulus n = 1 := supplied_r_pow_modulus e'
  have hMpos : 0 < modulus n := by omega
  have h4M : 4 ∣ modulus n := ⟨2 ^ (n - 3), hM4⟩
  have hval : ∀ (c : basis.index) (θ η : ℤ), (c = χ₁ ∨ c = χ₂ ∨ c = χ₃) →
      L 0 c - L ((modulus n / 2 : ℕ) : ℤ) c = θ →
      (∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 → L 0 c - L (2 * (l : ℤ)) c = η) →
      ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] → ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
        (basis.representation c).character ((e' (r n) : G) ^ v) =
          η + (η - θ) * (-1 : ℂ) ^ v := by
    intro c θ η hc hθc hηc v hv0 hv1
    exact character_zpow_of_multiplicities basis hMpos h4M hgM c θ η (by linarith [hθc])
      (multiplicityColumn_even_of_quarter hn e' basis c η
        (fun l hl1 hl2 => by linarith [hηc l hl1 hl2]))
      (multiplicityColumn_odd_of_transversal hn e' basis c hI (fun x hx => hφχ x hx c hc))
      v hv0 hv1
  have hrot : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] → ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      (basis.representation χ₁).character ((e' (r n) : G) ^ v) = δ₁ ∧
      (basis.representation χ₂).character ((e' (r n) : G) ^ v) = -δ₂ * (-1 : ℂ) ^ v ∧
      (basis.representation χ₃).character ((e' (r n) : G) ^ v) = -δ₃ * (-1 : ℂ) ^ v := by
    intro v hv0 hv1
    refine ⟨?_, ?_, ?_⟩
    · rw [hval χ₁ δ₁ δ₁ (Or.inl rfl) hθχ.1 (fun l hl1 hl2 => (hηχ l hl1 hl2).1) v hv0 hv1]
      ring
    · rw [hval χ₂ δ₂ 0 (Or.inr (Or.inl rfl)) hθχ.2.1 (fun l hl1 hl2 => (hηχ l hl1 hl2).2.1) v
        hv0 hv1]
      push_cast
      ring
    · rw [hval χ₃ δ₃ 0 (Or.inr (Or.inr rfl)) hθχ.2.2 (fun l hl1 hl2 => (hηχ l hl1 hl2).2.2) v
        hv0 hv1]
      push_cast
      ring
  refine ⟨hrot, ?_⟩
  have hq4 : ((modulus n / 4 : ℕ) : ℤ) = 2 ^ (n - 3) := by rw [hM4]; push_cast; omega
  have hv4_0 : ¬ ((modulus n / 4 : ℕ) : ℤ) ≡ 0 [ZMOD modulus n] := by
    intro h
    have h' := Int.ModEq.dvd h.symm
    rw [sub_zero] at h'
    have := Int.le_of_dvd (by omega) h'
    omega
  have hv4_1 : ¬ ((modulus n / 4 : ℕ) : ℤ) ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
    intro h
    have h' := Int.ModEq.dvd h
    have hlt : (((modulus n / 2 : ℕ) : ℤ) - ((modulus n / 4 : ℕ) : ℤ)) < (modulus n : ℤ) := by
      omega
    have hpos : 0 < (((modulus n / 2 : ℕ) : ℤ) - ((modulus n / 4 : ℕ) : ℤ)) := by omega
    have := Int.le_of_dvd hpos h'
    omega
  obtain ⟨hu1, hu2, hu3⟩ := hrot _ hv4_0 hv4_1
  rw [zpow_natCast] at hu1 hu2 hu3
  have hev4 : Even ((modulus n / 4 : ℕ) : ℤ) := by
    rw [hq4]
    exact (Int.even_pow' (by omega)).mpr even_two
  rw [hev4.neg_one_zpow] at hu2 hu3
  have hc1 := degree_congruence_of_quarter_rotation hindex hn e' basis χ₁ δ₁ (δ₁ * e * q)
    (by rw [hu1]) (by rw [hcent, hχ₁tv]; push_cast; ring)
  have hc2 := degree_congruence_of_quarter_rotation hindex hn e' basis χ₂ (-δ₂) (-(δ₂ * e * q))
    (by rw [hu2]; push_cast; ring) (by rw [hcent, hχ₂tv]; push_cast; ring)
  have hc3 := degree_congruence_of_quarter_rotation hindex hn e' basis χ₃ (-δ₃) (-δ₃)
    (by rw [hu3]; push_cast; ring) (by rw [hcent, hχ₃tv, Int.cast_neg])
  simp only [Int.ModEq] at hc1 hc2 hc3 ⊢
  have hqmod : q % 4 = 1 ∨ q % 4 = 3 := by obtain ⟨m, hm⟩ := hqodd; omega
  refine ⟨?_, ?_, ?_⟩
  · rcases hδ₁ with rfl | rfl <;> rcases he with rfl | rfl <;> omega
  · rcases hqmod with hq | hq
    · have he' := he1 hq
      subst he'
      rcases hδ₂ with rfl | rfl <;> omega
    · have he' := he3 hq
      subst he'
      rcases hδ₂ with rfl | rfl <;> omega
  · rcases hδ₃ with rfl | rfl <;> omega

end CFSG.Semidihedral.Principal
