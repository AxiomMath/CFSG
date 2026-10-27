module

public import CFSG.CharacterTheory.Semidihedral.Principal.NormalPrimeDihedralEightInvolutionCounts
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFormula
public import CFSG.Adapters.LinearSmallCatalog

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

namespace PrimeTorusExclusion

theorem dvd_add_of_rotation_values {G : Type*} [Group G] (data : FiniteComplexRepresentation G)
    {r : G} {M : ℕ} (hMpos : 0 < M) (hM4 : 4 ∣ M) (hr : r ^ M = 1) (ε : ℤ)
    (ht : data.character (r ^ (M / 2)) = -ε)
    (hrot : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD M] → ¬ v ≡ ((M / 2 : ℕ) : ℤ) [ZMOD M] →
      data.character (r ^ v) = -ε * (-1 : ℂ) ^ v) :
    (M : ℤ) ∣ (Module.finrank ℂ data.vector : ℤ) + ε := by
  obtain ⟨m, hm⟩ := cyclicMultiplicity_natural data r hMpos hr 0
  unfold cyclicMultiplicity at hm
  simp only [zero_mul, neg_zero, zpow_zero, mul_one] at hm
  have hhalf : M / 2 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
  have hzero : 0 ∈ (Finset.range M).erase (M / 2) := by
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have hval : ∀ v ∈ ((Finset.range M).erase (M / 2)).erase 0,
      data.character (r ^ v) = -ε * (-1 : ℂ) ^ v := by
    intro v hv
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_range] at hv
    obtain ⟨hv0, hvh, hvM⟩ := hv
    have h := hrot (v : ℤ) (by
      intro hc
      have h1 : (v : ℤ) % M = 0 % M := hc
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.zero_emod] at h1
      omega) (by
      intro hc
      have h1 : (v : ℤ) % M = ((M / 2 : ℕ) : ℤ) % M := hc
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at h1
      omega)
    rw [zpow_natCast, zpow_natCast] at h
    exact h
  have hsign : ∑ v ∈ ((Finset.range M).erase (M / 2)).erase 0, (-1 : ℂ) ^ v = -2 := by
    have htot : ∑ v ∈ Finset.range M, (-1 : ℂ) ^ v = 0 := by
      rw [geom_sum_eq (by norm_num) M]
      obtain ⟨k, hk⟩ := hM4
      rw [hk, pow_mul]
      norm_num
    have hM2 : (-1 : ℂ) ^ (M / 2) = 1 := by
      obtain ⟨k, hk⟩ := hM4
      rw [show M / 2 = 2 * k by omega, pow_mul]
      norm_num
    rw [← Finset.add_sum_erase _ _ hhalf, ← Finset.add_sum_erase _ _ hzero, hM2, pow_zero] at htot
    linear_combination htot
  have hsum : ∑ v ∈ Finset.range M, data.character (r ^ v) =
      (Module.finrank ℂ data.vector : ℂ) + ε := by
    rw [← Finset.add_sum_erase _ _ hhalf, ← Finset.add_sum_erase _ _ hzero, ht, pow_zero,
      FiniteComplexRepresentation.character, Representation.char_one]
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum, hsign]
    ring
  rw [hsum] at hm
  have hM0' : (M : ℂ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have h : (((Module.finrank ℂ data.vector : ℤ) + ε : ℤ) : ℂ) = ((M * m : ℤ) : ℂ) := by
    push_cast
    rw [inv_mul_eq_iff_eq_mul₀ hM0'] at hm
    exact hm
  exact ⟨m, by exact_mod_cast h⟩

theorem card_eq_two_pow_mul_odd {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 3 ≤ n)
    (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* (S : Subgroup G)) (X : Subgroup G)
    (hSX : (S : Subgroup G) ≤ X) : ∃ g : ℕ, Odd g ∧ Nat.card X = 2 ^ n * g := by
  have hS : Nat.card (S : Subgroup G) = 2 ^ n := by
    rw [← Nat.card_congr fS.toEquiv, CFSG.Semidihedral.card n hn]
  have hcard := Subgroup.card_mul_index ((S : Subgroup G).subgroupOf X)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hS] at hcard
  refine ⟨((S : Subgroup G).subgroupOf X).index, ?_, hcard.symm⟩
  have hrel := Subgroup.relIndex_mul_index hSX
  have hodd : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
  rcases Nat.even_or_odd ((S : Subgroup G).subgroupOf X).index with h | h
  · exfalso
    apply hodd
    rw [← hrel]
    exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
  · exact h

theorem brauer_sum_of_prime_torus_normalizer {G : Type} [Group G] [Fintype G]
    (t : G) (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t)
    (W : Subgroup G) [IsCyclic W] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hW : Nat.card W = ℓ)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hdih : ∃ P : Sylow 2 (Subgroup.normalizer (W : Set G)),
      Nonempty ((P : Subgroup (Subgroup.normalizer (W : Set G))) ≃* DihedralGroup 4))
    (hR : (CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))).map
      (Subgroup.centralizer (W : Set G)).subtype = W)
    (d : ℕ) (hd : d = 4 ∨ d = 5)
    (hK : Nonempty ((Subgroup.centralizer (W : Set G) ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))) ≃* alternatingGroup (Fin d)))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {w : G} (hwW : w ∈ W)
    (hw1 : w ≠ 1) (hEH : extendedCentralizer w ≤ Subgroup.normalizer (W : Set G)) :
    (Nat.card G : ℂ) * ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation θ).character t * (basis.representation θ).character t *
          (basis.representation θ).character w / (basis.representation θ).character 1 =
      (Nat.card (Subgroup.normalizer (W : Set G)) : ℂ) *
        (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
          (if d = 4 then 1 / 8 else 1 / 72) := by
  have hp : ℓ.Prime := Fact.out
  set H := Subgroup.normalizer (W : Set G) with hHdef
  set K := Subgroup.centralizer (W : Set G) with hKdef
  have hWH : W ≤ H := Subgroup.le_normalizer
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  set W' : Subgroup H := W.subgroupOf H with hW'def
  have hW'n : W'.Normal := Subgroup.normal_in_normalizer
  have hW'card : Nat.card W' = ℓ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv, hW]
  have : IsCyclic W' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWH).symm.surjective
  have hcent : Subgroup.centralizer (W' : Set H) = K.subgroupOf H := by
    ext h
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh w hw
      exact congrArg Subtype.val (hh ⟨w, hWH hw⟩ hw)
    · intro hh w hw
      exact Subtype.ext (hh w hw)
  have hindex' : (Subgroup.centralizer (W' : Set H)).index = 2 := by
    rw [hcent]
    exact hKH
  let hKsub : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH'
  let φ : Subgroup.centralizer (W' : Set H) ≃* K :=
    (MulEquiv.subgroupCongr hcent).trans hKsub
  have hφval : ∀ x : Subgroup.centralizer (W' : Set H), ((φ x : K) : G) = ((x : H) : G) :=
    fun x => rfl
  have hmapN : (W'.subgroupOf (Subgroup.centralizer (W' : Set H))).map φ.toMonoidHom =
      CFSG.pPrimeCore 2 K := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxW : ((x : H) : G) ∈ W := hx
      rw [← hR] at hxW
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxW
      have : y = φ.toMonoidHom x := Subtype.ext (by
        change (y : G) = ((φ x : K) : G)
        rw [hφval]
        exact hyx)
      rw [← this]
      exact hy
    · intro hk
      refine ⟨φ.symm k, ?_, by simp⟩
      change (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) ∈ W
      have h1 : (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) = (k : G) := by
        rw [← hφval, MulEquiv.apply_symm_apply]
      rw [h1, ← hR]
      exact ⟨k, hk, rfl⟩
  obtain ⟨ψ⟩ := hK
  have hquot : Nonempty (Subgroup.centralizer (W' : Set H) ⧸
      W'.subgroupOf (Subgroup.centralizer (W' : Set H)) ≃* alternatingGroup (Fin d)) :=
    ⟨(QuotientGroup.congr _ _ φ hmapN).trans ψ⟩
  obtain ⟨-, -, -, -, hloc⟩ :=
    normal_prime_dihedral_eight_small_alternating_quotient_involution_counts ℓ hℓ W' hW'card
      hindex' hdih d hd hquot
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation H)
    (principalFiniteComplexRepresentation_isIrreducible H)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  have hlocal := hloc ideal localBasis localPrincipal hlocalPrincipal ⟨w, hWH hwW⟩ hwW
    (fun h => hw1 (congrArg Subtype.val h))
  have hwo : orderOf w = ℓ := by
    have hdvd : orderOf w ∣ ℓ := hW ▸ Subgroup.orderOf_dvd_natCard W hwW
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have ht2 : orderOf t = 2 := (hinvol t).mpr (IsConj.refl t)
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hwdvd : orderOf ((⟨w, hWH hwW⟩ : H) : G) ∣ ℓ ^ 1 := by
    change orderOf w ∣ ℓ ^ 1
    rw [hwo, pow_one]
  have hform := (brauer_principal_order_formula basis ideal ℓ principal hprincipal htt htt H
    ⟨w, hWH hwW⟩ 1 hwdvd hEH localBasis localPrincipal hlocalPrincipal).1 1 (Subgroup.one_mem _)
    (by rw [orderOf_one]; exact Nat.coprime_one_right ℓ)
  have hcw : ∀ ψ : H → ℂ, classWeight H ψ t =
      (Nat.card H : ℂ)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x : H => orderOf x = 2), ψ x := by
    intro ψ
    rw [classWeight, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : IsConj (x : G) t ↔ orderOf x = 2 := by rw [← hinvol, Subgroup.orderOf_coe]
    by_cases h : orderOf x = 2
    · rw [ite_eq_left (hx.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hx.mp h')), ite_eq_right h]
  have hlocal' : ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
      localPrincipal, classWeight H (localBasis.representation label).character t *
        classWeight H (localBasis.representation label).character t *
          (localBasis.representation label).character (⟨w, hWH hwW⟩ * 1) /
            (localBasis.representation label).character 1 =
      if d = 4 then 1 / 8 else 1 / 72 := by
    rw [← hlocal]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [hcw, mul_one, sq]
  rw [hlocal'] at hform
  simp only [mul_one] at hform
  change (Nat.card G : ℂ) * ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal, (basis.representation label).character t *
        (basis.representation label).character t * (basis.representation label).character w /
          (basis.representation label).character 1 = _ at hform
  rw [hform]
  ring

theorem local_quotient_gamma
    {G : Type} [Group G] (W K H : Subgroup G) (ℓ : ℕ)
    (hWℓ : Nat.card W = ℓ)
    (hcases : (Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
          Nat.card K = 12 * Nat.card W ∧ Nat.card H = 24 * Nat.card W) ∨
        (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
          Nat.card K = 60 * Nat.card W ∧ Nat.card H = 120 * Nat.card W)) :
    ∃ d : ℕ, (d = 4 ∨ d = 5) ∧
      Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin d)) ∧
      ∃ γn γd : ℤ, ((γn = 3 ∧ γd = 1) ∨ (γn = 5 ∧ γd = 3)) ∧
        (Nat.card H : ℂ) * (if d = 4 then 1 / 8 else 1 / 72) = γn * ℓ / γd := by
  rcases hcases with ⟨hA4, -, hH24⟩ | ⟨hmod, -, hH120⟩
  · refine ⟨4, Or.inl rfl, hA4, 3, 1, Or.inl ⟨rfl, rfl⟩, ?_⟩
    rw [hH24, hWℓ, ite_eq_left rfl]
    push_cast
    ring
  · obtain ⟨-, F, hF, hFfin, hFcard, ⟨eK⟩⟩ := hmod
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inr (by rw [hFcard]; norm_num))
    refine ⟨5, Or.inr rfl, ⟨eK.trans e5⟩, 5, 3, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [hH120, hWℓ, ite_eq_right (by norm_num)]
    push_cast
    ring

theorem mul_add_sign_pos {f ε : ℤ} (hf : 1 < f) (hε : ε = 1 ∨ ε = -1) : 0 < f * (f + ε) := by
  rcases hε with rfl | rfl <;> nlinarith

theorem integral_brauer_identity {cardG cardH c F ℓ : ℕ} {X δ γn γd : ℤ} {s : ℂ}
    (hγd : (γd : ℂ) ≠ 0) (hpos : (0 : ℤ) < F * (F + δ))
    (hBr : (cardG : ℂ) * (((F : ℂ) - X) * ((F : ℂ) - X) / ((F : ℂ) * ((F : ℂ) + δ))) =
      (cardH : ℂ) * (c : ℂ) ^ 2 * s)
    (hHs : (cardH : ℂ) * s = γn * ℓ / γd) :
    γd * (cardG : ℤ) * (F - X) ^ 2 = γn * ℓ * (c : ℤ) ^ 2 * (F * (F + δ)) := by
  have hne : ((F : ℂ) * (F + δ)) ≠ 0 := by
    have h : ((F : ℤ) * (F + δ) : ℤ) ≠ 0 := hpos.ne'
    exact_mod_cast h
  have h1 : (cardG : ℂ) * ((F - X) * (F - X)) = (cardH : ℂ) * (c : ℂ) ^ 2 * s * (F * (F + δ)) := by
    rw [← hBr, mul_assoc, div_mul_cancel₀ _ hne]
  have h2 : (γd : ℂ) * ((cardH : ℂ) * s) = γn * ℓ := by
    rw [hHs]
    field_simp
  have h : ((γd * (cardG : ℤ) * (F - X) ^ 2 : ℤ) : ℂ) =
      ((γn * ℓ * (c : ℤ) ^ 2 * (F * (F + δ)) : ℤ) : ℂ) := by
    push_cast
    linear_combination (γd : ℂ) * h1 + (c : ℂ) ^ 2 * (F * (F + δ)) * h2
  exact_mod_cast h

theorem cleared_order_formula {cardG c d : ℕ} {A B X Q E : ℚ} (hd : (d : ℚ) ≠ 0) (hX : X ≠ 0)
    (hQ : Q ≠ 0) (h : (cardG : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 * (A * B / X ^ 2) * (E / Q)) :
    (cardG : ℚ) * (d : ℚ) ^ 2 * (X ^ 2 * Q) = (c : ℚ) ^ 3 * (A * B * E) := by
  rw [h]
  field_simp

theorem case_alpha_one_false {G c d q e ℓ f ε γn γd : ℤ} (hc : c = 2 * q * (q ^ 2 - 1))
    (hdd : d = 2 * (q + e)) (h2ℓ : 2 * ℓ = q + e) (hq : 3 < q) (he : e = 1 ∨ e = -1)
    (hℓ : 7 ≤ ℓ) (hℓp : Prime ℓ) (hℓodd : Odd ℓ) (hf : 1 < f) (hfodd : Odd f)
    (hε : ε = 1 ∨ ε = -1) (hγ : (γn = 3 ∧ γd = 1) ∨ (γn = 5 ∧ γd = 3))
    (hBr : γd * G * (f - ε * e * q) ^ 2 = γn * ℓ * c ^ 2 * (f * (f - ε)))
    (hOF : G * d ^ 2 * ((f - e * ε * q) ^ 2 * q) = c ^ 3 * (f * (f + ε) * (q + e))) : False := by
  have hc0 : c ≠ 0 := by
    rw [hc]
    have : 0 < q ^ 2 - 1 := by nlinarith
    have : 0 < 2 * q * (q ^ 2 - 1) := by positivity
    exact this.ne'
  have hf0 : f ≠ 0 := by omega
  have h1 : (c ^ 2 * f) * (γd * c * ((f + ε) * (q + e))) =
      (c ^ 2 * f) * (d ^ 2 * q * γn * ℓ * (f - ε)) := by
    linear_combination (-γd) * hOF + d ^ 2 * q * hBr
  have h2 := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hc0) hf0) h1
  have hq0 : 2 * q * (q + e) ^ 2 ≠ 0 := by
    have : 0 < 2 * q * (q + e) ^ 2 := by
      rcases he with rfl | rfl
      · have : 0 < q + 1 := by omega
        positivity
      · have : 0 < q + -1 := by omega
        positivity
    exact this.ne'
  have h3 : γd * (q - e) * (f + ε) = 2 * γn * ℓ * (f - ε) := by
    rw [hc, hdd] at h2
    have h4 : (2 * q * (q + e) ^ 2) * (γd * (q - e) * (f + ε)) =
        (2 * q * (q + e) ^ 2) * (2 * γn * ℓ * (f - ε)) := by
      rcases he with rfl | rfl
      · linear_combination h2
      · linear_combination h2
    exact mul_left_cancel₀ hq0 h4
  have hℓ0 : 0 < ℓ := by omega
  have hdvd : ℓ ∣ γd * (q - e) * (f + ε) := ⟨2 * γn * (f - ε), by rw [h3]; ring⟩
  have hℓfε : ℓ ∣ f + ε := by
    rcases hℓp.dvd_or_dvd hdvd with h | h
    · exfalso
      rcases hℓp.dvd_or_dvd h with h' | h'
      · rcases hγ with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact hℓp.not_isUnit (isUnit_of_dvd_one h')
        · have := Int.le_of_dvd (by norm_num) h'
          omega
      · have h'' : ℓ ∣ 2 * e := by
          have hqe : q - e = 2 * ℓ - 2 * e := by omega
          rw [hqe] at h'
          have := (dvd_sub (dvd_mul_left ℓ 2) h')
          simpa using this
        rcases he with rfl | rfl
        · have := Int.le_of_dvd (by norm_num) h''
          omega
        · have h2' : ℓ ∣ 2 := by simpa using h''
          have := Int.le_of_dvd (by norm_num) h2'
          omega
    · exact h
  have heven : Even (f + ε) := by
    obtain ⟨m, hm⟩ := hfodd
    rcases hε with rfl | rfl
    · exact ⟨m + 1, by omega⟩
    · exact ⟨m, by omega⟩
  obtain ⟨j, hj⟩ := hℓfε
  have hjeven : Even j := by
    rw [hj] at heven
    rcases Int.even_mul.mp heven with h | h
    · exact absurd h (Int.not_even_iff_odd.mpr hℓodd)
    · exact h
  obtain ⟨k, hk'⟩ := hjeven
  have hk : f + ε = 2 * ℓ * k := by rw [hj, hk']; ring
  have hk1 : 1 ≤ k := by
    by_contra hk1
    push Not at hk1
    rcases hε with rfl | rfl <;> nlinarith
  have hfk : f = 2 * ℓ * k - ε := by linarith
  rw [hfk] at h3
  rcases he with rfl | rfl <;> rcases hε with rfl | rfl <;>
    rcases hγ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith

theorem case_alpha_two_false {G c d q e ℓ f ε γn γd : ℤ} (hc : c = 2 * q * (q ^ 2 - 1))
    (hdd : d = 2 * (q + e)) (h2ℓ : 2 * ℓ = q + e) (hq : 3 < q) (he : e = 1 ∨ e = -1)
    (hf : 1 < f) (hε : ε = 1 ∨ ε = -1) (hγ : (γn = 3 ∧ γd = 1) ∨ (γn = 5 ∧ γd = 3))
    (hBr : γd * G * (f + ε * e * q) ^ 2 = γn * ℓ * c ^ 2 * (f * (f + ε)))
    (hOF : G * d ^ 2 * ((f + e * ε * q) ^ 2 * q) = c ^ 3 * (f * (f + ε) * (q - e))) : False := by
  have hc0 : c ≠ 0 := by
    rw [hc]
    have : 0 < q ^ 2 - 1 := by nlinarith
    have : 0 < 2 * q * (q ^ 2 - 1) := by positivity
    exact this.ne'
  have hX0 : f * (f + ε) ≠ 0 := by
    have : 0 < f * (f + ε) := by rcases hε with rfl | rfl <;> nlinarith
    exact this.ne'
  have h1 : (c ^ 2 * (f * (f + ε))) * (γd * c * (q - e)) =
      (c ^ 2 * (f * (f + ε))) * (d ^ 2 * q * γn * ℓ) := by
    linear_combination (-γd) * hOF + d ^ 2 * q * hBr
  have h2 := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hc0) hX0) h1
  rw [hc, hdd] at h2
  have hq0 : 2 * q * (q + e) ≠ 0 := by
    have : 0 < 2 * q * (q + e) := by
      rcases he with rfl | rfl
      · have : 0 < q + 1 := by omega
        positivity
      · have : 0 < q + -1 := by omega
        positivity
    exact this.ne'
  have h3 : γd * (q - e) ^ 2 = 2 * γn * ℓ * (q + e) := by
    have h4 : (2 * q * (q + e)) * (γd * (q - e) ^ 2) =
        (2 * q * (q + e)) * (2 * γn * ℓ * (q + e)) := by
      rcases he with rfl | rfl
      · linear_combination h2
      · linear_combination h2
    exact mul_left_cancel₀ hq0 h4
  have hq' : q = 2 * ℓ - e := by linarith
  rw [hq'] at h3
  rcases he with rfl | rfl <;> rcases hγ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h5 : 1 = 2 * (ℓ ^ 2 + ℓ) := by linarith
    omega
  · have h5 : 3 = 2 * (ℓ ^ 2 + 3 * ℓ) := by linarith
    omega
  · have h5 : 1 = 2 * (ℓ ^ 2 - ℓ) := by linarith
    omega
  · have h5 : 3 = 2 * (ℓ ^ 2 - 3 * ℓ) := by linarith
    omega

theorem case_alpha_three_false {G c f ε ℓ γn γd : ℤ} {n : ℕ} (hn : 4 ≤ n)
    (hG : ∃ g : ℤ, Odd g ∧ G = 2 ^ n * g) (hc : ∃ c₀ : ℤ, Odd c₀ ∧ c = 2 ^ n * c₀)
    (hM : (2 : ℤ) ^ (n - 1) ∣ f + ε) (hfodd : Odd f) (hε : ε = 1 ∨ ε = -1) (hℓodd : Odd ℓ)
    (hγ : (γn = 3 ∧ γd = 1) ∨ (γn = 5 ∧ γd = 3))
    (hBr : γd * G * (f + ε) ^ 2 = γn * ℓ * c ^ 2 * (f * (f - ε))) : False := by
  obtain ⟨g, hg, rfl⟩ := hG
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  obtain ⟨k, hk⟩ := hM
  set Y : ℤ := 2 ^ (n - 4) with hYdef
  have hpn : (2 : ℤ) ^ n = 16 * Y := by
    rw [hYdef, ← show (2 : ℤ) ^ 4 = 16 by norm_num, ← pow_add]
    congr 1
    omega
  have hpn1 : (2 : ℤ) ^ (n - 1) = 8 * Y := by
    rw [hYdef, ← show (2 : ℤ) ^ 3 = 8 by norm_num, ← pow_add]
    congr 1
    omega
  have hY0 : Y ≠ 0 := by positivity
  rw [hpn1] at hk
  rw [hpn] at hBr
  have hfe : f - ε = 8 * Y * k - 2 * ε := by linarith
  rw [hk, hfe] at hBr
  have h1 : (512 * Y ^ 2) * (2 * γd * Y * g * k ^ 2) =
      (512 * Y ^ 2) * (γn * ℓ * c₀ ^ 2 * f * (4 * Y * k - ε)) := by
    linear_combination hBr
  have h2 := mul_left_cancel₀ (by positivity : (512 : ℤ) * Y ^ 2 ≠ 0) h1
  have hγodd : Odd γn := by
    rcases hγ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hlast : Odd (4 * Y * k - ε) := by
    rcases hε with rfl | rfl
    · exact ⟨2 * Y * k - 1, by ring⟩
    · exact ⟨2 * Y * k, by ring⟩
  have hodd : Odd (γn * ℓ * c₀ ^ 2 * f * (4 * Y * k - ε)) :=
    ((((hγodd.mul hℓodd).mul (hc₀.pow)).mul hfodd).mul hlast)
  have heven : Even (2 * γd * Y * g * k ^ 2) := ⟨γd * Y * g * k ^ 2, by ring⟩
  rw [h2] at heven
  exact (Int.not_even_iff_odd.mpr hodd) heven

end PrimeTorusExclusion

end CFSG.Semidihedral.Principal
