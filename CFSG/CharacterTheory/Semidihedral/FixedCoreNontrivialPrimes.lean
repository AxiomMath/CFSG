module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialPrimesLocal
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialPrimesSetup
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialPrimesArith
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterNineNonregularOrderSupport

public section

namespace CFSG.Semidihedral.FixedCoreNontrivialPrimes

open scoped BigOperators Classical

open CFSG.TwoRankLowerBound.Helpers CFSG.CyclicBlocks CFSG.Semidihedral.Principal
open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.LyonsUnitaryFour

theorem distinguished_eq_chi_three {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal₂ : Ideal ComplexAlgebraicIntegers)
    [ideal₂.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (χ₁ χ₂ χ₃ : basis.index) {q : ℕ} (hq : 3 ≤ q) {δ₁ δ₂ δ₃ e : ℤ}
    (hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1)
    (he : e = 1 ∨ e = -1)
    (hodd2 : ∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal,
      Odd (Module.finrank ℂ (basis.representation θ).vector) ↔
        θ = principal ∨ θ = χ₁ ∨ θ = χ₂ ∨ θ = χ₃)
    {y : G} (h₁ : (basis.representation χ₁).character y = δ₁ * e * q)
    (h₂ : (basis.representation χ₂).character y = -(δ₂ * e * q))
    (h₃ : (basis.representation χ₃).character y = -δ₃)
    {a b : basis.index} {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) (hap : a ≠ principal)
    (hbp : b ≠ principal)
    (hareal : ∀ g, starRingEnd ℂ ((basis.representation a).character g) =
      (basis.representation a).character g)
    (hbreal : ∀ g, starRingEnd ℂ ((basis.representation b).character g) =
      (basis.representation b).character g)
    (hdeg : (Module.finrank ℂ (basis.representation b).vector : ℤ) =
      Module.finrank ℂ (basis.representation a).vector + δ)
    (hay : (basis.representation a).character y = δ)
    {ζ ζ' : ℂ} (hby : (basis.representation b).character y = δ * (ζ + ζ'))
    (hζ : ‖ζ‖ = 1) (hζ' : ‖ζ'‖ = 1) (hζne : ∀ c : ℂ, (c = 1 ∨ c = -1) → ζ + ζ' ≠ c) :
    a = χ₃ ∧ δ = -δ₃ := by
  have hmem : ∀ θ, (∀ g, starRingEnd ℂ ((basis.representation θ).character g) =
      (basis.representation θ).character g) →
      Odd (Module.finrank ℂ (basis.representation θ).vector) → θ ≠ principal →
        θ = χ₁ ∨ θ = χ₂ ∨ θ = χ₃ := by
    intro θ hθr hθo hθp
    have hθB := real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal₂
      principal hprincipal θ hθr hθo
    rcases (hodd2 θ hθB).mp hθo with h | h
    · exact absurd h hθp
    · exact h
  have hsignnorm : ∀ u : ℤ, (u = 1 ∨ u = -1) → ‖(u : ℂ)‖ = 1 := by
    intro u hu
    rcases hu with rfl | rfl <;> simp
  have hq2 : (2 : ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  have hn₁ : ‖(basis.representation χ₁).character y‖ = q := by
    rw [h₁, norm_mul, norm_mul, hsignnorm δ₁ hδ₁, hsignnorm e he, Complex.norm_natCast]
    ring
  have hn₂ : ‖(basis.representation χ₂).character y‖ = q := by
    rw [h₂, norm_neg, norm_mul, norm_mul, hsignnorm δ₂ hδ₂, hsignnorm e he,
      Complex.norm_natCast]
    ring
  have hna : ‖(basis.representation a).character y‖ = 1 := by
    rw [hay]
    exact hsignnorm δ hδ
  have hnb : ‖(basis.representation b).character y‖ ≤ 2 := by
    rw [hby, norm_mul, hsignnorm δ hδ, one_mul]
    calc ‖ζ + ζ'‖ ≤ ‖ζ‖ + ‖ζ'‖ := norm_add_le _ _
      _ = 2 := by rw [hζ, hζ']; norm_num
  have hδsq : (δ : ℂ) * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have haodd : Odd (Module.finrank ℂ (basis.representation a).vector) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have hbodd : Odd (Module.finrank ℂ (basis.representation b).vector) := by
      have hδodd : Odd δ := by rcases hδ with rfl | rfl <;> decide
      have h := (Int.even_coe_nat _).mpr hev |>.add_odd hδodd
      rw [← hdeg] at h
      exact (Int.odd_coe_nat _).mp h
    rcases hmem b hbreal hbodd hbp with h | h | h
    · rw [h, hn₁] at hnb
      linarith
    · rw [h, hn₂] at hnb
      linarith
    · rw [h, h₃] at hby
      apply hζne (-δ * δ₃) (by rcases hδ with rfl | rfl <;> rcases hδ₃ with rfl | rfl <;> simp)
      linear_combination (-(δ : ℂ)) * hby - (ζ + ζ') * hδsq
  rcases hmem a hareal haodd hap with h | h | h
  · rw [h, hn₁] at hna
    exfalso
    linarith
  · rw [h, hn₂] at hna
    exfalso
    linarith
  · refine ⟨h, ?_⟩
    rw [h, h₃] at hay
    exact_mod_cast (by linear_combination -hay : (δ : ℂ) = -δ₃)

theorem sum_class_weight_expand {ι : Type*} (s : Finset ι) (A B Z D : ι → ℂ) (c d : ℂ) :
    ∑ i ∈ s, (A i / c + B i / d) * (A i / c + B i / d) * Z i / D i =
      1 / c ^ 2 * ∑ i ∈ s, A i * A i * Z i / D i +
        2 / (c * d) * ∑ i ∈ s, A i * B i * Z i / D i +
          1 / d ^ 2 * ∑ i ∈ s, B i * B i * Z i / D i := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem brauer_local_side {G : Type} [Group G] [Fintype G] {n : ℕ} (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) {t : G} (ht2 : orderOf t = 2)
    (hcent : (fS (r n) : G) ^ (modulus n / 2) = t)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ]
    (hℓ : 5 ≤ ℓ) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (Q : Sylow ℓ (C t)) (hQn : (Q : Subgroup (C t)).Normal)
    (hcomm : ∀ x ∈ (Q : Subgroup (C t)), ∀ y ∈ (Q : Subgroup (C t)), x * y = y * x)
    (hindex : (Subgroup.centralizer (Q : Set (C t))).index = 2)
    (hinv : ∀ x ∈ (Q : Subgroup (C t)), (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = (x : G)⁻¹)
    {w : C t} (hwQ : w ∈ (Q : Subgroup (C t))) (hw1 : w ≠ 1)
    (hEH : extendedCentralizer (w : G) ≤ C t) :
    (Nat.card G : ℂ) * ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation θ).character t * (basis.representation θ).character t *
          (basis.representation θ).character w / (basis.representation θ).character 1 =
      2 * (Nat.card (C t) : ℂ) ^ 3 /
        (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer ({(fS (s n) : G)} : Set G) : Subgroup G) : ℂ) ^ 2 := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hℓ2 : ℓ ≠ 2 := by omega
  set sC := centeredReflection hn fS hcent with hsCdef
  set tC := tInC t with htCdef
  set K := Subgroup.centralizer (Q : Set (C t)) with hK
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_orderOf_dvd_pow (⟨w, hwQ⟩ : (Q : Subgroup (C t)))
  have hu : orderOf (w : G) ∣ ℓ ^ k := by
    rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk w hwQ]
    exact hk
  have hform := (brauer_principal_order_formula basis ideal ℓ principal hprincipal htt htt (C t) w
    k hu hEH localBasis localPrincipal hlocalPrincipal).1 1 (Subgroup.one_mem _)
    (by rw [orderOf_one]; exact Nat.coprime_one_right ℓ)
  simp only [mul_one] at hform
  rw [hform]
  have hcw : ∀ ψ : localBasis.index,
      classWeight (C t) (localBasis.representation ψ).character t =
        (localBasis.representation ψ).character tC / Nat.card (C t) +
          (localBasis.representation ψ).character sC /
            Nat.card (Subgroup.centralizer ({sC} : Set (C t))) := fun ψ =>
    classWeight_centered hn S fS hG fS hcent _ (fun x y =>
      Representation.char_conj (localBasis.representation ψ).representation x y)
  simp_rw [hcw]
  rw [sum_class_weight_expand]
  have hinvC : ∀ x ∈ (Q : Subgroup (C t)), sC * x * sC⁻¹ = x⁻¹ := fun x hx =>
    Subtype.ext (by simpa [hsCdef, coe_centeredReflection] using hinv x hx)
  have htreg : ¬ ℓ ∣ orderOf tC := by
    rw [← Subgroup.orderOf_coe, show ((tC : C t) : G) = t from rfl, ht2]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hsreg : ¬ ℓ ∣ orderOf sC := by
    rw [← Subgroup.orderOf_coe, hsCdef, coe_centeredReflection, Subgroup.orderOf_coe,
      MulEquiv.orderOf_eq, orderOf_s n (by omega)]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have htK : tC ∈ K := by
    rw [Subgroup.mem_centralizer_iff]
    intro x _
    exact (Subgroup.mem_center_iff.mp (tInC_central t) x)
  have hsK : sC ∉ K := by
    intro hs
    have h1 := hinvC w hwQ
    rw [show sC * w * sC⁻¹ = w by
      rw [(Subgroup.mem_centralizer_iff.mp hs w hwQ).symm, mul_inv_cancel_right]] at h1
    have hodd : Odd (orderOf w) := by
      have hk' : orderOf w ∣ ℓ ^ k := by
        rw [← Subgroup.orderOf_mk w hwQ]
        exact hk
      exact Odd.of_dvd_nat ((hp.eq_two_or_odd'.resolve_left hℓ2).pow) hk'
    exact hw1 (StationaryConfinement.eq_one_of_eq_inv_of_odd hodd h1)
  have hS := fun (x₁ x₂ : C t) (hx₁ : ¬ ℓ ∣ orderOf x₁) (hx₂ : ¬ ℓ ∣ orderOf x₂) =>
    normal_abelian_inverted_sylow_principal_sum localBasis ideal ℓ hℓ localPrincipal
      hlocalPrincipal Q hQn hcomm hindex sC hinvC hx₁ hx₂ hwQ hw1
  rw [hS tC tC htreg htreg, hS tC sC htreg hsreg, hS sC sC hsreg hsreg]
  simp only [← hK, htK, hsK, ↓reduceIte]
  rw [card_centralizer_centeredReflection hn fS hcent]
  ring

theorem trivial_fixed_core_primes_aux
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 9 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (N t) → ℓ ∣ p ^ f * (p ^ f - 1) * (p ^ f + 1) := by
  classical
  intro ℓ hℓ hℓN
  by_contra hℓq
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨hℓ5, Q, hQN, hQn, hQcomm, hQcent, hQinv, ⟨Q', hQ'⟩, hQnorm, hNQ, hCQ⟩ :=
    trivial_fixed_core_sylow_setup G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f
      hp hpodd hf hq hmodel hcov hY hA₀ ℓ hℓ hℓN hℓq
  let _ : Fintype G := Fintype.ofFinite G
  have hℓ2 : ℓ ≠ 2 := by omega
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨-, ht2, hcent, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  set s₀ : G := (fS (s n) : G) with hs₀
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal₂, hmax₂, h2⟩, hchar₂⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal₂.IsMaximal := hmax₂
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2 := hchar₂ ideal₂ hmax₂ h2
  obtain ⟨⟨idealℓ, hmaxℓ, hℓm⟩, hcharℓ⟩ := CFSG.BlockBasics.residue_prime_existence ℓ hℓ
  have : idealℓ.IsMaximal := hmaxℓ
  have : CharP (ComplexAlgebraicIntegers ⧸ idealℓ) ℓ := hcharℓ idealℓ hmaxℓ hℓm
  have hprinB : principal ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ)
      principal := coefficientBlock_self_mem _ _ _
  obtain ⟨F, hF, hFfin, ρ, hFcard, -, -, -, hrest⟩ :=
    actual_simple_layer_principal_order_formulas hGnonab n hn S fS t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal₂ basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  obtain ⟨hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg, -, hOFall⟩ := hrest
  have hOF := hOFall S fS hcent
  have hq3 : 3 ≤ Nat.card F := by omega
  have hqoddF : Odd (Nat.card F) := hFcard ▸ hpodd.pow
  have hq11 : 11 ≤ Nat.card F := by
    obtain ⟨k, hk⟩ := hqoddF
    omega
  have he1 : Nat.card F % 4 = 1 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 :=
    fun h => by simp [h]
  have he3 : Nat.card F % 4 = 3 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 :=
    fun h => by simp [show ¬ Nat.card F % 4 = 1 by omega]
  obtain ⟨-, -, -, hc₃⟩ := actual_principal_rotation_values_and_congruences hG hn ht2 hnonab
    basis ideal₂ principal hprincipal localBasis localPrincipal (Nat.card F) hq3 hqoddF _ he1 he3
    _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg fS hcent
  obtain ⟨-, hδ₁, hδ₂, hδ₃, -, -, -, -, -, -, -, -, -, hodd2, hsec, hrel⟩ := hfam
  obtain ⟨hf₁1, hf₂1, hf₃1, -, hsign, -, -, hprod, -⟩ := hdeg
  obtain ⟨hden₁, hden₂, hg₁, hg₂⟩ := hOF
  have he : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 ∨
      (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    split_ifs <;> simp
  obtain ⟨-, -, hrel1, -⟩ := hrel 1 (by rw [orderOf_one]; exact odd_one)
  rw [(basis_character_one basis χ₁).1, (basis_character_one basis χ₂).1,
    (basis_character_one basis χ₃).1] at hrel1
  have hsum : 1 + δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
      δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) +
      δ₃ * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) = 0 := by
    have h : (((1 + δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
        δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) +
        δ₃ * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) : ℤ)) : ℂ) = 0 := by
      push_cast
      exact hrel1
    exact_mod_cast h
  have hQ'mem : ∀ x : G, x ∈ (Q' : Subgroup G) → ∃ hx : x ∈ C t,
      (⟨x, hx⟩ : C t) ∈ (Q : Subgroup (C t)) := by
    intro x hx
    rw [hQ'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y.2, hy⟩
  have hP : InvertedAbelianSylow Q' s₀ := by
    refine ⟨fun x hx y hy => ?_, ?_, ?_, fun x hx => ?_⟩
    · obtain ⟨hxC, hxQ⟩ := hQ'mem x hx
      obtain ⟨hyC, hyQ⟩ := hQ'mem y hy
      exact congrArg Subtype.val (hQcomm _ hxQ _ hyQ)
    · change (Subgroup.centralizer ((Q' : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer ((Q' : Subgroup G) : Set G)) = 2
      rw [hQ', hNQ, hCQ, Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (C t).subtype_injective]
      exact hY
    · change s₀ ∈ Subgroup.normalizer ((Q' : Subgroup G) : Set G)
      rw [hQ', hNQ]
      exact hsC
    · obtain ⟨hxC, hxQ⟩ := hQ'mem x hx
      exact hQinv _ hxQ
  have := hP.isMulCommutative
  obtain ⟨basisP⟩ := finiteIrreducibleCharacterBasis_exists (G := (Q' : Subgroup G))
  obtain ⟨principalP, hprincipalP⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    basisP (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalP
  obtain ⟨T, a, b, δ, hFam⟩ := inverted_family_exists basis idealℓ ℓ hℓ2 principal hprincipal Q'
    s₀ hP basisP principalP hprincipalP
  obtain ⟨k₀, hk₀⟩ := hFam.T_nonempty
  obtain ⟨w, hw1, hwne⟩ := exists_character_add_inv_ne_sign hℓ5 Q' basisP principalP
    hprincipalP (μ := k₀) (fun h => hFam.T_nontrivial (h ▸ hk₀))
  have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨hwC, hwQ⟩ := hQ'mem (w : G) w.2
  set wC : C t := ⟨(w : G), hwC⟩ with hwCdef
  have hwC1 : wC ≠ 1 := fun h => hw1' (congrArg Subtype.val h)
  have hwodd : Odd (orderOf wC) := by
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_orderOf_dvd_pow (⟨wC, hwQ⟩ : (Q : Subgroup (C t)))
    rw [← Subgroup.orderOf_mk wC hwQ]
    exact Odd.of_dvd_nat ((hℓ.eq_two_or_odd'.resolve_left hℓ2).pow) hk
  have htreg : ¬ ℓ ∣ orderOf t := by
    rw [ht2]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hwt : Commute (w : G) t := Subgroup.mem_centralizer_singleton_iff.mp hwC
  have hkappa : kappa t wC = kappa t 1 := by
    rw [map_one]
    apply (QuotientGroup.eq_one_iff wC).mpr
    obtain ⟨y, hyN, hy⟩ := hQN ⟨wC, hwQ, rfl⟩
    have hyw : y = wC := Subtype.ext hy
    rw [← hyw]
    exact Subgroup.mem_sup_left hyN
  obtain ⟨hχ₁w, hχ₂w, hχ₃w, -⟩ := hsec wC hwodd
  obtain ⟨-, -, hχ₃t, -⟩ := hsec 1 (by rw [orderOf_one]; exact odd_one)
  simp only [hkappa] at hχ₁w hχ₂w
  beta_reduce at hφ1
  rw [hφ1] at hχ₁w hχ₂w
  rw [Subgroup.coe_one, mul_one] at hχ₃t
  have hsect : ∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ) principal,
      (basis.representation θ).character (t * (w : G)) =
        (basis.representation θ).character (w : G) := by
    intro θ hθ
    rw [← hwt.eq]
    exact hP.principal_section_constant basis idealℓ hℓ2 principal hprincipal w.2 hw1' hwt
      htreg hθ
  have hay : (basis.representation a).character (t * (w : G)) = δ := by
    rw [hsect a hFam.mem_a]
    exact hFam.value_a w hw1
  have hby : (basis.representation (b ⟨k₀, hk₀⟩)).character (t * (w : G)) =
      δ * ((basisP.representation k₀).character w +
        (basisP.representation k₀).character w⁻¹) := by
    rw [hsect _ (hFam.mem_b _)]
    exact hFam.value_b ⟨k₀, hk₀⟩ w hw1
  have hroot : ∀ x : (Q' : Subgroup G), ‖(basisP.representation k₀).character x‖ = 1 := by
    intro x
    have hpow : (basisP.representation k₀).character x ^ Nat.card (Q' : Subgroup G) = 1 := by
      rw [← label_character_pow_of_comm, pow_card_eq_one', label_character_one_of_comm]
    exact Complex.norm_eq_one_of_pow_eq_one hpow Nat.card_pos.ne'
  obtain ⟨ha3, hδ3⟩ := distinguished_eq_chi_three basis ideal₂ principal hprincipal χ₁ χ₂ χ₃
    hq3 hδ₁ hδ₂ hδ₃ he hodd2 (y := t * (w : G)) hχ₁w hχ₂w hχ₃w hFam.sign hFam.a_ne
    (hFam.b_ne_principal _) hFam.real_a (hFam.real_b _) (hFam.deg_b _) hay hby (hroot w)
    (hroot w⁻¹) (hwne)
  have hEH : extendedCentralizer (wC : G) ≤ C t :=
    (ParameterNineNonregular.extendedCentralizer_le_normalizer_zpowers _).trans
      (hQnorm wC hwQ hwC1)
  have hindexQ : (Subgroup.centralizer (Q : Set (C t))).index = 2 := by
    rw [hQcent]
    exact hY
  have hBr := brauer_local_side hn S fS hG ht2 hcent basis idealℓ ℓ hℓ5 principal hprincipal Q
    hQn hQcomm hindexQ hQinv hwQ hwC1 hEH
  have hws := hFam.weighted_sum hℓ hprincipal hprinB htreg htreg w hw1
  change (Nat.card G : ℂ) * ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing idealℓ)
      principal, (basis.representation θ).character t * (basis.representation θ).character t *
        (basis.representation θ).character (w : G) / (basis.representation θ).character 1 = _
    at hBr
  rw [hws, ha3, hχ₃t, hδ3, (basis_character_one basis χ₃).1] at hBr
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector with hf₃def
  set c := Nat.card (C t) with hcdef
  set d := Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
    Subgroup.centralizer ({(fS (s n) : G)} : Set G) : Subgroup G) with hddef
  have hF0 : ((f₃ : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hF1 : (f₃ : ℂ) + ((-δ₃ : ℤ) : ℂ) ≠ 0 := by
    have : ((f₃ : ℤ) + -δ₃ : ℤ) ≠ 0 := by rcases hδ₃ with h | h <;> rw [h] <;> omega
    exact_mod_cast this
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [mul_div_assoc', div_eq_div_iff (mul_ne_zero hF0 hF1) (pow_ne_zero 2 hd0)] at hBr
  have hG₃ : (Nat.card G : ℤ) * ((f₃ : ℤ) + δ₃) ^ 2 * (d : ℤ) ^ 2 =
      2 * (c : ℤ) ^ 3 * ((f₃ : ℤ) * (f₃ - δ₃)) := by
    have h : (((Nat.card G : ℤ) * ((f₃ : ℤ) + δ₃) ^ 2 * (d : ℤ) ^ 2 : ℤ) : ℂ) =
        ((2 * (c : ℤ) ^ 3 * ((f₃ : ℤ) * (f₃ - δ₃)) : ℤ) : ℂ) := by
      push_cast at hBr ⊢
      linear_combination hBr
    exact_mod_cast h
  exact three_order_formulas_false hq11 he hsign hf₁1 hf₂1 hf₃1 hsum hprod hc₃ Nat.card_pos
    Nat.card_pos hden₁ hden₂ hg₁ hg₂ hG₃

end CFSG.Semidihedral.FixedCoreNontrivialPrimes

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem trivial_fixed_core_odd_core_primes_divide_characteristic_orders
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 9 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (N t) → ℓ ∣ p ^ f * (p ^ f - 1) * (p ^ f + 1) :=
  FixedCoreNontrivialPrimes.trivial_fixed_core_primes_aux G hGnonab hrecognition n hn S fS t ht
    hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hY hA₀

end CFSG.Semidihedral.FixedCoreNontrivial
