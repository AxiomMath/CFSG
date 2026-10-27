module

public import CFSG.CharacterTheory.Semidihedral.StationarySevenNine
public import CFSG.CharacterTheory.Semidihedral.StationarySevenNineRows
public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterNineNonregularOrderSupport

public section

open scoped Classical

namespace CFSG.Semidihedral.StationarySevenNine

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.Principal
open CFSG.TwoRankLowerBound.Helpers

theorem central_core_first_character_data {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (S : Sylow 2 G) (fS : SemidihedralGroup 5 ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r 5) : G) ^ 2 ^ (5 - 2))
    (hcenter : N t ≤ Subgroup.center (C t))
    (hN5 : Nat.card ((N t).map (C t).subtype) = 5)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = 9) (e : ℤ) (he : e = 1) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (5 - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hδ₁ : δ₁ = -1)
    (h1 : Module.finrank ℂ (basis.representation χ₁).vector ≠ 1)
    (h2 : Module.finrank ℂ (basis.representation χ₂).vector ≠
      Module.finrank ℂ (basis.representation χ₁).vector)
    (h3 : Module.finrank ℂ (basis.representation χ₃).vector ≠
      Module.finrank ℂ (basis.representation χ₁).vector)
    (h4 : Module.finrank ℂ (basis.representation χ₄).vector ≠
      Module.finrank ℂ (basis.representation χ₁).vector) :
    ∀ z ∈ (N t).map (C t).subtype, z ≠ 1 → ∃ d₀ m : ℕ, 0 < m ∧ 9 ≤ d₀ ∧
      Module.finrank ℂ (basis.representation χ₁).vector = d₀ + 4 * (16 * m) ∧
      (basis.representation χ₁).character z = (d₀ : ℂ) - (16 * m : ℕ) := by
  obtain ⟨-, ht2, -, -, -, -⟩ := supplied_t_s_facts (by norm_num) fS ht
  have hrat := family_first_character_rat basis ideal principal hprincipal t localBasis
    localPrincipal q e _ φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam h1 h2 h3 h4
  obtain ⟨⟨lφ, -, -, hlφchar, hlφdeg, -⟩, -, -, -, -, -, -, -, -, -, -, hB, -, -, hsec, -⟩ :=
    hfam
  have hχ₁B : χ₁ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
  have hφ1 : φ 1 = 9 := by
    rw [← hlφchar, (basis_character_one localBasis lφ).1, hlφdeg, hq]
    norm_num
  have hχt : (basis.representation χ₁).character t = -9 := by
    have h := (hsec 1 (by rw [orderOf_one]; exact odd_one)).1
    rw [OneMemClass.coe_one, mul_one, hφ1, hδ₁, he] at h
    rw [h]
    norm_num
  have hχtn : ‖(basis.representation χ₁).character t‖ = 9 := by
    rw [hχt]
    norm_num
  obtain ⟨Q, hQC, hQ2, hQ16, htQ, hQt⟩ := supplied_quaternion_sixteen S fS t ht
  have hAZ : ∀ a ∈ (N t).map (C t).subtype, a ∈ Subgroup.centralizer {t} ∧
      ∀ c ∈ Subgroup.centralizer {t}, a * c = c * a := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, fun c hc => ?_⟩
    have h := Subgroup.mem_center_iff.mp (hcenter hx) ⟨c, hc⟩
    exact (congrArg Subtype.val h).symm
  have hker : ∃ a ∈ (N t).map (C t).subtype, (basis.representation χ₁).character a ≠
      (basis.representation χ₁).character 1 := by
    have hne : (N t).map (C t).subtype ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hN5]
      norm_num
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨a, a.2, character_ne_degree_of_simple basis χ₁ h1 (fun h => ha1 (Subtype.ext h))⟩
  exact central_five_eigenspace_data basis ideal principal hprincipal hχ₁B hrat ht2 hχtn _ hAZ
    hN5 Q hQC hQ2 hQ16 htQ hQt hker

theorem parameter_nine_regular_of_central_core
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcenter : N t ≤ Subgroup.center (C t))
    (hN5 : Nat.card ((N t).map (C t).subtype) = 5)
    (hNs : (N t).map (C t).subtype ≤ Subgroup.centralizer ({(fS (s n) : G)} : Set G))
    (hconf : ∀ u ∈ (N t).map (C t).subtype, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ C t) :
    n = 5 ∧ Nat.card (C t) = 7200 ∧
      Nat.card ↥(C t ⊓ Subgroup.centralizer ({(fS (s n) : G)} : Set G)) = 100 ∧
      Nat.card G = 42573600 ∧ (C t).index = 5913 := by
  have : Fintype G := Fintype.ofFinite G
  have : Group.IsPerfect G := StationaryLayerCover.isPerfect_of_nonabelian hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal, hmax, h2⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg,
      -, hOF⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  obtain ⟨hn5, hq9, he1, hc, hd, hrows⟩ := local_parameter_nine_rows_of_family n hn S fS t ht
    hnonab hcentral hnc p f hp hpodd hf hq hmodel basis ideal principal hprincipal localBasis
    localPrincipal (Nat.card F) hcard _ rfl _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg
    (hOF S fS hcent)
  subst hn5
  obtain ⟨hcardA, hindexA⟩ := fixed_core_card_index t (fS (s 5) : G)
  have hNaA : (N t).map (C t).subtype =
      (N t).map (C t).subtype ⊓ Subgroup.centralizer ({(fS (s 5) : G)} : Set G) :=
    le_antisymm (le_inf le_rfl hNs) inf_le_left
  have ha5 : Nat.card (((Subgroup.centralizer {(fS (s 5) : G)}).comap (C t).subtype).subgroupOf
      (N t)) = 5 := by
    rw [hcardA, ← hNaA, hN5]
  have hb1 : (((Subgroup.centralizer {(fS (s 5) : G)}).comap (C t).subtype).subgroupOf
      (N t)).index = 1 := by
    rw [hindexA, ← hNaA]
    exact Subgroup.relIndex_self _
  rw [ha5, hb1] at hc hrows
  rw [ha5] at hd
  have hc' : Nat.card (C t) = 7200 := by
    rw [hc]
  have hd' : Nat.card ↥(C t ⊓ Subgroup.centralizer ({(fS (s 5) : G)} : Set G)) = 100 := by
    rw [hd]
  obtain ⟨-, -, -, -, -, -, hf₄, -, -⟩ := hdeg
  have hne : (N t).map (C t).subtype ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hN5]
    norm_num
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzN : (z : G) ∈ (N t).map (C t).subtype := z.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hdata := central_core_first_character_data S fS t ht hcenter hN5 basis ideal principal
    hprincipal localBasis localPrincipal (Nat.card F) hq9 _ he1 _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν
    hfam
  rcases hrows with ⟨-, -, -, -, -, -, hX⟩ | ⟨hδ₁, hδ₂, -, hf₁, hf₂, hf₃, -⟩ |
      ⟨hδ₁, hδ₂, -, hf₁, hf₂, hf₃, -⟩
  ·
    have hGc : Nat.card G = 42573600 := by
      have h := congrArg Prod.fst hX
      simp only at h
      rw [h]
      norm_num
    have hI : (C t).index = 5913 := by
      have h := congrArg Prod.snd hX
      simp only at h
      rw [h]
      norm_num
    exact ⟨rfl, hc', hd', hGc, hI⟩
  ·
    exfalso
    have hf₄' : Module.finrank ℂ (basis.representation χ₄).vector = 568 := by
      have h : (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) = 568 := by
        rw [hf₄, hf₂, hδ₂]
        norm_num
      exact_mod_cast h
    obtain ⟨d₀, m, hm, hd₀, hdeg71, -⟩ := hdata hδ₁ (by rw [hf₁]; norm_num)
      (by rw [hf₁, hf₂]; norm_num) (by rw [hf₁, hf₃]; norm_num) (by rw [hf₁, hf₄']; norm_num)
      (z : G) hzN hz1'
    rw [hf₁] at hdeg71
    omega
  ·
    exfalso
    have hf₄' : Module.finrank ℂ (basis.representation χ₄).vector = 200 := by
      have h : (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) = 200 := by
        rw [hf₄, hf₂, hδ₂]
        norm_num
      exact_mod_cast h
    obtain ⟨d₀, m, hm, hd₀, hdeg135, hval⟩ := hdata hδ₁ (by rw [hf₁]; norm_num)
      (by rw [hf₁, hf₂]; norm_num) (by rw [hf₁, hf₃]; norm_num) (by rw [hf₁, hf₄']; norm_num)
      (z : G) hzN hz1'
    rw [hf₁] at hdeg135
    have hm1 : m = 1 := by omega
    have hd71 : d₀ = 71 := by omega
    subst hm1 hd71
    have hχz : (basis.representation χ₁).character (z : G) = 55 := by
      rw [hval]
      norm_num
    obtain ⟨-, -, -, -, -, -, -, hνinj, -, -, -, -, -, -, -, hodd⟩ := hfam
    have hzodd : Odd (orderOf (z : G)) := by
      have h := Subgroup.orderOf_dvd_natCard _ hzN
      rw [hN5] at h
      exact (Nat.odd_iff.mpr rfl : Odd 5).of_dvd_nat h
    have hν : ∀ i ∈ Finset.range (2 ^ (5 - 3)),
        (basis.representation (ν i)).character (z : G) = 54 := by
      intro i hi
      rw [(hodd (z : G) hzodd).2.1 i hi, hχz, hδ₁]
      norm_num
    have hcol := sum_norm_sq_le_card_centralizer basis ((Finset.range (2 ^ (5 - 3))).image ν)
      (z : G)
    rw [Finset.sum_image hνinj] at hcol
    have hsum : ∑ i ∈ Finset.range (2 ^ (5 - 3)),
        ‖(basis.representation (ν i)).character (z : G)‖ ^ 2 = 11664 := by
      rw [Finset.sum_congr rfl (fun i hi => by rw [hν i hi])]
      norm_num
    rw [hsum] at hcol
    have hCz : Nat.card (Subgroup.centralizer ({(z : G)} : Set G)) ≤ 7200 := by
      rw [← hc']
      exact Subgroup.card_le_of_le (hconf (z : G) hzN hz1')
    have hCz' : (Nat.card (Subgroup.centralizer ({(z : G)} : Set G)) : ℝ) ≤ 7200 := by
      exact_mod_cast hCz
    linarith

theorem padicValNat_three_parameter_nine_orders :
    padicValNat 3 42573600 = 6 ∧ padicValNat 3 7200 = 2 ∧ padicValNat 3 100 = 0 :=
  ⟨ParameterNineNonregular.padicValNat_eq_of_eq_pow_mul (a := 58400) Nat.prime_three
      (by norm_num) (by norm_num),
    ParameterNineNonregular.padicValNat_eq_of_eq_pow_mul (a := 800) Nat.prime_three
      (by norm_num) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)⟩

theorem stationary_all_prime_parameter_nine_with_nontrivial_odd_core_is_regular_of_confinement
    (hconfine : StationaryConfinementStatement) (hfixed : StationaryFixedFactorStatement)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hN : N t ≠ ⊥) :
    let s₀ : G := fS (s n)
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Na := (N t).map (C t).subtype
    let c := Nat.card (C t)
    let d := Nat.card ↥(C t ⊓ Subgroup.centralizer ({s₀} : Set G))
    N t ≤ Subgroup.center (C t) ∧ IsCyclic Na ∧ Nat.card Na = 5 ∧
      (∀ x ∈ Na, s₀ * x * s₀⁻¹ = x⁻¹ → x = 1) ∧ E = ⊥ ∧ n = 5 ∧
      c = 7200 ∧ d = 100 ∧ Nat.card G = 42573600 ∧ (C t).index = 5913 ∧
      padicValNat 3 (Nat.card G) = 6 ∧
      (padicValNat 3 (Nat.card G) : ℤ) = 3 * padicValNat 3 c - 2 * padicValNat 3 d := by
  intro s₀ T₀ Y H₀ J E Na c d
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨-, hUtriv, hEbot, hNaA, hNacyc, hNacard, -, -, ha9, -, -, -, -, hcenter, -, -, -⟩ :=
    stationary_all_prime_seven_nine_odd_core_is_cyclic_and_central_of_confinement hconfine
      hfixed hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf (Or.inr hq)
      hmodel hcov
  have hNa1 : Nat.card Na ≠ 1 := by
    intro h1
    apply hN
    have hbot : Na = ⊥ := Subgroup.card_eq_one.mp h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective).mp hbot
  have hN5 : Nat.card Na = 5 := by
    rcases ha9 hq with h | h
    · exact absurd (hNacard.trans h) hNa1
    · exact hNacard.trans h
  have hNs : Na ≤ Subgroup.centralizer ({s₀} : Set G) := by
    intro x hx
    have hx' : x ∈ (N t).map (C t).subtype ⊓ Subgroup.centralizer ({(fS (s n) : G)} : Set G) := by
      rw [← hNaA]
      exact hx
    exact hx'.2
  have hq5 : 5 < p ^ f := by omega
  obtain ⟨-, hconf, -, -⟩ := hconfine G hGnonab hrecognition n hn S fS t (fS (s n)) ht2 hs2 hsC
    (Ne.symm hst) hnonab hcentral hnc p f hp hpodd hf hq5 hmodel hcov
  obtain ⟨hn5, hc, hd, hGc, hI⟩ := parameter_nine_regular_of_central_core hGnonab n hn S fS t ht
    hnonab hcentral hnc p f hp hpodd hf hq hmodel hcenter hN5 hNs hconf
  obtain ⟨hv₁, hv₂, hv₃⟩ := padicValNat_three_parameter_nine_orders
  refine ⟨hcenter, hNacyc, hN5, hUtriv, hEbot, hn5, hc, hd, hGc, hI, by rw [hGc, hv₁], ?_⟩
  change (padicValNat 3 (Nat.card G) : ℤ) = 3 * padicValNat 3 (Nat.card (C t)) -
    2 * padicValNat 3 (Nat.card ↥(C t ⊓ Subgroup.centralizer ({s₀} : Set G)))
  rw [hGc, hc, hd, hv₁, hv₂, hv₃]
  norm_num

end CFSG.Semidihedral.StationarySevenNine
