module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchCore
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchCharacter
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchLocalData
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveCentralSplitting

public section

open scoped Classical

namespace CFSG.Semidihedral.ParameterFive

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
  CFSG.TwoRankLowerBound.Helpers

theorem dvd_two_fifty_of_dvd {d : ℕ} (h : d ∣ 1000) (h4 : ¬ 4 ∣ d) : d ∣ 250 := by
  have h1 : d ∣ Nat.gcd d 8 * 125 := Nat.dvd_gcd_mul_iff_dvd_mul.mpr (by norm_num; exact h)
  have h2 : Nat.gcd d 8 ∣ 2 := by
    have hg : Nat.gcd d 8 ∣ 8 := Nat.gcd_dvd_right d 8
    have hgd : Nat.gcd d 8 ∣ d := Nat.gcd_dvd_left d 8
    generalize Nat.gcd d 8 = g at hg hgd ⊢
    have hle : g ≤ 8 := Nat.le_of_dvd (by norm_num) hg
    interval_cases g <;> omega
  exact h1.trans (Nat.mul_dvd_mul_right h2 125)

theorem dvd_thousand_of_mul_dvd {d : ℕ} (h : d * 126 ∣ 126000) : d ∣ 1000 :=
  Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 126) (by rwa [show (1000 : ℕ) * 126 = 126000 by
    norm_num])

theorem order_identity_five : (126000 : ℕ) = 2 * (5 ^ 1) ^ 3 * (5 ^ 1 - 1) * ((5 ^ 1) ^ 3 + 1) := by
  norm_num

theorem factorization_five_126000 : (126000 : ℕ).factorization 5 = 3 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.factorization_def _ Nat.prime_five,
    show (126000 : ℕ) = 5 ^ 3 * 1008 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem basis_character_mem_blocksIrr {X : Type} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (l : basis.index) :
    (basis.representation l).character ∈ CFSG.BlocksIrr X :=
  ⟨(basis.representation l).vector, inferInstance, inferInstance, inferInstance,
    (basis.representation l).representation, basis.irreducible l, rfl⟩

theorem character_data_at_five
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (hG126 : Nat.card G = 126000) :
    ∃ χ : G → ℂ, χ ∈ CFSG.BlocksIrr G ∧ χ 1 = ((125 : ℕ) : ℂ) ∧
      ∀ u : G, u ≠ 1 → (∃ k : ℕ, orderOf u = 5 ^ k) →
        Nat.card (Subgroup.centralizer {u}) * 126 ∣ Nat.card G := by
  have : Fintype G := Fintype.ofFinite G
  have : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := Principal.supplied_t_s_facts hn fS ht
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
    Principal.actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral
      hnc 5 1 (by norm_num) (by decide) le_rfl hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal
  have hq5 : Nat.card F = 5 := by rw [hcard, pow_one]
  obtain ⟨hn4, -, -, hrows⟩ := Principal.local_parameter_five_rows_of_family n hn S fS t ht hnonab
    hcentral hnc hmodel basis ideal principal hprincipal localBasis localPrincipal (Nat.card F)
    hq5 _ rfl _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg (hOF S fS hcent)
  obtain ⟨-, -, -, hGreg, -, -, -⟩ :=
    Principal.simple_local_parameter_five_is_regular_with_exact_order hGnonab n hn S fS t ht
      hnonab hcentral hnc hmodel
  set a₀ := Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
    (N t)) with ha₀
  set b₀ := (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
    (N t)).index with hb₀
  have hab : 0 < a₀ * b₀ ^ 3 := by
    have ha : 0 < a₀ := Nat.card_pos
    have hb : 0 < b₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    positivity
  have hGreg' : Nat.card G = 126000 * a₀ * b₀ ^ 3 := hGreg
  have hrow : δ₁ = 1 ∧ Module.finrank ℂ (basis.representation χ₁).vector = 125 := by
    rcases hrows with ⟨-, -, -, -, -, -, hX⟩ | ⟨h1, -, -, hf1, -, -, -⟩ | ⟨-, -, -, -, -, -, hX⟩
    · have h := congrArg Prod.fst hX
      change Nat.card G = 68400 * a₀ * b₀ ^ 3 at h
      rw [hGreg'] at h
      nlinarith
    · exact ⟨h1, hf1⟩
    · have h := congrArg Prod.fst hX
      change Nat.card G = 85680 * a₀ * b₀ ^ 3 at h
      rw [hGreg'] at h
      nlinarith
  obtain ⟨hδ₁, hf₁⟩ := hrow
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ideal5, hmax5, hmem5⟩ := (CFSG.BlockBasics.residue_prime_existence 5 Nat.prime_five).1
  have : ideal5.IsMaximal := hmax5
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal5) 5 :=
    (CFSG.BlockBasics.residue_prime_existence 5 Nat.prime_five).2 ideal5 hmax5 hmem5
  have hdeg5 : 5 ^ (Nat.card G).factorization 5 ∣
      Module.finrank ℂ (basis.representation χ₁).vector := by
    rw [hG126, factorization_five_126000, hf₁]
    norm_num
  have hvanish := (Principal.full_prime_part_character_degree_singleton_block_singular_vanishing
    basis ideal5 5 χ₁ hdeg5).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hodd⟩ := hfam
  have h0 : 0 ∈ Finset.range (2 ^ (n - 3)) := by
    rw [Finset.mem_range]
    positivity
  have hν : ∀ x : G, Odd (orderOf x) → (basis.representation (ν 0)).character x =
      (basis.representation χ₁).character x + 1 := by
    intro x hx
    rw [(hodd x hx).2.1 0 h0, hδ₁]
    push_cast
    ring
  have hχ1 : (basis.representation χ₁).character 1 = ((125 : ℕ) : ℂ) := by
    rw [show (basis.representation χ₁).character 1 =
      (Module.finrank ℂ (basis.representation χ₁).vector : ℂ) from Representation.char_one _, hf₁]
  have hν1 : (basis.representation (ν 0)).character 1 = ((126 : ℕ) : ℂ) := by
    rw [hν 1 (by rw [orderOf_one]; exact odd_one), hχ1]
    push_cast
    ring
  refine ⟨_, basis_character_mem_blocksIrr basis χ₁, hχ1, fun u hu1 hup => ?_⟩
  obtain ⟨k, hk⟩ := hup
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hu1 hk
  have h5u : 5 ∣ orderOf u := by
    rw [hk]
    exact dvd_pow_self 5 hk0
  have huodd : Odd (orderOf u) := by
    rw [hk]
    exact Odd.pow (by decide)
  have hνu : (basis.representation (ν 0)).character u = 1 := by
    rw [hν u huodd, hvanish u h5u, zero_add]
  exact UnitaryBranch.card_centralizer_mul_dvd_of_character_eq_one
    (basis_character_mem_blocksIrr basis (ν 0)) hν1 hνu

theorem layer_preimage_index_eq_two_at_five {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1) :
    (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2 := by
  have : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, -⟩ := Principal.supplied_t_s_facts hn fS ht
  have hLJ := Principal.generalizedFitting_eq_J_of_field_group_trivial n hn S fS hG t ht2 hnonab
    hcentral hnc 5 1 (by norm_num) (by decide) le_rfl hmodel (fun a _ ha => Nat.dvd_one.mp ha)
  obtain ⟨-, hJindex, -, -, -, -, -⟩ := actual_quotient_inputs n hn S fS hG t ht2
  rw [Subgroup.comap_comap, barKappa_comp_nu, hLJ,
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hJindex]

theorem statedClassicalModel_psu_of_card_oddCore_eq_one
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (hN : Nat.card (N t) = 1) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 5 1 := by
  have : Fintype G := Fintype.ofFinite G
  have : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨hzt, ht2, -⟩ := Principal.supplied_t_s_facts hn fS ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hG126, -⟩ :=
    Principal.simple_local_parameter_five_central_odd_core_and_actual_centralizer_splitting
      hGnonab n hn S fS t ht hnonab hcentral hnc hmodel
  have hG126000 : Nat.card G = 126000 := by rw [hG126, hN]
  have hNbot : N t = ⊥ := Subgroup.eq_bot_of_card_eq _ hN
  have hNcent : N t ≤ Subgroup.center (C t) := by rw [hNbot]; exact bot_le
  have hNcyc : IsCyclic (N t) := by rw [hNbot]; infer_instance
  have hNcop : Nat.Coprime (Nat.card (N t)) (5 * (5 ^ 1 - 1)) := by
    rw [hN]
    exact Nat.coprime_one_left _
  obtain ⟨F, _, _, κ, hD⟩ := UnitaryBranch.exists_unitaryLocalData hGnonab n hn S fS t ht hnonab
    hcentral hnc 5 1 Nat.prime_five (by decide) le_rfl (by decide) hmodel
    (layer_preimage_index_eq_two_at_five hGnonab n hn S fS t ht hnonab hcentral hnc hmodel)
    hNcent hNcyc hNcop
  obtain ⟨hKcard, -⟩ := UnitaryBranch.unitaryLocalData_card hD
  rw [hN, mul_one] at hKcard
  obtain ⟨htK, hKcent, hKp, hKconf'⟩ := UnitaryBranch.unitaryK_properties hD
  have hKconf := hKconf' (fun u hu hu1 => by
    rw [hNbot, Subgroup.map_bot, Subgroup.mem_bot] at hu
    exact absurd hu hu1)
  obtain ⟨hSN, hNS⟩ := UnitaryBranch.sylow_le_and_normalizer_le_centralizer n hn S fS ht
  obtain ⟨Q₀, H, hQ₀card, hQ₀comm, hQ₀N, hQ₀syl, -, -, hHQ₀, hHcyc, hKH, hHcard⟩ :=
    UnitaryBranch.exists_unitary_local_subgroups hD n hn S fS ht
  have hinv : ∀ y : G, orderOf y = 2 → IsConj y t := fun y hy => by
    have h := InvolutionFusion.ambient_involution_isConj_z n hn S fS hG y hy
    rwa [hzt] at h
  obtain ⟨χ, hχ, hχdeg, hχcent⟩ :=
    character_data_at_five hGnonab n hn S fS t ht hnonab hcentral hnc hmodel hG126000
  have hcent : ∀ u : G, u ≠ 1 → (∃ k : ℕ, orderOf u = 5 ^ k) →
      Nat.card (Subgroup.centralizer {u}) ∣ Nat.card (UnitaryBranch.unitaryK t) * (5 ^ 1) ^ 3 := by
    intro u hu1 hup
    have h1 := hχcent u hu1 hup
    rw [hG126000] at h1
    have h1000 : Nat.card (Subgroup.centralizer {u}) ∣ 1000 := dvd_thousand_of_mul_dvd h1
    have h4 := UnitaryBranch.not_four_dvd_card_centralizer (p := 5) (f := 1) hD hinv hu1
      (by simpa using hup)
    rw [hKcard]
    exact dvd_two_fifty_of_dvd h1000 h4
  exact UnitaryBranch.statedClassicalModel_psu_of_centralizer_data hGnonab 5 1 Nat.prime_five
    (by norm_num) le_rfl t ht2 (UnitaryBranch.unitaryK t) htK hKcent hKp hKconf S hSN hNS Q₀
    hQ₀card hQ₀comm hQ₀N hQ₀syl H hHQ₀ hHcyc hKH hHcard hcent
    (by rw [hG126000, hKcard]; exact order_identity_five) hχ
    (by rw [hχdeg, show ((5 ^ 1) ^ 3 : ℕ) = 125 by norm_num])
    (by rw [hKcard, show Nat.gcd (5 ^ 1 + 1) 3 = 3 by norm_num]; norm_num)

end CFSG.Semidihedral.ParameterFive
