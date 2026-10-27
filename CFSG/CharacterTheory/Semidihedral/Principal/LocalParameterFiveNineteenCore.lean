module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveNineteenCoreSupport
public import CFSG.CharacterTheory.Semidihedral.Local.PerfectFullLocalFusion

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem simple_local_parameter_five_nineteen_order_has_trivial_odd_core
    {G : Type} [Group G]
    [Fintype G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    let a₀ := Nat.card CN
    let b₀ := CN.index
    Nat.card G = 68400 * a₀ * b₀ ^ 3 →
      N t = ⊥ ∧ Nat.card (C t) = 240 ∧ Nat.card G = 68400 := by
  intro CN a₀ b₀ hGcard
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
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
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc 5 1
      (by norm_num) (by decide) le_rfl hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal
  have hq5 : Nat.card F = 5 := by rw [hcard, pow_one]
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).property _
  have hVS : (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) ≤
      (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s n)).property)
  have htV : t ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    norm_num at ht2
  have hfus : ∀ v ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G),
      v ≠ 1 → ∃ g ∈ Subgroup.normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G),
        g * v * g⁻¹ = t := fun v hv hv1 =>
    CFSG.Semidihedral.Local.klein_four_normalizer_conj_transitive n hn S fS _ hVS
      (supplied_four_group_isKleinFour hn fS ht) hv htV hv1 ht1
  obtain ⟨hN, hC⟩ := local_parameter_five_nineteen_trivial_core_of_family hGnonab n hn S fS t ht
    hnonab hcentral hnc hmodel basis ideal principal hprincipal localBasis localPrincipal
    (Nat.card F) hq5 _ rfl _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg (hOF S fS hcent) hfus hGcard
  have hab : a₀ * b₀ = 1 := by
    change Nat.card CN * CN.index = 1
    rw [Subgroup.card_mul_index, hN, Subgroup.card_bot]
  obtain ⟨ha, hb⟩ := mul_eq_one.mp hab
  refine ⟨hN, ?_, ?_⟩
  · rw [hC]
    change 240 * a₀ * b₀ = 240
    rw [ha, hb]
    norm_num
  · rw [hGcard, ha, hb]
    norm_num

end CFSG.Semidihedral.Principal
