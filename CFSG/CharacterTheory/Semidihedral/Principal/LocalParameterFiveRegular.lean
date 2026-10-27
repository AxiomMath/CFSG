module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveTrivialCore
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveSeventeen
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveNineteenCore

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem simple_local_parameter_five_is_regular_with_exact_order
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
    n = 4 ∧ Nat.card (C t) = 240 * a₀ * b₀ ∧
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * a₀ ∧
      Nat.card G = 126000 * a₀ * b₀ ^ 3 ∧ (C t).index = 525 * b₀ ^ 2 ∧
      padicValNat 5 (Nat.card G) = 3 + padicValNat 5 a₀ + 3 * padicValNat 5 b₀ ∧
      (padicValNat 5 (Nat.card G) : ℤ) = 3 * (padicValNat 5 (Nat.card (C t)) : ℤ) -
        2 * (padicValNat 5 (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) : ℤ) := by
  intro CN a₀ b₀
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
  obtain ⟨hn4, hCt, hDt, hrows⟩ := local_parameter_five_rows_of_family n hn S fS t ht hnonab
    hcentral hnc hmodel basis ideal principal hprincipal localBasis localPrincipal (Nat.card F)
    hq5 _ rfl _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg (hOF S fS hcent)
  have h17 := (simple_local_parameter_five_excludes_seventeen_order_alternative hGnonab n hn S fS
    t ht hnonab hcentral hnc hmodel).2
  have h19 := simple_local_parameter_five_nineteen_order_has_trivial_odd_core hGnonab n hn S fS t
    ht hnonab hcentral hnc hmodel
  have hex := simple_local_parameter_five_trivial_core_excludes_nineteen_order hGnonab n hn S fS
    t ht hnonab hcentral hnc hmodel
  rcases hrows with ⟨-, -, -, -, -, -, hX⟩ | ⟨-, -, -, -, -, -, hX⟩ | ⟨-, -, -, -, -, -, hX⟩
  · exfalso
    obtain ⟨hN, -, hG68400⟩ := h19 (congrArg Prod.fst hX)
    exact hex hN hG68400
  rotate_left
  · exact (h17 (congrArg Prod.fst hX)).elim
  have hGc : Nat.card G = 126000 * a₀ * b₀ ^ 3 := congrArg Prod.fst hX
  have hCi : (C t).index = 525 * b₀ ^ 2 := congrArg Prod.snd hX
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hv126 : padicValNat 5 126000 = 3 := by
    rw [show (126000 : ℕ) = 5 ^ 3 * 1008 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hv240 : padicValNat 5 240 = 1 := by
    rw [show (240 : ℕ) = 5 ^ 1 * 48 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hv12 : padicValNat 5 12 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have hvG : padicValNat 5 (Nat.card G) = 3 + padicValNat 5 a₀ + 3 * padicValNat 5 b₀ := by
    rw [hGc, padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul (by norm_num) ha.ne', padicValNat.pow, hv126]
  have hvC : padicValNat 5 (Nat.card (C t)) = 1 + padicValNat 5 a₀ + padicValNat 5 b₀ := by
    rw [hCt, padicValNat.mul (by positivity) hb.ne', padicValNat.mul (by norm_num) ha.ne', hv240]
  have hvD : padicValNat 5 (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) =
      padicValNat 5 a₀ := by
    rw [hDt, padicValNat.mul (by norm_num) ha.ne', hv12, zero_add]
  refine ⟨hn4, hCt, hDt, hGc, hCi, hvG, ?_⟩
  rw [hvG, hvC, hvD]
  push_cast
  ring

end CFSG.Semidihedral.Principal
