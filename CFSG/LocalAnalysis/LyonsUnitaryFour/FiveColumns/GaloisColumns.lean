module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.GlobalFiveColumns

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes

variable {G : Type} [Group G] [Fintype G]

theorem global_value_mul_pow_mod_five (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {z : G} (hz2 : z ^ 2 = 1)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers z : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (quotientBasis : FiniteIrreducibleCharacterBasis L)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (hker : ¬ 2 ∣ Nat.card π.ker)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G))) (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (l : ℕ) :
    (basis.representation χ).character (z * (y : G) ^ l) =
      (basis.representation χ).character (z * (y : G) ^ (l % 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z ∣ 2 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hz2
  set f : Subgroup.centralizer (Subgroup.zpowers z : Set G) → ℂ :=
    fun m => (basis.representation χ).character m.val with hf
  have hproj : ∀ j : ℕ, (basis.representation χ).character (z * (y : G) ^ j) =
      ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        characterPairing f (localBasis.representation θ).character *
          (localBasis.representation θ).character (centralizerSelf z * y ^ j) := by
    intro j
    have hord : orderOf (((y ^ j)⁻¹ : Subgroup.centralizer (Subgroup.zpowers z : Set G)) : G) ∣
        orderOf (y : G) := by
      rw [Subgroup.coe_inv, orderOf_inv, Subgroup.coe_pow]
      exact orderOf_pow_dvd (x := (y : G)) j
    have hregular : Nat.Coprime 2
        (orderOf (((y ^ j)⁻¹ : Subgroup.centralizer (Subgroup.zpowers z : Set G)) : G)) :=
      Nat.Coprime.coprime_dvd_right hord hyodd
    have hloc := principal_local_section_projection_character basis ideal 2 principal hprincipal
      z 1 hzord localBasis localPrincipal hlocalPrincipal (y ^ j)⁻¹ hregular χ
    have hpoint : ((⟨z, element_mem_centralizer_zpowers z⟩ :
        Subgroup.centralizer (Subgroup.zpowers z : Set G)) * (y ^ j)⁻¹)⁻¹ =
        centralizerSelf z * y ^ j := by
      have hself : (centralizerSelf z)⁻¹ = centralizerSelf z := by
        apply Subtype.ext
        change z⁻¹ = z
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, hz2])
      change (centralizerSelf z * (y ^ j)⁻¹)⁻¹ = _
      rw [mul_inv_rev, inv_inv, hself]
      exact ((centralizerSelf_commute z (y ^ j)).eq).symm
    rw [hpoint, characterSubsetProjection_character basis _ χ hχ,
      characterSubsetProjection_apply'] at hloc
    rw [show z * (y : G) ^ j = ((centralizerSelf z * y ^ j :
        Subgroup.centralizer (Subgroup.zpowers z : Set G)) : G) by
      rw [Subgroup.coe_mul, Subgroup.coe_pow]; rfl, ← hloc]
  rw [hproj, hproj, local_principal_block_eq localBasis ideal localPrincipal hlocalPrincipal hL
    quotientBasis π hπ hker, sum_normalSubgroupCharacterSupport_eq localBasis quotientBasis π hπ
    (fun ψ => characterPairing f ψ * ψ (centralizerSelf z * y ^ l)),
    sum_normalSubgroupCharacterSupport_eq localBasis quotientBasis π hπ
    (fun ψ => characterPairing f ψ * ψ (centralizerSelf z * y ^ (l % 5)))]
  refine Finset.sum_congr rfl fun θ _ => ?_
  simp only [Function.comp_apply, map_mul, map_pow, hy]
  rw [hL.pow_mod_five l]

theorem global_fiveFourier_galois (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {z : G} (hz2 : z ^ 2 = 1)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers z : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (quotientBasis : FiniteIrreducibleCharacterBasis L)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (hker : ¬ 2 ∣ Nat.card π.ker)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G))) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (τ : Equiv.Perm basis.index) (k : ℕ) (hkodd : k % 2 = 1) (hk5 : k % 5 = 2)
    (hτ : ∀ a g, (basis.representation (τ a)).character g = (basis.representation a).character
      (g ^ k)) (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (i : ℕ) :
    fiveFourier (basis.representation (τ χ)).character ζ z (y : G) i =
      fiveFourier (basis.representation χ).character ζ z (y : G) (3 * i) := by
  have hzy : Commute z (y : G) := by
    have := congrArg Subtype.val (centralizerSelf_commute z y).eq
    exact this
  have hzk : z ^ k = z := by
    rw [← Nat.mod_add_div k 2, hkodd, pow_add, pow_mul, hz2, one_pow, mul_one, pow_one]
  have hval : ∀ j : ℕ, (basis.representation (τ χ)).character (z * (y : G) ^ j) =
      (basis.representation χ).character (z * (y : G) ^ ((2 * j) % 5)) := by
    intro j
    rw [hτ, (hzy.pow_right j).mul_pow, hzk, ← pow_mul,
      global_value_mul_pow_mod_five basis ideal principal hprincipal hz2 localBasis localPrincipal
        hlocalPrincipal hL quotientBasis π hπ hker y hy hyodd χ hχ (j * k)]
    congr 3
    rw [Nat.mul_mod, hk5, mul_comm 2 j, Nat.mul_mod j 2]
  unfold fiveFourier
  congr 1
  rw [Finset.sum_congr rfl fun j _ => by rw [hval j]]
  have hperm : ∀ F : ℕ → ℂ,
      ∑ j ∈ Finset.range 5, F ((2 * j) % 5) = ∑ l ∈ Finset.range 5, F l := by
    intro F
    simp [Finset.sum_range_succ]
    ring
  have hζ5 : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 5) := by
    intro m
    conv_lhs => rw [← Nat.mod_add_div m 5, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hexp : ∀ j : ℕ, j < 5 → ζ ^ (4 * i * j) = ζ ^ (4 * (3 * i) * ((2 * j) % 5)) := by
    intro j hj
    rw [hζ5 (4 * i * j), hζ5 (4 * (3 * i) * ((2 * j) % 5))]
    congr 1
    have : (4 * (3 * i) * ((2 * j) % 5)) % 5 = (4 * i * j) % 5 := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      have h2 : 4 * (3 * i) * (2 * j) = 4 * i * j + 5 * (4 * i * j) := by ring
      rw [h2, Nat.add_mul_mod_self_left]
    exact this.symm
  rw [Finset.sum_congr rfl fun j hj => by rw [hexp j (Finset.mem_range.mp hj)]]
  exact hperm (fun l =>
    ζ ^ (4 * (3 * i) * l) * (basis.representation χ).character (z * (y : G) ^ l))

end CFSG.LyonsUnitaryFour
