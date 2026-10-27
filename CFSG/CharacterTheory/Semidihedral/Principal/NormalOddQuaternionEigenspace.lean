module

public import CFSG.CharacterTheory.Semidihedral.Principal.CentralOddEigenspaceBound

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes
open CosetConstantEigenspaces

theorem normal_odd_prime_principal_quaternion_eigenspace_bound {G W : Type*} [Group G]
    [Fintype G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (ρ : Representation ℂ G W) (hρ : ρ.character = (basis.representation χ).character)
    {t : G} (ht : orderOf t = 2) (P : Subgroup G)
    (hPnormal : P ≤ Subgroup.centralizer {t} ∧
      ∀ c ∈ Subgroup.centralizer {t}, ∀ x ∈ P, c * x * c⁻¹ ∈ P)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (hPcard : Nat.card P = ℓ)
    (Q : Subgroup G) (hQ : Q ≤ Subgroup.centralizer {t} ∧ Q ≤ Subgroup.centralizer P)
    (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q) (hQt : ∀ u ∈ Q, u ≠ 1 → t ∈ Subgroup.zpowers u)
    (hrat : ∀ x ∈ P, ∃ q : ℚ, (basis.representation χ).character x = q)
    (hker : ∃ x ∈ P, (basis.representation χ).character x ≠ (basis.representation χ).character 1) :
    ((Nat.card Q * (ℓ - 1) : ℕ) : ℝ) + ‖ρ.character t‖ ≤ Module.finrank ℂ W ∧
    (∀ z ∈ P, z ≠ 1 → ∀ μ : ℂ, μ ^ ℓ = 1 → μ ≠ 1 →
      ∃ m : ℕ, 0 < m ∧ Module.finrank ℂ (Module.End.eigenspace (ρ z) μ) = Nat.card Q * m) := by
  have := Fact.mk Nat.prime_two
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hQP : ∀ q ∈ Q, ∀ x ∈ P, q * x = x * q :=
    fun q hq x hx => (Subgroup.mem_centralizer_iff.mp (hQ.2 hq) x hx).symm
  have hconst : ∀ u ∈ Q, u ≠ 1 → ∀ x ∈ P, ρ.character (u * x) = ρ.character u := by
    intro u hu hu1 x hx
    rw [hρ]
    obtain ⟨k, hk⟩ := hQ2 ⟨u, hu⟩
    have hu2 : orderOf u ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have htu := hQt u hu hu1
    have hCu : ∀ g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G),
        g ∈ Subgroup.centralizer {t} := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hg t htu).symm
    refine principal_character_coset_constant_of_normal basis ideal 2 principal hprincipal hχ hu2
      P ?_ ?_ ?_ hx
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left (hQP u hu b hb) i)).eq
    · intro g hg n hn
      exact hPnormal.2 g (hCu g hg) n hn
    · rw [hPcard, Nat.coprime_two_left]
      exact hℓodd
  have hker' : ¬ P ≤ MonoidHom.ker ρ := by
    intro hle
    obtain ⟨x, hx, hne⟩ := hker
    apply hne
    rw [← hρ]
    have h1 : ρ x = 1 := MonoidHom.mem_ker.mp (hle hx)
    change LinearMap.trace ℂ W (ρ x) = LinearMap.trace ℂ W (ρ 1)
    rw [h1, map_one ρ]
  have hrat' : ∀ x ∈ P, ∃ q : ℚ, ρ.character x = q := fun x hx => by
    rw [hρ]
    exact hrat x hx
  obtain ⟨h1, -, h3⟩ := cyclic_prime_coset_constant_eigenspaces ρ Q P hQP hℓ hPcard hrat' hker'
    hconst
  exact ⟨h3 t htQ ht1, h1⟩

end CFSG.Semidihedral.Principal
