module

public import CFSG.CharacterTheory.Semidihedral.Principal.SectionConstancy
public import CFSG.CharacterTheory.Semidihedral.Principal.FourGroupCosetDegreeBound

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes
open CosetConstantEigenspaces

theorem principal_character_coset_constant_of_normal {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    {u : G} {e : ℕ} (hu : orderOf u ∣ p ^ e) (N : Subgroup G)
    (hNC : N ≤ Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hNnormal : ∀ g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G), ∀ n ∈ N,
      g * n * g⁻¹ ∈ N)
    (hNcop : Nat.Coprime p (Nat.card N)) {y : G} (hy : y ∈ N) :
    (basis.representation χ).character (u * y) = (basis.representation χ).character u := by
  classical
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers u : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  let N' : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G)) :=
    N.subgroupOf (Subgroup.centralizer (Subgroup.zpowers u : Set G))
  have : N'.Normal := ⟨fun n hn g => hNnormal g g.2 n hn⟩
  have hN'card : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
  let R := localizedComplexIntegerRing ideal
  have := localizedComplexIntegerRing_residue_charP ideal p
  have hunit : IsUnit ((Nat.card N' : ℤ) : R) := by
    rw [localizedComplexInteger_integer_unit_iff ideal p]
    intro hdvd
    have hdvd' : p ∣ Nat.card N' := Int.natCast_dvd_natCast.mp hdvd
    rw [hN'card] at hdvd'
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hNcop hdvd'
  have hcardUnit : ((hunit.unit : Rˣ) : R) = Nat.card N' := by
    rw [IsUnit.unit_spec, Int.cast_natCast]
  have hadm := normalSubgroupCharacterSupport_admissible localBasis R N' hunit.unit hcardUnit
  have hsub := coefficientBlock_subset_admissible localBasis R _ hadm localPrincipal
    (normalSubgroupCharacterSupport_principal_mem localBasis N' localPrincipal hlocalPrincipal)
  let y' : Subgroup.centralizer (Subgroup.zpowers u : Set G) := ⟨y, hNC hy⟩
  have hy'N : y' ∈ N' := hy
  have hyreg : Nat.Coprime p (orderOf y') := by
    have hdvd : orderOf y' ∣ Nat.card N' := by
      have := orderOf_dvd_natCard (⟨y', hy'N⟩ : N')
      rwa [Subgroup.orderOf_mk] at this
    rw [hN'card] at hdvd
    exact Nat.Coprime.coprime_dvd_right hdvd hNcop
  have hproj := principal_character_section_projection basis ideal p principal hprincipal hu
    localBasis localPrincipal hlocalPrincipal hχ y' hyreg
  have h1 := principal_character_section_projection basis ideal p principal hprincipal hu
    localBasis localPrincipal hlocalPrincipal hχ 1
    (by rw [orderOf_one]; exact Nat.coprime_one_right p)
  rw [Subgroup.coe_one, mul_one] at h1
  change (basis.representation χ).character (u * (y' : G)) = _
  rw [hproj, h1]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  congr 1
  have hθN := hsub hθ
  simp only [normalSubgroupCharacterSupport, Finset.mem_filter, Finset.mem_univ,
    true_and] at hθN
  have hyker : (localBasis.representation θ).representation y' = 1 := hθN ⟨y', hy'N⟩
  rw [one_mul, FiniteComplexRepresentation.character, Representation.character,
    Representation.character, map_mul, hyker, one_mul]

theorem central_odd_prime_principal_eigenspace_degree_bound {G W : Type*} [Group G] [Fintype G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (ρ : Representation ℂ G W) (hρ : ρ.character = (basis.representation χ).character)
    {t : G} (ht : orderOf t = 2) (A : Subgroup G)
    (hAZ : ∀ a ∈ A, a ∈ Subgroup.centralizer {t} ∧ ∀ c ∈ Subgroup.centralizer {t}, a * c = c * a)
    {r : ℕ} (hr : r.Prime) (hrodd : Odd r) (hAcard : Nat.card A = r)
    (Q : Subgroup G) (hQC : Q ≤ Subgroup.centralizer {t}) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q)
    (hQt : ∀ u ∈ Q, u ≠ 1 → t ∈ Subgroup.zpowers u)
    (hrat : ∀ a ∈ A, ∃ q : ℚ, (basis.representation χ).character a = q)
    (hker : ∃ a ∈ A, (basis.representation χ).character a ≠ (basis.representation χ).character 1) :
    (∀ z ∈ A, z ≠ 1 → ∀ μ : ℂ, μ ^ r = 1 → μ ≠ 1 →
      ∃ m : ℕ, 0 < m ∧ Module.finrank ℂ (Module.End.eigenspace (ρ z) μ) = Nat.card Q * m) ∧
    (∀ z ∈ A, z ≠ 1 → ‖ρ.character t‖ ≤ Module.finrank ℂ (Module.End.eigenspace (ρ z) 1)) ∧
    ((Nat.card Q * (r - 1) : ℕ) : ℝ) + ‖ρ.character t‖ ≤ Module.finrank ℂ W := by
  have := Fact.mk Nat.prime_two
  have hAcent : ∀ a ∈ A, ∀ c ∈ Subgroup.centralizer {t}, a * c = c * a :=
    fun a ha => (hAZ a ha).2
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hQA : ∀ q ∈ Q, ∀ a ∈ A, q * a = a * q := fun q hq a ha => (hAcent a ha q (hQC hq)).symm
  have hconst : ∀ u ∈ Q, u ≠ 1 → ∀ a ∈ A, ρ.character (u * a) = ρ.character u := by
    intro u hu hu1 a ha
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
      A ?_ ?_ ?_ ha
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left (hQA u hu b hb) i)).eq
    · intro g hg n hn
      have hgn : g * n = n * g := (hAcent n hn g (hCu g hg)).symm
      rw [hgn, mul_inv_cancel_right]
      exact hn
    · rw [hAcard, Nat.coprime_two_left]
      exact hrodd
  have hker' : ¬ A ≤ MonoidHom.ker ρ := by
    intro hle
    obtain ⟨a, ha, hne⟩ := hker
    apply hne
    rw [← hρ]
    have h1 : ρ a = 1 := MonoidHom.mem_ker.mp (hle ha)
    change LinearMap.trace ℂ W (ρ a) = LinearMap.trace ℂ W (ρ 1)
    rw [h1, map_one ρ]
  have hrat' : ∀ a ∈ A, ∃ q : ℚ, ρ.character a = q := fun a ha => by
    rw [hρ]
    exact hrat a ha
  obtain ⟨h1, h2, h3⟩ := cyclic_prime_coset_constant_eigenspaces ρ Q A hQA hr hAcard hrat' hker'
    hconst
  exact ⟨h1, fun z hz hz1 => h2 z hz hz1 t htQ ht1, h3 t htQ ht1⟩

end CFSG.Semidihedral.Principal
