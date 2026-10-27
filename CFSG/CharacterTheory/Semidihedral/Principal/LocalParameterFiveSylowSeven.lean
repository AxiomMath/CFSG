module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveSylowSevenSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOddCore

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  LocalParameterFiveSylowSeven

theorem simple_local_parameter_five_seven_centralizer_normalizer_congruence
    {G : Type}
    [Group G] [Fintype G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ)
    (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
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
    7 ^ (Nat.card G).factorization 7 = 7 ∧ ¬ 7 ∣ Nat.card (C t) ∧
    (∀ P : Sylow 7 G, ∃ A : Subgroup G, Odd (Nat.card A) ∧ (Nat.card A = 1 ∨ Nat.card A = 3) ∧
      (P : Subgroup G) ⊔ A = Subgroup.centralizer (P : Set G) ∧ (P : Subgroup G) ⊓ A = ⊥ ∧
      (∀ x ∈ (P : Subgroup G), ∀ y ∈ A, x * y = y * x) ∧
      (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 3 ∧
      a₀ * b₀ ^ 3 ≡ Nat.card A [MOD 7] ∧
      ∀ basis : FiniteIrreducibleCharacterBasis G,
        (∃ χ ψ : basis.index,
          Function.Injective (basis.representation χ).representation ∧
          Function.Injective (basis.representation ψ).representation ∧
          (∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) ∧
          (∀ g, ∃ q : ℚ, (basis.representation ψ).character g = q) ∧
          (basis.representation χ).character 1 = 21 ∧ (basis.representation ψ).character 1 = 20 ∧
          (basis.representation χ).character t = 5 ∧
          ∀ x : G, Odd (orderOf x) →
            (basis.representation ψ).character x = (basis.representation χ).character x - 1) ∧
        ∀ χ ψ : basis.index,
          Function.Injective (basis.representation χ).representation →
          Function.Injective (basis.representation ψ).representation →
          (∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) →
          (∀ g, ∃ q : ℚ, (basis.representation ψ).character g = q) →
          (basis.representation χ).character 1 = 21 → (basis.representation ψ).character 1 = 20 →
          (basis.representation χ).character t = 5 →
          (∀ x : G, Odd (orderOf x) →
            (basis.representation ψ).character x = (basis.representation χ).character x - 1) →
          ∀ V : FiniteComplexRepresentation.{0, 0} G,
            V.character = (basis.representation ψ).character →
            let ρA : Representation ℂ A V.vector := V.representation.comp A.subtype
            let E₀ : Submodule ℂ V.vector :=
              ⨅ u : (P : Subgroup G), Module.End.eigenspace (V.representation u) 1
            ∃ hE₀ : ∀ y : A, E₀ ≤ E₀.comap (ρA y),
              (ρA.subrepresentation E₀ hE₀).character 1 = 2 ∧
              Function.Injective (ρA.subrepresentation E₀ hE₀) ∧
              (∀ y : A, ∃ q : ℚ, (ρA.subrepresentation E₀ hE₀).character y = q) ∧
              (∀ y : A, (basis.representation ψ).character y =
                7 * (ρA.subrepresentation E₀ hE₀).character y + 6) ∧
              ∀ lam : (P : Subgroup G) →* ℂˣ, lam ≠ 1 →
                let E : Submodule ℂ V.vector := ⨅ u : (P : Subgroup G),
                  Module.End.eigenspace (V.representation u) (lam u : ℂ)
                ∃ hE : ∀ y : A, E ≤ E.comap (ρA y),
                  ∀ y : A, (ρA.subrepresentation E hE).character y =
                    (ρA.subrepresentation E₀ hE₀).character y + 1) ∧
    ∀ g : G, orderOf g ≠ 35 := by
  intro CN a₀ b₀
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ht2, -, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨hN13, -⟩ := simple_local_parameter_five_odd_core_has_order_one_or_three hGnonab n hn S
    fS t ht hnonab hcentral hnc hmodel
  obtain ⟨-, hCcard, -, hGcard, -, -, -⟩ := simple_local_parameter_five_is_regular_with_exact_order
    hGnonab n hn S fS t ht hnonab hcentral hnc hmodel
  have hCcard : Nat.card (C t) = 240 * a₀ * b₀ := hCcard
  have hGcard : Nat.card G = 126000 * a₀ * b₀ ^ 3 := hGcard
  have hab : a₀ * b₀ = Nat.card (N t) := Subgroup.card_mul_index CN
  have hab13 : (a₀ = 1 ∧ b₀ = 1) ∨ (a₀ = 1 ∧ b₀ = 3) ∨ (a₀ = 3 ∧ b₀ = 1) := by
    rcases hN13 with hN1 | ⟨-, hN3⟩
    · rw [hN1, Subgroup.card_bot] at hab
      exact Or.inl ⟨Nat.eq_one_of_mul_eq_one_right hab, Nat.eq_one_of_mul_eq_one_left hab⟩
    · rw [hN3] at hab
      have ha : a₀ ∣ 3 := ⟨b₀, hab.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp ha with h1 | h3
      · rw [h1, one_mul] at hab
        exact Or.inr (Or.inl ⟨h1, hab⟩)
      · rw [h3] at hab
        exact Or.inr (Or.inr ⟨h3, by omega⟩)
  have hG7 : (Nat.card G).factorization 7 = 1 := by
    have h7 : 7 ∣ Nat.card G := by
      rw [hGcard]
      rcases hab13 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> norm_num
    have h49 : ¬ 7 ^ 2 ∣ Nat.card G := by
      rw [hGcard]
      rcases hab13 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> norm_num
    have h1 := (Nat.prime_seven.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
      (by rw [pow_one]; exact h7)
    have h2 : ¬ 2 ≤ (Nat.card G).factorization 7 := fun h =>
      h49 ((Nat.prime_seven.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr h)
    omega
  have hC7 : ¬ 7 ∣ Nat.card (C t) := by
    rw [hCcard]
    rcases hab13 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> norm_num
  have hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t := by
    obtain ⟨-, -, h⟩ := CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn
      S fS
    have hz : (((fS (r n)) ^ 2 ^ (n - 2) : S) : G) = t := by rw [ht, Subgroup.coe_pow]
    intro x
    rw [← hz]
    exact h Group.IsPerfect.commutator_eq_top x
  have hP7 : ∀ P : Sylow 7 G, Nat.card (P : Subgroup G) = 7 := fun P => by
    rw [P.card_eq_multiplicity, hG7, pow_one]
  obtain ⟨⟨ideal₇, hmax₇, h7mem⟩, hchar₇⟩ := CFSG.BlockBasics.residue_prime_existence 7
    Nat.prime_seven
  have : ideal₇.IsMaximal := hmax₇
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₇) 7 := hchar₇ ideal₇ hmax₇ h7mem
  have hvan : ∀ (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index),
      (basis.representation χ).character 1 = 21 →
      ∀ g : G, 7 ∣ orderOf g → (basis.representation χ).character g = 0 := by
    intro basis χ hχ1 g hg
    have hχdeg : Module.finrank ℂ (basis.representation χ).vector = 21 := by
      have h := (basis_character_one basis χ).1
      rw [hχ1] at h
      exact_mod_cast h.symm
    exact (full_prime_part_character_degree_singleton_block_singular_vanishing basis ideal₇ 7 χ
      (by rw [hG7, pow_one, hχdeg]; norm_num)).2 g hg
  have hEIG : ∀ (P : Sylow 7 G) (A : Subgroup G), A ≤ Subgroup.centralizer (P : Set G) →
      Nat.Coprime 7 (Nat.card A) → Odd (Nat.card A) →
      ∀ (basis : FiniteIrreducibleCharacterBasis G) (χ ψ : basis.index),
        Function.Injective (basis.representation ψ).representation →
        (∀ g, ∃ q : ℚ, (basis.representation ψ).character g = q) →
        (basis.representation χ).character 1 = 21 → (basis.representation ψ).character 1 = 20 →
        (∀ x : G, Odd (orderOf x) →
          (basis.representation ψ).character x = (basis.representation χ).character x - 1) →
        ∀ V : FiniteComplexRepresentation.{0, 0} G,
          V.character = (basis.representation ψ).character →
          let ρA : Representation ℂ A V.vector := V.representation.comp A.subtype
          let E₀ : Submodule ℂ V.vector :=
            ⨅ u : (P : Subgroup G), Module.End.eigenspace (V.representation u) 1
          ∃ hE₀ : ∀ y : A, E₀ ≤ E₀.comap (ρA y),
            (ρA.subrepresentation E₀ hE₀).character 1 = 2 ∧
            Function.Injective (ρA.subrepresentation E₀ hE₀) ∧
            (∀ y : A, ∃ q : ℚ, (ρA.subrepresentation E₀ hE₀).character y = q) ∧
            (∀ y : A, (basis.representation ψ).character y =
              7 * (ρA.subrepresentation E₀ hE₀).character y + 6) ∧
            ∀ lam : (P : Subgroup G) →* ℂˣ, lam ≠ 1 →
              let E : Submodule ℂ V.vector := ⨅ u : (P : Subgroup G),
                Module.End.eigenspace (V.representation u) (lam u : ℂ)
              ∃ hE : ∀ y : A, E ≤ E.comap (ρA y),
                ∀ y : A, (ρA.subrepresentation E hE).character y =
                  (ρA.subrepresentation E₀ hE₀).character y + 1 := by
    intro P A hAC hAcop hAodd basis χ ψ hψf hψr hχ1 hψ1 hψχ V hV ρA E₀
    have hcomm : ∀ y : A, ∀ u ∈ (P : Subgroup G), (y : G) * u = u * y := fun y u hu =>
      (Subgroup.mem_centralizer_iff.mp (hAC y.2) u hu).symm
    have hval : ∀ y : A, ∀ u ∈ (P : Subgroup G), u ≠ 1 →
        V.representation.character ((y : G) * u) = -1 := by
      intro y u hu hu1
      have huo : orderOf u = 7 := by
        have hdvd : orderOf u ∣ 7 := hP7 P ▸ Subgroup.orderOf_dvd_natCard _ hu
        rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hu1
        · exact h
      have hyo : orderOf (y : G) ∣ Nat.card A := Subgroup.orderOf_dvd_natCard _ y.2
      have hcop : Nat.Coprime (orderOf (y : G)) (orderOf u) := by
        rw [huo]
        exact Nat.Coprime.coprime_dvd_left hyo hAcop.symm
      have hord : orderOf ((y : G) * u) = orderOf (y : G) * 7 := by
        rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (hcomm y u hu) hcop, huo]
      have h7 : 7 ∣ orderOf ((y : G) * u) := hord ▸ dvd_mul_left 7 _
      have hodd : Odd (orderOf ((y : G) * u)) := by
        rw [hord]
        exact (Odd.of_dvd_nat hAodd hyo).mul (by decide)
      have h := hψχ _ hodd
      rw [hvan basis χ hχ1 _ h7, zero_sub] at h
      change V.character _ = _
      rw [hV, h]
    have hnorm : ∀ y : A, (y : G) ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
      intro y
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        rw [hcomm y u hu, mul_inv_cancel_right]
        exact hu
      · intro hu
        have h := hcomm y ((y : G) * u * (y : G)⁻¹) hu
        have heq : (y : G) * u * (y : G)⁻¹ = u := by
          have h' : (y : G) * ((y : G) * u * (y : G)⁻¹) = (y : G) * u := by
            rw [h, inv_mul_cancel_right]
          exact mul_left_cancel h'
        rw [← heq]
        exact hu
    have hE₀ : ∀ y : A, E₀ ≤ E₀.comap (ρA y) := fun y v hv =>
      mapsTo_fixed_of_mem_normalizer V.representation (P : Subgroup G) (hnorm y) v hv
    have hγ : ∀ y : A, (ρA.subrepresentation E₀ hE₀).character y =
        (7 : ℂ)⁻¹ * (V.character y - 6) := by
      intro y
      have h := trace_restrict_fixed_of_constant V.representation (P : Subgroup G) (hnorm y) (-1)
        (hval y)
      rw [hP7 P] at h
      change LinearMap.trace ℂ ↥E₀ ((V.representation y).restrict (hE₀ y)) = _
      rw [h]
      push_cast
      ring
    have hV1 : V.character 1 = 20 := by rw [hV, hψ1]
    refine ⟨hE₀, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hγ 1]
      rw [Subgroup.coe_one, hV1]
      norm_num
    ·
      have hker : ∀ y : A, ρA.subrepresentation E₀ hE₀ y = 1 → y = 1 := by
        intro y hy1
        have hval1 : ∀ h ∈ Subgroup.zpowers (y : G),
            (basis.representation ψ).representation.character h =
              (basis.representation ψ).representation.character 1 := by
          intro h hh
          obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hh
          have hk1 : (ρA.subrepresentation E₀ hE₀).character (y ^ k) =
              (ρA.subrepresentation E₀ hE₀).character 1 := by
            simp only [Representation.character, map_pow, hy1, one_pow, map_one]
          rw [hγ, hγ] at hk1
          have hk2 : V.character ((y ^ k : A) : G) = V.character ((1 : A) : G) := by
            have h7 : (7 : ℂ)⁻¹ ≠ 0 := by norm_num
            have := mul_left_cancel₀ h7 hk1
            linear_combination this
          rw [Subgroup.coe_pow, Subgroup.coe_one, hV] at hk2
          exact hk2
        have hle := CFSG.LyonsUnitaryFour.le_ker_of_character_eq_degree
          (basis.representation ψ).representation (Subgroup.zpowers (y : G)) hval1
        have hy1' : (basis.representation ψ).representation (y : G) = 1 :=
          hle (Subgroup.mem_zpowers _)
        exact Subtype.ext (hψf (hy1'.trans (map_one _).symm))
      intro a b hab
      have h1 : ρA.subrepresentation E₀ hE₀ (a * b⁻¹) = 1 := by
        rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
      exact mul_inv_eq_one.mp (hker _ h1)
    · intro y
      obtain ⟨q, hq⟩ := hψr y
      refine ⟨(q - 6) / 7, ?_⟩
      rw [hγ y]
      rw [hV, hq]
      push_cast
      ring
    · intro y
      rw [hγ y]
      rw [hV]
      ring
    · intro lam hlam E
      have hE : ∀ y : A, E ≤ E.comap (ρA y) := fun y v hv =>
        QuaternionSixteen.mapsTo_isotypic V.representation (P : Subgroup G) lam (hcomm y) v hv
      refine ⟨hE, fun y => ?_⟩
      have h := trace_restrict_isotypic_of_singular V.representation (P : Subgroup G) lam
        (hcomm y) (hval y)
      rw [hP7 P, ite_eq_right hlam] at h
      rw [hγ y]
      change LinearMap.trace ℂ ↥E ((V.representation y).restrict (hE y)) = _
      rw [h]
      change _ = (7 : ℂ)⁻¹ * (V.representation.character (y : G) - 6) + 1
      push_cast
      ring
  obtain ⟨⟨ideal₂, hmax₂, h2mem⟩, hchar₂⟩ := CFSG.BlockBasics.residue_prime_existence 2
    Nat.prime_two
  have : ideal₂.IsMaximal := hmax₂
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2 := hchar₂ ideal₂ hmax₂ h2mem
  have hpair : ∀ basis : FiniteIrreducibleCharacterBasis G, ∃ χ ψ : basis.index,
      Function.Injective (basis.representation χ).representation ∧
      Function.Injective (basis.representation ψ).representation ∧
      (∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) ∧
      (∀ g, ∃ q : ℚ, (basis.representation ψ).character g = q) ∧
      (basis.representation χ).character 1 = 21 ∧ (basis.representation ψ).character 1 = 20 ∧
      (basis.representation χ).character t = 5 ∧
      ∀ x : G, Odd (orderOf x) →
        (basis.representation ψ).character x = (basis.representation χ).character x - 1 := by
    intro basis
    obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
      (principalFiniteComplexRepresentation G)
      (principalFiniteComplexRepresentation_isIrreducible G)
    rw [principalFiniteComplexRepresentation_character] at hprincipal
    obtain ⟨χ, ψ, -, -, -, -, -, hχf, hψf, hχr, hψr, hχ1, hψ1, hχt, -, -, hψχ, -⟩ :=
      simple_local_parameter_five_faithful_rational_centralizer_degree_eight hGnonab n hn S fS t
        ht hnonab hcentral hnc hmodel basis principal hprincipal ideal₂
    exact ⟨χ, ψ, hχf, hψf, hχr, hψr, hχ1, hψ1, hχt, hψχ⟩
  obtain ⟨basis₀⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨χ₀, ψ₀, -, hψ₀f, -, hψ₀r, hχ₀1, hψ₀1, hχ₀t, hψ₀χ₀⟩ := hpair basis₀
  have hPmain : ∀ P : Sylow 7 G, ∃ A : Subgroup G,
      Nat.card (Subgroup.centralizer (P : Set G)) = 7 * Nat.card A ∧
      Odd (Nat.card A) ∧ (Nat.card A = 1 ∨ Nat.card A = 3) ∧
      (P : Subgroup G) ⊔ A = Subgroup.centralizer (P : Set G) ∧ (P : Subgroup G) ⊓ A = ⊥ ∧
      (∀ x ∈ (P : Subgroup G), ∀ y ∈ A, x * y = y * x) ∧
      (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 3 ∧
      a₀ * b₀ ^ 3 ≡ Nat.card A [MOD 7] ∧ A ≤ Subgroup.centralizer (P : Set G) ∧
      Nat.Coprime 7 (Nat.card A) := by
    intro P
    have hPcard := hP7 P
    have : IsCyclic (P : Subgroup G) := isCyclic_of_prime_card hPcard
    have hPC : (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G) :=
      CyclicInversion.sylow_le_centralizer P
    have hCodd : Odd (Nat.card (Subgroup.centralizer (P : Set G))) := by
      rw [Nat.odd_iff]
      by_contra h2
      have h2' : 2 ∣ Nat.card (Subgroup.centralizer (P : Set G)) := by omega
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2'
      have hv' : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hv
      obtain ⟨c, hc⟩ := isConj_iff.mp ((hinvol _).mp hv')
      apply hC7
      have hle : (P : Subgroup G).map (MulAut.conj c).toMonoidHom ≤ C t := by
        rintro _ ⟨u, hu, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
        have huv : u * (v : G) = (v : G) * u := Subgroup.mem_centralizer_iff.mp v.2 u hu
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc c * u * c⁻¹ * (c * (v : G) * c⁻¹) = c * (u * (v : G)) * c⁻¹ := by group
          _ = c * ((v : G) * u) * c⁻¹ := by rw [huv]
          _ = c * (v : G) * c⁻¹ * (c * u * c⁻¹) := by group
      have hcard : Nat.card ((P : Subgroup G).map (MulAut.conj c).toMonoidHom) = 7 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hPcard]
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    obtain ⟨Nc, hNc, hcop, hpq⟩ := CyclicInversion.exists_centralizer_normal_complement P
    have hPcard' : Nat.card (P : Subgroup G) = 7 ^ 1 := by rw [pow_one]; exact hPcard
    have hcomp := CyclicInversion.isComplement'_complement P Nc 1 hPcard' hcop hpq
    obtain ⟨A, hAdef⟩ : ∃ A : Subgroup G, A = Nc.map (Subgroup.centralizer (P : Set G)).subtype :=
      ⟨_, rfl⟩
    have hAC : A ≤ Subgroup.centralizer (P : Set G) := hAdef ▸ Subgroup.map_subtype_le _
    have hsupA : (P : Subgroup G) ⊔ A = Subgroup.centralizer (P : Set G) := by
      rw [hAdef]
      exact CyclicInversion.sup_map_complement P Nc hcomp
    have hinfA : (P : Subgroup G) ⊓ A = ⊥ := by
      rw [hAdef]
      exact CyclicInversion.inf_map_complement P Nc 1 hPcard' hcop hpq
    have hAcard : Nat.card A = Nat.card Nc := by
      rw [hAdef]
      exact CyclicInversion.card_map_complement P Nc
    have hCcard7 : Nat.card (Subgroup.centralizer (P : Set G)) = 7 * Nat.card A := by
      have h := CyclicInversion.card_mul_card_complement P Nc 1 hPcard' hcop hpq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, hPcard] at h
      rw [hAcard]
      exact h.symm
    have hAcop : Nat.Coprime 7 (Nat.card A) := hAcard ▸ hcop
    have hAodd : Odd (Nat.card A) := Odd.of_dvd_nat hCodd (Subgroup.card_dvd_of_le hAC)
    have hPA : ∀ x ∈ (P : Subgroup G), ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (hAC hy) x hx
    obtain ⟨hE₀, hγ1, hγinj, hγrat, -, -⟩ := hEIG P A hAC hAcop hAodd basis₀ χ₀ ψ₀ hψ₀f hψ₀r hχ₀1
      hψ₀1 hψ₀χ₀ (basis₀.representation ψ₀) rfl
    have hA13 : Nat.card A = 1 ∨ Nat.card A = 3 := by
      apply eq_one_or_three_of_factorization_le Nat.card_pos.ne' hAodd
      intro p hp
      have h := CFSG.LyonsUnitaryFour.factorization_le_of_faithful_rational_character
        (⟨_, Representation.subrepresentation
          ((basis₀.representation ψ₀).representation.comp A.subtype) _ hE₀⟩ :
          FiniteComplexRepresentation.{0, 0} A) hγinj hγrat hp
      have hfin : Module.finrank ℂ ↥(⨅ u : (P : Subgroup G),
          Module.End.eigenspace ((basis₀.representation ψ₀).representation u) 1) = 2 := by
        have h1 : (Representation.subrepresentation
            ((basis₀.representation ψ₀).representation.comp A.subtype) _
            hE₀).character 1 = (Module.finrank ℂ ↥(⨅ u : (P : Subgroup G),
              Module.End.eigenspace ((basis₀.representation ψ₀).representation u) 1) : ℂ) := by
          rw [Representation.character, map_one, LinearMap.trace_one]
        rw [hγ1] at h1
        exact_mod_cast h1.symm
      exact hfin ▸ h
    have hCN : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.centralizer_le_normalizer _
    obtain ⟨e, he⟩ : ∃ e, e =
        (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) :=
      ⟨_, rfl⟩
    have hNcard : e * Nat.card (Subgroup.centralizer (P : Set G)) =
        Nat.card (Subgroup.normalizer (P : Set G)) := by
      have h := Subgroup.relIndex_mul_card (Subgroup.centralizer (P : Set G))
        (Subgroup.normalizer (P : Set G))
      rwa [inf_eq_left.mpr hCN, ← he] at h
    have he6 : e ∣ 6 := by
      have h := relIndex_centralizer_normalizer_dvd_totient (P : Subgroup G)
      rw [hPcard, Nat.totient_prime Nat.prime_seven] at h
      rw [he]
      exact h
    have he1 : e ≠ 1 := by
      intro h1
      rw [he] at h1
      exact not_normalizer_le_centralizer hGnonab P hPcard (Subgroup.relIndex_eq_one.mp h1)
    have he2 : ¬ 2 ∣ e := by
      intro h2
      have h2N : 2 ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
        rw [← hNcard]
        exact Dvd.dvd.mul_right h2 _
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2N
      have hv' : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hv
      have hvC : (v : G) ∉ Subgroup.centralizer (P : Set G) := by
        intro hvC
        have h := Subgroup.orderOf_dvd_natCard _ hvC
        rw [hv'] at h
        rw [Nat.odd_iff] at hCodd
        omega
      have hv2 : (v : G) ^ 2 = 1 := by rw [← hv']; exact pow_orderOf_eq_one _
      have hinv := conj_eq_inv_of_involution_mem_normalizer Nat.prime_seven (P : Subgroup G)
        hPcard v.2 hv2 hvC
      set ρ := (basis₀.representation χ₀).representation with hρ
      have hρ1 : ρ.character 1 = 21 := hχ₀1
      have hord7 : ∀ u ∈ (P : Subgroup G), u ≠ 1 → orderOf u = 7 := by
        intro u hu hu1
        have hdvd : orderOf u ∣ 7 := hPcard ▸ Subgroup.orderOf_dvd_natCard _ hu
        rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hu1
        · exact h
      have hval0 : ∀ u ∈ (P : Subgroup G), u ≠ 1 → ρ.character (1 * u) = 0 := by
        intro u hu hu1
        rw [one_mul]
        exact hvan basis₀ χ₀ hχ₀1 u (by rw [hord7 u hu hu1])
      have hinvo : ∀ x : G, orderOf x = 2 → ρ.character x = 5 := by
        intro x hx
        obtain ⟨c, hc⟩ := isConj_iff.mp ((hinvol x).mp hx)
        have h := Representation.char_conj ρ x c
        rw [hc] at h
        rw [← h]
        exact hχ₀t
      have hvinv : (v : G)⁻¹ = (v : G) := by
        rw [inv_eq_iff_mul_eq_one, ← sq, hv2]
      have hvalv : ∀ u ∈ (P : Subgroup G), u ≠ 1 → ρ.character ((v : G) * u) = 5 := by
        intro u hu hu1
        apply hinvo
        have hvu : (v : G) * u * (v : G)⁻¹ = u⁻¹ := hinv u hu
        have hsq : ((v : G) * u) ^ 2 = 1 := by
          have h1 : (v : G) * u * (v : G) = u⁻¹ := by
            calc (v : G) * u * (v : G) = (v : G) * u * (v : G)⁻¹ := by rw [hvinv]
              _ = u⁻¹ := hvu
          rw [sq, ← mul_assoc, h1, inv_mul_cancel]
        have hne : (v : G) * u ≠ 1 := by
          intro h
          apply hvC
          rw [eq_inv_of_mul_eq_one_left h]
          exact hPC (Subgroup.inv_mem _ hu)
        exact orderOf_eq_prime hsq hne
      have hv5 : ρ.character (v : G) = 5 := hinvo _ hv'
      have hdim := trace_restrict_fixed_of_constant ρ (P : Subgroup G) (Subgroup.one_mem _) 0 hval0
      have htr := trace_restrict_fixed_of_constant ρ (P : Subgroup G) v.2 5 hvalv
      rw [hPcard, hρ1] at hdim
      rw [hPcard, hv5] at htr
      have hid : (ρ 1).restrict (mapsTo_fixed_of_mem_normalizer ρ (P : Subgroup G)
          (Subgroup.one_mem _)) = 1 := by
        ext x
        simp
      rw [hid, LinearMap.trace_one] at hdim
      have hTT : (ρ v).restrict (mapsTo_fixed_of_mem_normalizer ρ (P : Subgroup G) v.2) *
          (ρ v).restrict (mapsTo_fixed_of_mem_normalizer ρ (P : Subgroup G) v.2) = 1 := by
        ext x
        change ρ v (ρ v x) = x
        rw [← Module.End.mul_apply, ← map_mul, ← sq, hv2, map_one, Module.End.one_apply]
      obtain ⟨k, hk, hk2⟩ := finrank_add_trace_of_mul_self_eq_one _ hTT
      rw [htr, hdim] at hk2
      have hk4 : (k : ℂ) = 4 := by
        linear_combination (-1 / 2 : ℂ) * hk2
      have hk4' : k = 4 := by exact_mod_cast hk4
      have hfin : (Module.finrank ℂ ↥(⨅ u : (P : Subgroup G), Module.End.eigenspace (ρ u) 1) :
          ℂ) = 3 := by
        rw [hdim]
        norm_num
      have hfin' : Module.finrank ℂ ↥(⨅ u : (P : Subgroup G),
          Module.End.eigenspace (ρ u) 1) = 3 := by exact_mod_cast hfin
      omega
    have he3 : e = 3 := by
      have hle : e ≤ 6 := Nat.le_of_dvd (by norm_num) he6
      interval_cases e <;> omega
    have hNcard' : Nat.card (Subgroup.normalizer (P : Set G)) = 3 * (7 * Nat.card A) := by
      rw [← hNcard, he3, hCcard7]
    have hGidx := Subgroup.card_mul_index (Subgroup.normalizer (P : Set G))
    have hmod := card_sylow_modEq_one 7 G
    rw [Sylow.card_eq_index_normalizer P] at hmod
    have hcong : a₀ * b₀ ^ 3 ≡ Nat.card A [MOD 7] := by
      obtain ⟨x, hx⟩ : ∃ x, x = a₀ * b₀ ^ 3 := ⟨_, rfl⟩
      have hGx : Nat.card G = 126000 * x := by rw [hGcard, hx, mul_assoc]
      rw [← hx]
      unfold Nat.ModEq at hmod ⊢
      rw [hNcard', hGx] at hGidx
      rcases hA13 with h1 | h3
      · rw [h1] at hGidx ⊢
        omega
      · rw [h3] at hGidx ⊢
        omega
    exact ⟨A, hCcard7, hAodd, hA13, hsupA, hinfA, hPA, by rw [← he]; exact he3, hcong, hAC,
      hAcop⟩
  refine ⟨by rw [hG7, pow_one], hC7, fun P => ?_, fun g hg => ?_⟩
  · obtain ⟨A, -, hAodd, hA13, hsupA, hinfA, hPA, he3, hcong, hAC, hAcop⟩ := hPmain P
    refine ⟨A, hAodd, hA13, hsupA, hinfA, hPA, he3, hcong, fun basis => ⟨hpair basis, ?_⟩⟩
    intro χ ψ _hχf hψf _hχr hψr hχ1 hψ1 _hχt hψχ V hV
    exact hEIG P A hAC hAcop hAodd basis χ ψ hψf hψr hχ1 hψ1 hψχ V hV
  ·
    have h5 : orderOf (g ^ 7) = 5 := by
      rw [orderOf_pow' g (by norm_num), hg]
      norm_num
    have h7 : orderOf (g ^ 5) = 7 := by
      rw [orderOf_pow' g (by norm_num), hg]
      norm_num
    have hcard : Nat.card (Subgroup.zpowers (g ^ 5)) = 7 ^ (Nat.card G).factorization 7 := by
      rw [Nat.card_zpowers, h7, hG7, pow_one]
    obtain ⟨A, hCA, -, hA13, -⟩ := hPmain (Sylow.ofCard _ hcard)
    have hmem : g ^ 7 ∈ Subgroup.centralizer ((Sylow.ofCard _ hcard : Sylow 7 G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ Subgroup.zpowers (g ^ 5) := hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
      exact ((Commute.pow_pow_self g 5 7).zpow_left k).eq
    have h5dvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [h5, hCA] at h5dvd
    rcases hA13 with h1 | h3
    · rw [h1] at h5dvd
      norm_num at h5dvd
    · rw [h3] at h5dvd
      norm_num at h5dvd

end CFSG.Semidihedral.Principal
